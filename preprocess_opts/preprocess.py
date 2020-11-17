# -*- coding: utf-8 -*-
# @Author  : arabela

import os
import re
import sys
import getopt
import time
import subprocess
import collections
import pandas as pd
import multiprocessing
from shutil import copyfile
from sklearn.externals import joblib


def split_back(stmt):
    if not stmt:
        return (set(), '')
    parts = stmt.split(',')
    if len(parts) == 2:
        return (set([parts[0]]), parts[1])
    elif len(parts) == 3:
        return (set([parts[0], parts[1]]), parts[2])
    else:
        print('Wrong rule')


def split_string_to_tuple(stmt):
    if not stmt:
        return (set(), '')
    try:
        parts = stmt.split(' -> ')
    except ValueError:
        print('Error string: %s' % stmt)
    else:
        if not len(re.findall(' & ', parts[0])):
            return (set([parts[0]]), parts[1])
        else:
            return (set(parts[0].split(' & ')), parts[1])


def pre_checker(data_dir, prot_name, murphi_dir):
    # complete the path to protocol file
    prot_dir = "{0}/{1}/{1}.m".format(data_dir, prot_name)
    if not os.path.exists(prot_dir):
        print('protocol file cannot be find in {}'.format(prot_dir))
        sys.exit(1)

    abs_prot_file = "{0}/{1}/ABS_{1}.m".format(data_dir, prot_name)
    copyfile(prot_dir, abs_prot_file)

    # check murphi url
    murphi_url = locate_murphi(murphi_dir)  # '../murphi_url.txt

    return murphi_url


def locate_murphi(murphi_url_file):
    try:
        fr = open(murphi_url_file, "r")
    except IOError:
        print('Cannot find murphi url in {}'.format(murphi_url_file))
    else:
        murphi_url = fr.read().strip()
        fr.close()
        if murphi_url == '':
            sys.stderr.write('Empty murphi_url.txt, please check again.')
            sys.exit(1)
        return murphi_url


class DataProcess(object):
    def __init__(self, data_dir, name, replace_index, atom_formulas=set(), has_atom=False):
        self.data_dir = data_dir
        self.name = name
        self.replace_index = replace_index
        self.atom_formulas = self.get_atoms(atom_formulas)
        self.has_atom = os.path.exists("{}/{}/atom.txt".format(self.data_dir, self.name)) or has_atom
        print('replace_index:{}'.format(self.replace_index))

    def read_trans(self):
        dataList, stateDict = self.read_trans_dataset()
        para_digit = self.para_form(stateDict.keys())
        dataset, itemMeaning = self.state2num_trans(dataList, stateDict)
        return dataset, itemMeaning, para_digit

    def execute(self, save=True, load=True):
        file_itemMeaning = "{}/{}/data/itemMeaning.pkl".format(self.data_dir, self.name)
        file_dataset = "{}/{}/data/dataset.pkl".format(self.data_dir, self.name)
        file_para = "{}/{}/data/para_digit.pkl".format(self.data_dir, self.name)
        if load:
            if os.path.exists(file_itemMeaning) and os.path.exists(file_dataset) and os.path.exists(file_para):
                print('Read existing files')
                dataset, itemMeaning, para_digit = joblib.load(file_dataset), joblib.load(
                    file_itemMeaning), joblib.load(file_para)
                print('Reachable set: %d\nitemMeaning: \n{}\npara digit:\n{}'.format(len(dataset), itemMeaning,
                                                                                     para_digit))
                return dataset, itemMeaning, para_digit
            else:
                print('files "{}", "{}" or "{}" do not exist'.format(file_itemMeaning, file_dataset, file_para))

        dataList, stateDict = self.collect_dataset()
        #print('dataList:{}'.format(dataList))
        #print('stateDict:{}'.format(stateDict))
        dataset, itemMeaning = self.encode_dataset(dataList, stateDict)
        para_digit = self.para_form(stateDict.keys())
        print('Reachable set: %d' % len(dataset))

        if save:
            if not os.path.exists("{}/{}/data".format(self.data_dir, self.name)):
                os.mkdir("{}/{}/data".format(self.data_dir, self.name))
            joblib.dump(dataset, file_dataset)
            joblib.dump(itemMeaning, file_itemMeaning)
        print('size of dataset: {} * {}'.format(len(dataset), len(dataset[0])))
        return dataset, itemMeaning, para_digit

    def para_form(self, name_list):
        """
        the parameter the protocol uses
        with symmetry reduction: NODE_1, NODE_2, ...
        without: 1, 2, ...
        '[]' is a symbol of local variables
        :param name_list:
        :return:
        """
        for name in name_list:
            if '[' in name:
                return False if re.search(r'\w+\_\d', name) else True
            continue
        return True

    def collect_dataset(self):
        """
        From reachable set collect dataset
        :return:
        dataList:
            [
                [v1, v2, ..., vn],
                [e11, e12, ..., e1n],
                ...,
                [en1,en2, ..., enn]]
        dataDict:
            {v1: {e11,e21,..., en1}, v2: {e12,e22, ..., en2},...}
        """
        print('Reading reachable set')

        if not os.path.exists('{0}/{1}/{1}.csv'.format(self.data_dir, self.name)) or not self.is_rs_match_dataset():
            return self.txt2csv()
        else:
            return self.readcsv()

    def is_rs_match_dataset(self):
        """
        Counts the number of states in reachable set printed by Murphi and the number of lines in transferred csv.
        If these two equal, return True; else return False

        NOTE: actually csv file will add a title line with variable names, so # states in txt +1 = # lines in csv
        """
        print('call is_rs_match_dataset')
        filename = '{0}/{1}/{1}'.format(self.data_dir, self.name)
        if not os.path.exists("{}.txt".format(filename)):
            print('Cannot find reachable state set file. \nNot sure whether the reachable set matches the protocol.')
            return True

        csv_cnt = subprocess.check_output(['wc', '-l', '{}.csv'.format(filename)]).decode('utf-8')
        tail_rs = subprocess.check_output(['tail', '{}.txt'.format(filename)]).decode('utf-8')
        return int(re.findall(r'\d+', csv_cnt)[0]) == int(
            re.findall(r'State Space Explored:.*?(\d+)\sstates', tail_rs, re.S)[0]) + 1

    def readcsv(self, input_file=""):
        print('call read_csv')
        input_file = '{0}/{1}/{1}.csv'.format(self.data_dir, self.name) if not input_file else input_file
        df = pd.read_csv(input_file)
        stateDict = {}
        booleandf = set(df.select_dtypes(include=[bool]).columns.values)

        for col in df.columns:
            if col in booleandf:
                df[col] = df[col].map({True: 'true', False: 'false'})
            stateDict[col] = set(df[col])
        return [df.columns.tolist()] + df.values.tolist(), stateDict

    def read_trans_dataset(self):
        print('call trans_dataset')
        df = pd.read_csv('{}/{}/trans_dataset.csv'.format(self.data_dir, self.name))
        stateDict = {}
        booleandf = set(df.select_dtypes(include=[bool]).columns.values)

        for col in df.columns:
            if col in booleandf:
                df[col] = df[col].map({True: 'true', False: 'false'})
            stateDict[col] = set(df[col])
        return [df.columns.tolist()] + df.values.tolist(), stateDict

    def txt2csv(self):
        print('txt2csv...')
        prefix_filename = '{0}/{1}/{1}'.format(self.data_dir, self.name)
        csv_filename = prefix_filename + '.csv'
        txt_filename = prefix_filename + '.txt'
        reachset = open(txt_filename).read()

        if self.replace_index:
            for k, v in self.replace_index.items():
                print('replace %s by %s' % (k, v))
                reachset = reachset.replace(k, v)
        states = re.findall(r'State\s\d+:\n(.*?)\n\n', reachset, re.S)

        variables = [var.split(':')[0] for var in states[0].split('\n')]

        dataset = [variables]
        open(csv_filename, 'w').write("{}\n".format("".join(variables)))

        stateDict = collections.defaultdict(set)

        for state in states:
            for var in state.split('\n'):
                stateDict[var.split(":")[0]].add(var.split(":")[1])
            dataset.append([var.split(':')[1] for var in state.split('\n')])

        with open(csv_filename, 'w') as f:
            for line in dataset:
                f.write(','.join(line) + '\n')
        return dataset, stateDict

    def describe(self, dataList):
        print('---------------------')
        print('Protocol {} has {} states.'.format(self.name, len(dataList) - 1))
        print('Each state has {} variables.'.format(len(dataList[0])))
        print('---------------------\n')

    def encode_dataset(self, dataList, stateDict):
        dataset, itemMeaning = self.tonumber(dataList, stateDict, atom=self.has_atom, neg=False)

        return dataset, itemMeaning

    def tonumber(self, stateList, statesDict, trans=True, atom=False, neg=False):
        if atom:
            stateList, statesDict = self.atom_feature(statesDict, stateList)
            mappingDict, itemMeaning = self.states2num_atom(statesDict)
        elif neg:
            stateList, statesDict = self.negative(stateList, statesDict)
            mappingDict, itemMeaning = self.states2num(statesDict)
        else:
            mappingDict, itemMeaning = self.states2num(statesDict)
        states_numberful = self.mapStates(mappingDict, stateList)

        return states_numberful, itemMeaning

    def enumerateStates(self, stateslist):
        statesDict = collections.defaultdict(set)
        col = len(stateslist[0])
        row = len(stateslist)
        for c in range(col):
            for r in range(1, row):
                if (stateslist[r][c] not in statesDict[stateslist[0][c]]) and (stateslist[r][c] != 'Undefined'):
                    statesDict[stateslist[0][c]].add(stateslist[r][c])
        return statesDict

    def atom_feature(self, stateDict, stateList):
        new_statelist, new_stateDict = [], {}
        index = {title: i for i, title in enumerate(stateList[0])}
        print('\nIndex of atomic predicates:', index)

        for i, af in enumerate(self.atom_formulas):
            pre = af.split(' ')[0]
            post = af.split(' ')[-1]
            #print('i:{}'.format(i))
            #print('pre:{}'.format(pre))
            #print('post:{}'.format(post))
            if pre not in index:
                sys.stderr.write('Cannot find %s in Index' % pre)
                sys.exit()

            col = index[pre]
            cur = [af]
            print('len(staetList):{}'.format(len(stateList)))
            for row in range(1, len(stateList)):
                if post not in index:  # in stateDict[pre]:
                    cur.append(str(post == stateList[row][col]))
                    #print('post not in index')
                    #print('post:{} stateList[row][col]:{}'.format(post, stateList[row][col]))
                else:
                    if post in index:
                        col_post = index[post]
                        if stateList[row][col] != 'Undefined' and stateList[row][col_post] != 'Undefined':
                            cur.append(str(stateList[row][col_post] == stateList[row][col]))
                        else:
                            cur.append('Undefined')
                    else:
                        cur = []
                        print('???????')
                        break
            if cur:
                #print('cur:{}'.format(cur))
                new_statelist.append(cur)
                new_stateDict[af] = {x for x in cur} - {af}
                #print('new_stateDict[af]:{}'.format(new_stateDict[af]))

        t_statelist = list(list(i) for i in zip(*new_statelist))
        #print('t_stateList:{}'.format(t_statelist))
        assert len(new_statelist) == len(t_statelist[0])
        assert len(new_statelist[0]) == len(t_statelist)

        with open('{}/{}/trans_dataset.csv'.format(self.data_dir, self.name), 'w') as f:
            for state_line in t_statelist:
                f.write('{}\n'.format(','.join(state_line)))

        print("Features / Atomic predicates: % d " % len(self.atom_formulas))
        print('statelist:{}'.format(t_statelist))
        print('new_stateDict:{}'.format(new_stateDict))
        return t_statelist, new_stateDict

    def state2num_trans(self, stateList, statesDict):
        dataset = stateList
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v in ('true', 'True'):
                    itemMeaning[cnt] = key
                if v in ('false', 'False'):
                    itemMeaning[cnt] = '!' + key
                newDict[key][v] = cnt
                cnt += 1

        state_numberful = self.mapStates(newDict, dataset)

        return state_numberful, itemMeaning

    def states2num_atom(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0
        #print('statesDict:{}'.format(statesDict))
        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                lower_key = key.lower()
                if 'true' in lower_key or 'false' in lower_key:
                    if 'true' in lower_key:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('true', 'false', key)
                    else:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('false', 'true', key)
                else:
                    #print('lower_key:{}'.format(lower_key))
                    if v.lower() == 'false':
                        itemMeaning[cnt] = re.sub(r'=', '!=', key)
                    else:
                        itemMeaning[cnt] = key

                newDict[key][v] = cnt
                cnt += 1
        print('newDict:{}'.format(newDict))
        print('ItemMeaning:', itemMeaning)
        #for key, value in itemMeaning.items():
        #    print(key, value)
        #print('Total products in rs: %d ' % len(itemMeaning))
        return newDict, itemMeaning

    def states2num(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                if '!' in v:
                    itemMeaning[cnt] = key + ' != ' + v[1:]
                else:
                    itemMeaning[cnt] = key + ' = ' + v
                newDict[key][v] = cnt
                cnt += 1

        print('\nTotal products in rs: %d \n---------------------------' % len(itemMeaning))

        return newDict, itemMeaning

    def mapStates(self, mappingDict, stateList):
        print('Mapping states into numbers using all variables...')
        states_numberful = []
        #print('stateList:{}'.format(stateList))
        for r in range(1, len(stateList)):
            temp = set()
            for c in range(len(stateList[0])):
                
                if stateList[r][c] != 'Undefined':
                    #print('stateList[r][c]:{}'.format(stateList[r][c]))
                    temp.add(mappingDict[stateList[0][c]][stateList[r][c]])
            states_numberful.append(temp)
        #print('states_numberful:{}'.format(states_numberful))
        #print('successfully mapped!')
        return states_numberful

    def get_atoms(self, atom_formulas):
        if atom_formulas:
            return atom_formulas
        else:
            file_name = "{}/{}/atom.txt".format(self.data_dir, self.name)

            return set(filter(lambda x: x,
                              map(lambda x: re.sub(r'[()]', '', x.strip()), open(file_name, 'r').read().split("\n"))))

    def select_global(self, itemMeaning):
        file_global = "{}/{}/global_vars.txt".format(self.data_dir, self.name)
        try:
            print('Read existing global variables from "{}"'.format(file_global))
            if os.path.exists(file_global):
                global_vars = joblib.load(file_global)
                print('global_vars:{}'.format(global_vars))
        except:
            raise FileExistsError
        else:
            global_vars = set()
            for k, v in itemMeaning.items():
                if not re.search('[\[\]]', v):
                    global_vars.add(k)
            print('global_vars:{}'.format(global_vars))
            joblib.dump(global_vars, filename=file_global)
        return global_vars

    def negative(self, stateList, statesDict):
        for i in range(1, len(stateList)):
            n = len(stateList[i])
            for j in range(n):
                vals = statesDict[stateList[0][j]]
                if len(vals) <= 2:
                    continue
                for v in vals:
                    if i == 1:
                        stateList[0].append(stateList[0][j])
                    stateList[i].append(v if v == stateList[i][j] else '!' + v)

        statesDict2 = self.enumerateStates(stateList)
        return stateList, statesDict2


class Save_Load_Data(object):
    def __init__(self, protocol_name):
        self.L_name = protocol_name + '/backup/' + 'L_' + protocol_name + '.pkl'
        self.Support_name = protocol_name + '/backup/' + 'SupportData_' + protocol_name + '.pkl'

        if not os.path.exists(protocol_name + '/backup'):
            os.mkdir(protocol_name + '/backup')

    def load_from_plk(self):
        print("Loading L and Supportive Data ........")
        L = joblib.load(self.L_name)
        support_data = joblib.load(self.Support_name)
        print("L and Supportive Data loaded successfully!")
        return L, support_data

    def save_to_plk(self, L, support_data):
        print("Saving L and Supportive data......")
        joblib.dump(L, self.L_name)
        joblib.dump(support_data, self.Support_name)
        print("L and Supportive data saved Successfully!")
