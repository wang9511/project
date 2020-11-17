import re
import os
import sys
import time
import joblib
import getopt
import collections

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

class RuleLearing(object):
    def __init__(self, data_dir, protocol_name, dataset, itemMeaning, global_vars=set(), max_freq_size=3, min_support=0.0,
                 min_confidence=1.0):
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.dataset = dataset
        self.global_vars = global_vars
        self.itemMeaning = itemMeaning
        self.max_freq_size = max_freq_size
        self.min_support = min_support
        self.min_confidence = min_confidence
        self.d_super_set = collections.defaultdict(set)

    def execute(self):
        L, support_data = self.apriori(self.global_vars)
        bigRuleList = self.generateRules(L, support_data)
        print('length:{}'.format(len(bigRuleList)))
        rule_tuple, rule_string_list = self.prntRules(bigRuleList)
        return rule_tuple, rule_string_list

    def symmetry_reduction(self, rule_tuple, rule_string_list, all_types):
        print('Symmetry reducing rules...')

        min_rule_tuple, min_rule_string_list = [], []
        for (pre, cond), rule_string in zip(rule_tuple, rule_string_list):
            pre_var_set = set(map(lambda x: x.split(' ')[0], pre))
            cond_var = cond.split(' ')[0]
            #print('pre_var_set:{}, cond_var:{}'.format(pre_var_set, cond_var))
            if cond_var not in pre_var_set:
                min_rule_tuple.append((pre, cond))
                min_rule_string_list.append(rule_string)
        print('Remove redundant: before : {}, after: {}'.format(len(rule_tuple), len(min_rule_tuple)))

        rule_string_set = set(min_rule_string_list)

        print('all_types:{}'.format(all_types))
        for rule_string in min_rule_string_list:
            for t in all_types:
                tmp_stmt = rule_string
                cur_t_set = set(re.findall('%s_\d' % t, rule_string))
                if len(cur_t_set) == 0:  # not contain type parameter
                    continue
                elif len(cur_t_set) == 1:
                    # 含一种type parameter, such as 'NODE_1'
                    if '%s_1' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, rule_string)
                    elif '%s_2' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_2' % t, '%s_1' % t, tmp_stmt)
                    else:
                        print('%s contains too many parameters!' % tmp_stmt)

                    
                    if tmp_stmt in rule_string_set:
                        if rule_string in rule_string_set:
                            rule_string_set.remove(rule_string)

                elif len(cur_t_set) == 2:
                    # 含2种type parameter, such as 'NODE_1' and 'NODE_2'
                    #print('tmp_stmt:{}'.format(tmp_stmt))
                    #print('cur_t_set:{}'.format(cur_t_set))
                    cur_t_dict = {}
                    for i, cur_t in enumerate(cur_t_set):
                        cur_t_dict['REP_X_%d' % i] = cur_t
                        tmp_stmt = re.sub(cur_t, 'REP_X_%d' % i, tmp_stmt)
                    for k, v in cur_t_dict.items():
                        tmp_stmt = re.sub(k, (cur_t_set - set([v])).pop(), tmp_stmt)
                    if tmp_stmt in rule_string_set:
                        if rule_string in rule_string_set:
                            rule_string_set.remove(rule_string)
                else:
                    print('Too many types of parameters!')

        sym_red_rule_string = list(rule_string_set)
        sym_red_rule_tuple = list(map(lambda x: split_string_to_tuple(x), sym_red_rule_string))
        assert len(sym_red_rule_string) == len(sym_red_rule_tuple)

        print('Reduction result: before : {}, after: {}'.format(len(min_rule_tuple), len(sym_red_rule_tuple)))
        return sym_red_rule_tuple, sym_red_rule_string

    def instantiate(self, rule_tuple, rule_string_list, all_types):
        print('Instantiating rules...')
        fout = '{}/{}/aux_invs.txt'.format(self.data_dir, self.protocol_name)
        fout1 = '{}/{}/aux_invs1.txt'.format(self.data_dir, self.protocol_name)
        ftemp = '{}/{}/data/aux_invs.json'.format(self.data_dir, self.protocol_name)

        rule_string_set = set(rule_string_list)

        #print('rule_string_list:{}'.format(rule_string_list))
        #print('all_types:{}'.format(all_types))

        try:
            for rule_string in rule_string_list:
                for t in all_types:
                    tmp_stmt = rule_string
                    cur_t_set = set(re.findall('%s\_\d' % t, rule_string))
                    #print('cur_t_set:{}'.format(cur_t_set))
                    if len(cur_t_set) == 0:  # not contain type parameter
                        continue
                    elif len(cur_t_set) == 1:  # 含一种type parameter, such as 'NODE_1'
                        if '%s_1' % t in tmp_stmt:
                            #print('tmp_stmt:{}'.format(tmp_stmt))
                            tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, rule_string)
                            #print('tmp_stmtAfter:{}'.format(tmp_stmt))
                        elif '%s_2' % t in tmp_stmt:
                            tmp_stmt = re.sub('%s_2' % t, '%s_1' % t, tmp_stmt)
                        else:
                            print('Too many parameters!')
                        if tmp_stmt not in rule_string_set:
                            rule_string_set.add(tmp_stmt)
                    elif len(cur_t_set) == 2:  # 含2种type parameter, such as 'NODE_1' and 'NODE_2'
                        cur_t_dict = {}
                        for i, cur_t in enumerate(cur_t_set):
                            #print('tmp_stmt:{}'.format(tmp_stmt))
                            cur_t_dict['REP_X_%d' % i] = cur_t
                            tmp_stmt = re.sub(cur_t, 'REP_X_%d' % i, tmp_stmt)
                            #print('cur_t_dict:{}'.format(cur_t_dict))
                        for k, v in cur_t_dict.items():
                            #print('cur_t_set:{}'.format(cur_t_set))
                            
                            #print('cur_t_set - set([v]):{}'.format(cur_t_set - set([v])))
                            tmp_stmt = re.sub(k, (cur_t_set - set([v])).pop(), tmp_stmt)
                            #print('tmp_stmtAfter:{}'.format(tmp_stmt))
                        if tmp_stmt not in rule_string_set:
                            rule_string_set.add(tmp_stmt)
                    else:
                        print('Too many types of parameters!')
        except getopt.GetoptError:
            sys.stderr.write('Cannot instantiation, skip')

        #filter rule_string_set, remove repeat rule
        #for example, p&q->r q&p->r should remain one
        rule_string_set_filtered = set()

        repeatSet = set()
        for item in rule_string_set:
            guardsFilter, actionFilter= item.split('->')[0].strip(), item.split('->')[1].strip()
            if len(guardsFilter.split('&')) == 2:
                guardFilter1, guardFilter2 = guardsFilter.split('&')[0].strip(), guardsFilter.split('&')[1].strip()
                itemUpdated = guardFilter2 + ' & ' + guardFilter1 +' -> ' + actionFilter
                if itemUpdated in rule_string_set:
                    if item not in repeatSet:
                        repeatSet.add(itemUpdated)
                else:
                    rule_string_set_filtered.add(item)
            else:
                rule_string_set_filtered.add(item)
        rule_string_set_filtered = rule_string_set_filtered | repeatSet

        sym_expan_rule_string = list(rule_string_set_filtered)
        #print('rule_string_set:{}'.format(rule_string_set))
        sym_expan_rule_tuple = list(map(lambda x: split_string_to_tuple(x), sym_expan_rule_string))
        assert len(sym_expan_rule_string) == len(sym_expan_rule_tuple)
        print('Expansion result: before : {}, after: {}'.format(len(rule_tuple), len(sym_expan_rule_tuple)))

        with open(fout, 'w') as f:
            # for cnt, stmt in enumerate(sorted(sym_expan_rule_string, key=lambda x: len(x)), 1):
            for cnt, stmt in enumerate(sym_expan_rule_string, 1):
                f.write('rule_%d: %s\n' % (cnt, stmt))
        """
        with open(fout1, 'w') as f:
            # for cnt, stmt in enumerate(sorted(sym_expan_rule_string, key=lambda x: len(x)), 1):
            for cnt, stmt in enumerate(sym_expan_rule_string, 1):
                f.write('rule_%d: %s\n' % (cnt, stmt))
        """
        joblib.dump(sym_expan_rule_tuple, ftemp)

        print(type(sym_expan_rule_tuple))
        #print('len(tuple):{}'.format(len(sym_expan_rule_tuple)))
        #print('len(string):{}'.format(len(sym_expan_rule_string)))
        return sym_expan_rule_tuple, sym_expan_rule_string

    def minimize_rule(self, rest_rule_tuple):
        print('Minimizing rules..')
        fout = '{}/{}/min_rule.txt'.format(self.data_dir, self.protocol_name)
        rest_rule_tuple = sorted(rest_rule_tuple, key=lambda x: len(x[0]))

        left, right = [], []
        for pre, cond in rest_rule_tuple:
            left.append(list(pre))
            right.append(cond)

        same_right = collections.defaultdict(list)
        for l, r in zip(left, right):
            same_right[r].append(l)

        for r, left_list in same_right.items():
            index = [x for x in range(len(left_list))]
            for i in range(len(left_list)):
                for j in range(i + 1, len(left_list)):
                    if j not in index: continue
                    if not (set(left_list[i]) - set(left_list[j])):
                        index.remove(j)
            same_right[r] = [left_list[i] for i in index]

        min_rule_string, min_rule_tuple = [], []

        for r, left_list in same_right.items():
            for l in left_list:
                # if left part doesn't contain array variable, then continue
                if not re.search('[\[\]]', ''.join(l)):
                    continue
                min_rule_tuple.append((set(l), r))
                min_rule_string.append('{} -> {}'.format(' & '.join(l), r))

        with open(fout, 'w') as f:
            for cnt, stmt in enumerate(min_rule_string, 1):
                f.write('rule_%d: %s\n' % (cnt, stmt))

        print('Before: {}, After: {}'.format(len(rest_rule_tuple), len(min_rule_tuple)))
        return min_rule_tuple, min_rule_string

    def createC1(self, dataSet):  # creat candidates frequent set with 1 element
        C1 = []
        for transaction in dataSet:
            for item in transaction:
                if [item] not in C1:
                    C1.append([item])

        C1.sort()
        return list(map(frozenset, C1))  # use frozen set so we can use it as a key in a dict

    def scanD(self, D, Ck, minSupport):
        print("len d: {}, len ck:{} ".format(len(D), len(Ck)))
        print("time complexity will be: O({})".format(len(D) * len(Ck)))

        ssCnt = {}
        for key in Ck:
            can = list(key)
            res = self.d_super_set[can[0]]
            for t in can[1:]:
                res = res & self.d_super_set[t]
            if len(res) != 0:
                ssCnt[key] = len(res)
        if len(ssCnt) < 50:
            print('ssCnt:{}'.format(ssCnt))

        numItems = float(len(D))
        retList = []
        supportData = {}
        for key in ssCnt:
            support = ssCnt[key] / numItems
            if support >= minSupport:
                retList.append(key)
            supportData[key] = support
        return retList, supportData

    def _build_trie(self, data, k):
        root = {}
        for i, row in enumerate(data):
            row = sorted(list(row))[:k - 2]
            cur = root
            for d in row:
                if d not in cur:
                    cur[d] = {}
                cur = cur[d]
            cur[i] = None
        return root

    def aprioriGen(self, Lk, k):  # creates Ck
        retList = []
        root = self._build_trie(Lk, k)
        #print('Lk:{}'.format(Lk))
        #if k==3:
        #    print('root:{}'.format(root))
        for i, row in enumerate(Lk):
            row = sorted(list(row))[:k - 2]

            cur = root
            #if k==3:
                #print('row:{},cur:{}'.format(row,cur))
            ok = True

            for d in row:
                if d not in cur:
                    ok = False
                    break
                cur = cur[d]
            if ok:
                retList.extend([Lk[i] | Lk[j] for j in cur.keys() if i < j])
        return retList

    def _build_super_set(self, data: list):
        """
        :param data: [set,set..]
        :return:
        """
        print('---build_super_set----')
        for i, d in enumerate(data):
            for x in d:
                self.d_super_set[x].add(i)
        #print('d_super_set:{}'.format(self.d_super_set))
        print('build_super_set done')

    def apriori(self, global_vars):
        print('--------------------------\nGenerating frequent set........')
        start_freq = time.time()
        #C1:[frozenset({0}), frozenset({1}), frozenset({2}), frozenset({3}), frozenset({4}), frozenset({5}), frozenset({6}), frozenset({7}), frozenset({8}), frozenset({9}), frozenset({10}), frozenset({11}), frozenset({12}), frozenset({13}), frozenset({14}), frozenset({15}), frozenset({16}), frozenset({17}), frozenset({18}), frozenset({19}), frozenset({20}), frozenset({21})]
        C1 = self.createC1(self.dataset)
        #D:[{1, 2, 4, 6, 8, 10, 11, 13, 14, 17, 19, 20}, {1, 2, 4, 6, 8, 10, 11, 13, 15, 17, 18, 20}, {0, 2, 4, 6, 8, 10, 12, 13, 15, 16, 19, 20}, {1, 3, 4, 6, 7, 10, 11, 13, 15, 17, 18, 20}, {0, 2, 4, 6, 8, 10, 12, 13, 15, 16, 19, 21}, {0, 2, 4, 6, 8, 9, 12, 13, 15, 17, 19, 20}, {0, 3, 4, 6, 7, 10, 12, 13, 15, 16, 19, 20}, {0, 2, 4, 6, 8, 9, 12, 13, 15, 17, 19, 21}, {0, 3, 4, 6, 7, 10, 12, 13, 15, 16, 19, 21}, {0, 3, 4, 6, 7, 9, 12, 13, 15, 17, 19, 20}, {1, 2, 4, 6, 8, 10, 11, 13, 14, 17, 19, 21}, {0, 3, 4, 6, 7, 9, 12, 13, 15, 17, 19, 21}, {1, 2, 5, 6, 8, 10, 11, 13, 15, 17, 18, 20}, {1, 2, 4, 6, 8, 10, 11, 13, 15, 17, 18, 21}, {1, 3, 4, 6, 7, 10, 11, 13, 15, 17, 18, 21}, {0, 2, 4, 6, 8, 10, 12, 13, 15, 16, 19, 21}, {0, 3, 4, 6, 7, 10, 12, 13, 15, 16, 19, 21}, {0, 2, 4, 6, 8, 10, 12, 13, 15, 16, 19, 20}, {0, 2, 4, 6, 8, 9, 12, 13, 15, 17, 19, 21}, {0, 3, 4, 6, 7, 10, 12, 13, 15, 16, 19, 20}, {0, 3, 4, 6, 7, 9, 12, 13, 15, 17, 19, 21}, {0, 2, 4, 6, 8, 9, 12, 13, 15, 17, 19, 20}, {0, 3, 4, 6, 7, 9, 12, 13, 15, 17, 19, 20}]
        D = list(map(set, self.dataset))  # add cast to list. In py3, map create a genarator.
        #print('C1:{}\n D:{}'.format(C1, D))
        self._build_super_set(D)

        start = time.time()
        L1, supportData = self.scanD(D, C1, self.min_support)
        print('time for scan L1: %.3f' % (time.time() - start))

        L = [L1]
        #print('L:{}'.format(L))
        k = 2
        while k <= self.max_freq_size:
            #if k==3:
                #print('L[k-2]:{}'.format(L[k-2]))
            Ck = self.aprioriGen(L[k - 2], k)
            #if k==3:
                #print('Ck:{}'.format(Ck))
            start = time.time()
            #print('ck:{}'.format(Ck))
            print('len(CK):{}'.format(len(Ck)))
            # remove those 3 global variables if minimize = True
            Ck = filter(lambda x: len(x & global_vars) < 3, Ck)  # if is_minimize else Ck
            print('CK:{}'.format(Ck))

            all_lemma_set = list(Ck)
            #if k<3:
            #    print('all_lemma_set:{}'.format(all_lemma_set))
            Lk, supK = [], {}

            for t in [self.parellel_cal(D, all_lemma_set, self.min_support)]:
                Lk.extend(t[0])
                #print('t[0]:{}'.format(len(t[0])))
                supK.update(t[1])

            print('time for scan L%d : %.3f\n-------------------\n' % (k, time.time() - start))

            supportData.update(supK)
           # if k<3:
               # print('Lk:{}'.format(Lk))
            L.append(Lk)
            k += 1
        #print('L;{}'.format(L))
        print('Running time for frequent sets: %.3f s' % (time.time() - start_freq))
        return L, supportData

    def parellel_cal(self, D, Ck, minSupport):
        Lk, supK = self.scanD(D, Ck, minSupport)  # scan DB to get Lk
        return (Lk, supK)

    def generateRules(self, L, supportData, minConf=1.0):  # supportData is a dict coming from scanD
        start = time.time()

        bigRuleList = []
        for i in range(1, len(L)):  # only get the sets with two or more items
            for freqSet in L[i]:
                H1 = [frozenset([item]) for item in freqSet]
                #print('H1:{}'.format(H1))
                if i > 1:
                    self.rulesFromConseq(freqSet, H1, supportData, bigRuleList, minConf)
                else:
                    self.calcConf(freqSet, H1, supportData, bigRuleList, minConf)

        print('Running time for calculating association rules: %.3f s ' % (time.time() - start))
        #print('bigRuleList:{}'.format(bigRuleList))
        return bigRuleList

    def calcConf(self, freqSet, H, supportData, brl, minConf=1.0):
        prunedH = []  # create new list to return

        for cond in H:
            conf = supportData[freqSet] / supportData[cond]  # calc confidence
            if conf >= minConf:
                if len(freqSet - cond) == 1:
                    brl.append((cond, freqSet - cond, conf))
                prunedH.append(cond)

        return prunedH

    def rulesFromConseq(self, freqSet, H, supportData, brl, minConf=1.0):
        m = len(H[0])
        #print('m:{},H[0]:{},H:{}'.format(m,H[0],H))
        if (len(freqSet) > (m + 1)):  # try further merging
            Hmp1 = self.aprioriGen(H, m + 1)  # create Hm+1 new candidates

            Hmp1 = self.calcConf(freqSet, Hmp1, supportData, brl, minConf)

            if (len(Hmp1) > 1):  # need at least two sets to merge
                self.rulesFromConseq(freqSet, Hmp1, supportData, brl, minConf)

    def prntRules(self, bigRuleList):
        # sortedRuleList = sorted(bigRuleList, key=lambda d: d[2], reverse=True)
        print('\n\nAssociation rules: {}'.format(len(bigRuleList)))

        ar_filename = '{}/{}/assoRules.txt'.format(self.data_dir, self.protocol_name)

        rule_tuple, rule_string_list = [], []

        for ruleTup in bigRuleList:
            ant, conseq = ruleTup[0], ruleTup[1]
            e_ant = set(self.itemMeaning[a] for a in ant)
            e_conseq = list(self.itemMeaning[c] for c in conseq)
            #print('e_ant:{},e_conseq:{}'.format(e_ant,e_conseq))
            rule_tuple.append((e_ant, e_conseq[0]))
            rule_string_list.append(' & '.join(e_ant) + ' -> ' + ''.join(e_conseq))

        with open(ar_filename, 'w') as fw:
            for i, rule in enumerate(sorted(rule_string_list, key=lambda x: len(x)), 1):
                fw.write('rule_%d: %s\n' % (i, rule))
        #print('rule_string_list:{}'.format(rule_string_list))
        return rule_tuple, rule_string_list

    def slct_rules_by_guards(self, rules_map, guards, par, save=True, load=False):
        if load and os.path.exists("{}/data/norm_rule_dict.pkl".format(self.name)) and os.path.exists(
                "{}/data/rules.pkl".format(self.name)):
            return joblib.load("{}/data/norm_rule_dict.pkl".format(self.name)), joblib.load(
                "{}/data/rules.pkl".format(self.name))

        par = par[0]
        if guards:
            norm_rule_dict = {key: rules for key, rules in rules_map.items() if set(key).issubset(guards)}
        else:
            norm_rule_dict = {key: rules for key, rules in rules_map.items()}

        rules = set()

        for ant_dict in norm_rule_dict.values():
            for ant, conse_set in ant_dict.items():
                for conse in conse_set:
                    line = "{} -> {}".format(' & '.join(sorted(ant)), conse)
                    search_para = re.search(r'%s\_\d' % par, line)
                    # search_para = re.search(r'\d', line)

                    cnt = 1
                    while search_para:
                        line = re.sub(search_para.group(), 'P%d' % cnt, line)
                        search_para = re.search(r'%s\_\d' % par, line)
                        # search_para = re.search(r'%s\_\d' % par, line)

                        cnt += 1

                    rules.add(line)
        print('select %d association rules' % len(rules))

        # fout = '%s/selected_by_guard.txt' % self.name
        # with open(fout, 'w') as f:
        #     for i, r in enumerate(rules, 1):
        #         f.write('rule_%d: %s\n' % (i, r))

        # save data
        # self.write_to_file(rules)

        if save:
            joblib.dump(norm_rule_dict, "{}/data/norm_rule_dict.pkl".format(self.name))
            joblib.dump(rules, "{}/data/rules.pkl".format(self.name))

        return norm_rule_dict, rules