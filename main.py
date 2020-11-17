import os
import re
import sys
import copy
import argparse
import joblib
from shutil import copyfile
from collections import OrderedDict
from murphi_analysis.call_murphi import run_murphi
from murphi_analysis.call_murphi import run_murphi_all
from preprocess_opts.preprocess import pre_checker
from preprocess_opts.preprocess import DataProcess
from association_rule_learning.learn import RuleLearing
from association_rule_learning.learn import split_string_to_tuple
from murphi_analysis.analyser import Protocol
from association_rule_learning.select_invs import SlctInv
from preprocess_opts.utils import transform
from shutil import copyfile

def to_murphi(inv_name, rule, all_types, home_flag):
    """
    translate an association rule('Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].Data = AuxData') into murphi code
    invariant "rule_1"
        forall i: NODE do forall j: NODE do
        (i != j) -> (Chan2[i].Cmd = Inv -> Cache[j].Data = AuxData)
    end end;

    :param rule: an association rule
    :param par: NODE
    :return: murphi code
    """

    cur_paras_dict = {}
    for t in all_types:
        #找NODE_1,NODE_2
        find_result = re.findall(r'{}\_\d'.format(t), rule)
        #find_result:['NODE_2', 'NODE_1']
        for result in find_result:
            cur_paras_dict.update({transform(result): t})
            #(result, transform(result)):  (NODE_2,j),  (NODE_1,i)
            #print('{},{}'.format(result, transform(result)))
            rule = re.sub(result, transform(result), rule)
    

    murphi_string = '\n\nruleset ' if cur_paras_dict else ''

    unequal_list, para_list = [], []
    for p, t in cur_paras_dict.items():
        para_list.append('{} : {} '.format(p, t))
        if home_flag:
            unequal_list.append('Home != {}'.format(p))
    murphi_string += ('; '.join(para_list) + 'do\n') if cur_paras_dict else ''

    index = 1
    cur_para_list = list(cur_paras_dict.keys())
    while index < len(cur_paras_dict):
        if cur_paras_dict[cur_para_list[index - 1]] == cur_paras_dict[cur_para_list[index]]:
            unequal_list.append("{} != {}".format(cur_para_list[index - 1], cur_para_list[index]))
        index += 1

    murphi_string += "Invariant \"{}\"\n\t".format(inv_name)
    unequal_string = '\t(' + ' & '.join(unequal_list) + ') ->\t' if unequal_list else ''
    murphi_string += unequal_string  # ('\n\t%s' % unequal_string + '\n\t->\n\t') if unequal_string else ''
    murphi_string += ("({});".format(rule))

    murphi_string += '\nendruleset;\n' if cur_paras_dict else '\n'
    return murphi_string

def removeSameRules(rule_string_list):
    result = []
    for i in rule_string_list:
        #pre是单个原子公式的,1171->1146
        if '&' not in i:
            if i not in result:
                result.append(i)
        else:   #pre是2个原子公式的,1146->892
            pre, cond = i.split('->')[0].strip(), i.split('->')[1].strip()
            pre1, pre2 = pre.split('&')[0].strip(), pre.split('&')[1].strip()
            tempI = pre2 + ' & ' + pre1 + ' -> ' +  cond
            if i in result or tempI in result:
                continue
            else:
                result.append(i)
    return result

def removeRedundancyRules(rule_string_list):
    result = []
    for i in rule_string_list:
        preTemp, condTemp = i.split('->')[0].strip(), i.split('->')[1].strip()
        if '&' not in  preTemp:
            if ('=' in preTemp and '!=' in condTemp and '!=' not in preTemp):
                preTempLeft, condTempLeft = preTemp.split('=')[0].strip(), condTemp.split('!=')[0].strip()
                if preTempLeft != condTempLeft:
                    result.append(preTemp + ' -> ' + condTemp)
            elif('!=' in preTemp and '=' in condTemp and '!=' not in condTemp):
                preTempLeft, condTempLeft = preTemp.split('!=')[0].strip(), condTemp.split('=')[0].strip()
                if preTempLeft != condTempLeft:
                    result.append(preTemp + ' -> ' + condTemp)
            elif '!=' in preTemp and '!=' in condTemp:
                #print(preTemp, condTemp)
                preTempLeft, condTempLeft = preTemp.split('!=')[0].strip(), condTemp.split('!=')[0].strip()
                if preTempLeft != condTempLeft:
                    result.append(preTemp + ' -> ' + condTemp)
            else:
                preTempLeft, condTempLeft = preTemp.split('=')[0].strip(), condTemp.split('=')[0].strip()
                if preTempLeft != condTempLeft:
                    result.append(preTemp + ' -> ' + condTemp)
        else:
            #result.append(i)
            preTemp1, preTemp2 = preTemp.split('&')[0].strip(), preTemp.split('&')[1].strip()
            if ('=' in condTemp and '!=' not in condTemp):
                condTempLeft = condTemp.split('=')[0].strip()
                if ('=' in preTemp1 and '!=' not in preTemp1 and '=' in preTemp2 and '!=' not in preTemp2):
                    preTempLeft1, preTempLeft2 = preTemp1.split('=')[0].strip(), preTemp2.split('=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
                elif ('!=' in preTemp1 and '=' in preTemp2 and '!=' not in preTemp2):
                    preTempLeft1, preTempLeft2 = preTemp1.split('!=')[0].strip(), preTemp2.split('=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
                elif ('!=' in preTemp2 and '=' in preTemp1 and '!=' not in preTemp1):
                    preTempLeft1, preTempLeft2 = preTemp1.split('=')[0].strip(), preTemp2.split('!=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
                elif ('!=' in preTemp1 and '!=' in preTemp2):
                    preTempLeft1, preTempLeft2 = preTemp1.split('!=')[0].strip(), preTemp2.split('!=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
            elif '!=' in condTemp:
                condTempLeft = condTemp.split('!=')[0].strip()
                if ('!=' in preTemp1 and '!=' in preTemp2):
                    preTempLeft1, preTempLeft2 = preTemp1.split('!=')[0].strip(), preTemp2.split('!=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
                elif ('!=' in preTemp1 and '=' in preTemp2 and '!=' not in preTemp2):
                    preTempLeft1, preTempLeft2 = preTemp1.split('!=')[0].strip(), preTemp2.split('=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
                elif ('!=' in preTemp2 and '=' in preTemp1 and '!=' not in preTemp1):
                    preTempLeft1, preTempLeft2 = preTemp1.split('=')[0].strip(), preTemp2.split('!=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
                elif ('=' in preTemp1 and '!=' not in preTemp1 and '=' in preTemp2 and '!=' not in preTemp2):
                    preTempLeft1, preTempLeft2 = preTemp1.split('=')[0].strip(), preTemp2.split('=')[0].strip()
                    if condTempLeft != preTempLeft1 and condTempLeft != preTempLeft2:
                        result.append(preTemp + ' -> ' + condTemp)
    return result

def string2tuple(rule_string_list):
    pre = []
    cond = []
    for i in rule_string_list:
        setTemp = set()
        preTemp, condTemp = i.split('->')[0].strip(), i.split('->')[1].strip()
        if '&' in preTemp:
            setTemp.add(preTemp.split('&')[0].strip())
            setTemp.add(preTemp.split('&')[1].strip())
        else:
            setTemp.add(preTemp.strip())
        pre.append(setTemp)
        cond.append(condTemp)
    rule_tuple = list(zip(pre, cond))
    return rule_tuple

def removeRepeatRules(rule_tuple_string):
    candidate_inv_string_filtered1 = []
    for i, canInvStrI in enumerate(rule_tuple_string):
        guardsI, actionI = canInvStrI.split('->')[0].strip(), canInvStrI.split('->')[1].strip()
        if len(guardsI.split('&')) == 2:
            sign = 0
            guardsI1, guardsI2 = guardsI.split('&')[0].strip(), guardsI.split('&')[1].strip()
            for j, canInvStrJ in enumerate(rule_tuple_string):
                guardsJ, actionJ = canInvStrJ.split('->')[0].strip(), canInvStrJ.split('->')[1].strip()
                if i != j and len(guardsJ.split('&')) == 1:
                    if actionI == actionJ:
                        if guardsJ == guardsI1 or guardsJ == guardsI2:
                            sign = 1
                            break
            if sign == 0:
                candidate_inv_string_filtered1.append(canInvStrI)
        else:
            candidate_inv_string_filtered1.append(canInvStrI)
    return candidate_inv_string_filtered1


def pre(data_dir, protocol_name, node_num, murphi_url):
    def return_replace_index():
        od = OrderedDict()
        od['NODE_1'] = 'Home'
        od['NODE_2'] = 'NODE_1'
        od['NODE_3'] = 'NODE_2'
        return od

    if not os.path.exists('{1}/{0}/{0}.txt'.format(protocol_name, data_dir)):
        run_murphi(data_dir, protocol_name, murphi_dir=murphi_url,
                   aux_para='-ta >{0}/{1}/{1}.txt'.format(data_dir, protocol_name))

    replace_index = None if node_num == 2 else return_replace_index()
    processor = DataProcess(data_dir, protocol_name, replace_index=replace_index)
    dataset, itemMeaning, para_digit = processor.execute(load=True)
    global_vars = processor.select_global(itemMeaning)

    return dataset, itemMeaning, global_vars


def learn(data_dir, protocol_name, dataset, itemMeaning, global_vars, kmax):
    learner = RuleLearing(data_dir, protocol_name, dataset, itemMeaning, global_vars=global_vars, max_freq_size=kmax,
                          min_support=0.0, min_confidence=1.0)
    rule_tuple, rule_string_list = learner.execute()
    assert len(rule_tuple) == len(rule_string_list)
    return rule_tuple, rule_string_list


def select(data_dir, protocol_name, abs_type, home_flag, num_core, rule_tuple, rule_string_list, prot_analyzer,
           all_types=None):
    # prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))

    if all_types is None:
        all_types = prot_analyzer.collect_atoms()

    with open('./protocols/{}/used_aux_invs.txt'.format(protocol_name), 'w') as usedAuxInvsf:
        usedAuxInvsf.truncate()

    #*********************对称变换*********************************************************************

    instantiator = RuleLearing(data_dir, protocol_name, [], {})
    instan_rule_tuple, _ = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
    #print('aux_inv = {}'.format(instan_rule_tuple))
    #len_instan_rule_tuple: 28
    #*************************************************************************************************

    #******************参数抽象、卫式加强*****************************************************************
    print('{}\nAbstract and Strengthen'.format('*' * 30))

    _, candidate_inv_string = prot_analyzer.refine_abstract(instan_rule_tuple, abs_type=abs_type,
                                                               print_usedinvs_to_file=False, boundary_K=1)

    #print('candidate_inv_string:{}'.format(candidate_inv_string))

    candidate_inv_tuple = list(map(lambda x: split_string_to_tuple(x), candidate_inv_string))
    #print('candidate_inv_tuple:{}'.format(candidate_inv_tuple))
    assert len(candidate_inv_string) == len(candidate_inv_tuple)

    print('select candidate association rules: before: {}, after: {}'.format(len(instan_rule_tuple),
                                                                             len(candidate_inv_tuple)))

    with open('{}/{}/candidate_rules.txt'.format(data_dir, protocol_name), 'w') as f:
        for cnt, stmt in enumerate(sorted(candidate_inv_string, key=lambda x: len(x)), 1):
            f.write('rule_%d: %s\n' % (cnt, stmt))

    #**************************************************************************************************

    #**********************************对称规约*********************************************************
    # minimize candidate invs, because runnign murphi costs lots of time
    minimzer = RuleLearing(data_dir, protocol_name, [], {})
    #print('all_types:{}'.format(all_types))
    rule_tuple, rule_string_list = minimzer.symmetry_reduction(candidate_inv_tuple, candidate_inv_string,
                                                               all_types)
    #print('tuple:{}'.format(rule_tuple))
    #print('string:{}'.format(rule_string_list))
    #**************************************************************************************************
    """
    # remove spurious invariants
    # start removing spurious invariants
    selector = SlctInv(data_dir, protocol_name, [], all_types, home=home_flag)
    _, counterex_index = selector.select_invariant(rule_string_list, keep_file=False, num_core=num_core,
                                                   original_file='{0}/{1}/{1}.m'.format(data_dir, protocol_name),
                                                   aux_para="-finderrors -ndl")

    tmp_tuple, tmp_string = copy.deepcopy(rule_tuple), copy.deepcopy(rule_string_list)
    for cex in counterex_index:
        tmp_tuple.remove(rule_tuple[cex])
        tmp_string.remove(rule_string_list[cex])
    rule_tuple, rule_string_list = tmp_tuple, tmp_string

    # instantiate invariants using symmetry expansion
    instantiator = RuleLearing(data_dir, protocol_name, [], {})
    aux_invs, aux_inv_string = instantiator.instantiate(rule_tuple, rule_string_list, all_types)

    """
    #return aux_invs, aux_inv_string
    return rule_tuple, rule_string_list


def cmp(data_dir, args, all_types, aux_invs, abs_filename, prot_analyzer):
    home_flag = False if args.node_num < 3 else True

    print_info, used_inv_string_list = prot_analyzer.refine_abstract(aux_invs, abs_type=args.abs_obj,
                                                                                     print_usedinvs_to_file=True,
                                                                                     boundary_K=1)
    #boundary_K=args.kmax
    #print('print_info:{}, used_inv_string_list:{}'.format(print_info, len(used_inv_string_list)))
    with open(abs_filename, 'a') as fw:
        fw.write(print_info)

    checker = SlctInv(data_dir, args.protocol, [], all_types, home=home_flag)
    counterex_index = checker.check_usedF(used_inv_string_list, 1, abs_filename,
                                          aux_para="-finderrors -ndl -m100",
                                          keep_file=True)
    if counterex_index:
            print('\nCounter-examples:{}\n'.format(counterex_index))
    else:
        print('End verifing, no counter-examples')
    return counterex_index, used_inv_string_list


def iter_cmp(data_dir, args, all_types=None, aux_invs=None, abs_filename=None, prot_analyzer=None, max_cnt=10):
    home_flag = False if args.node_num < 3 else True

    prot_dir = '{0}/{1}/{1}.m'.format(data_dir, args.protocol)
    counterex_index, used_inv_string_list = cmp(data_dir, args, all_types, aux_invs,
                                                abs_filename,
                                                prot_analyzer)
    if counterex_index:
        '''
        if still exists counterexample after strengthening,
        then iterate until max_cnt or no counterexample
        '''
        print('\n\n-----------------\nCounter example founded! Start iteration.\n')
        cnt = 1

        while counterex_index and cnt < max_cnt:
            tmp_string = copy.deepcopy(used_inv_string_list)
            for cex in counterex_index:
                tmp_string.remove(used_inv_string_list[cex])
            new_string_list = tmp_string
            new_inv_tuple = list(map(lambda x: split_string_to_tuple(x), new_string_list))

            new_absfile = "{2}/{0}/ABS_{0}_{1}.m".format(args.protocol, cnt, data_dir)
            copyfile(prot_dir, new_absfile)

            print_info, used_inv_string_list = prot_analyzer.refine_abstract(new_inv_tuple,
                                                                                             abs_type=args.abs_obj,
                                                                                             print_usedinvs_to_file=True,
                                                                                             boundary_K=1)
            with open(new_absfile, 'a') as fw:
                fw.write(print_info)
            checker = SlctInv(data_dir, args.protocol, [], all_types, home=home_flag)
            counterex_index = checker.check_usedF(used_inv_string_list, 1, new_absfile,
                                                  "-finderrors -ndl -m100",
                                                  keep_file=True)
            cnt += 1
        if counterex_index:
            print('\nCounter-examples:{}\n'.format(counterex_index))
    else:
        print('End verifing, no counter-examples')


def all(data_dir, args, murphi_url, max_cnt=10, end_with='all', abs_filename=None, recalculate=False):
    home_flag = False if args.node_num < 3 else True
    print('{}\nPreprocessing'.format('*' * 30))

    prot_analyzer = Protocol(data_dir, args.protocol, '{0}/{1}/{1}.m'.format(data_dir, args.protocol), home_flag)
    all_types = prot_analyzer.collect_atoms()
    print('all_types:{}'.format(all_types))

    if recalculate:
        dataset, itemMeaning, global_vars = pre(data_dir, args.protocol, args.node_num, murphi_url)
        if end_with == 'pre':
            return

        print('{}\nLearning'.format('*' * 3))
        rule_tuple, rule_string_list = learn(data_dir, args.protocol, dataset, itemMeaning, global_vars, args.kmax)
        if end_with == 'learn':
            return
        
        #(1)去除相同规则，例如p->q, p->q; p&q->r, q&p->r, 结果保存在newFile,1171->1146, 1146->892
        rule_string_list = removeSameRules(rule_string_list)
        rule_tuple = string2tuple(rule_string_list)
        print('len(rule_string_list):{}'.format(len(rule_string_list)))
        newFile = '{0}/{1}/removeSameRules.txt'.format(data_dir, args.protocol)
        with open(newFile, 'w') as nF:
            for rule_string in rule_string_list:
                nF.writelines(rule_string+'\n')

        #(2)对剩下的规则去除重复，即p->r 和 p&q->r同时存在时，删除p&q->r，结果保存在newFile,892->96
        rule_string_list = removeRepeatRules(rule_string_list)
        rule_tuple = string2tuple(rule_string_list)
        print('len(rule_string_list):{}'.format(len(rule_string_list)))
        newFile = '{0}/{1}/removeRepeatRules.txt'.format(data_dir, args.protocol)
        with open(newFile, 'w') as nF:
            for rule_string in rule_string_list:
                nF.writelines(rule_string+'\n')

        #(3)去除冗余, p->p, 结果保存在newFile,96->68
        rule_string_list = removeRedundancyRules(rule_string_list)
        rule_tuple = string2tuple(rule_string_list)
        print('len(rule_string_list):{}'.format(len(rule_string_list)))
        newFile = '{0}/{1}/removeRedundancyRules.txt'.format(data_dir, args.protocol)
        with open(newFile, 'w') as nF:
            for rule_string in rule_string_list:
                nF.writelines(rule_string+'\n')

        #(4)把剩余规则翻译成murphi语言，使用工具进行检测,
        test_rule_string_dict = {'rule_%d' % i: rule for i, rule in
                                 enumerate(rule_string_list, 1)}

        translate_dic = {}
        for key, rule in test_rule_string_dict.items():
            #all_types:{'NODE': 'NODENUMS', 'DATA': 'DATANUMS'}
            translate_dic.update({key: to_murphi(key, rule, all_types, home_flag)}) #.replace(';;',';')
        new_file = '{0}/{1}/ABS_{1}_{2}.m'.format(data_dir, args.protocol, 'checkByMurphi')
        
        dictlength = len(translate_dic) + 1 #初始化大小不一致，while跑起来
        falseRulesString = []
        falseRulesIndex = []

        #先直接把murphi检查后留下的规则赋值，避免重复运行检测，太耗费时间
        
        
        while(dictlength != len(translate_dic)):
            stopSign = 0
            copyfile('{0}/{1}/{1}.m'.format(data_dir, args.protocol), new_file)
            with open(new_file, 'a') as f:
                for key, value in translate_dic.items():
                    f.writelines(value)
            counter_ex_list = run_murphi_all(data_dir, args.protocol, 'ABS_{0}_{1}'.format(args.protocol, 'checkByMurphi'), murphi_url,
                                         aux_para="-finderrors -ndl")
            if len(counter_ex_list):
                stopSign = 1
                for counter_ex in counter_ex_list:
                    if not re.findall('rule_\d', counter_ex):
                        print(counter_ex)
                        break
                    falseRulesString.append(translate_dic['{}'.format(counter_ex)])
                    falseRulesIndex.append(int(counter_ex.split('_')[1]))
                    translate_dic.pop(counter_ex)
            if stopSign == 0:
                break
        newFile = '{0}/{1}/removedRulesByMurphi.txt'.format(data_dir, args.protocol)
        with open(newFile, 'w') as nF:
            for falseRule in falseRulesString:
                nF.writelines(falseRule+'\n')

        #把下标不是伪不变式的（正确的）保存在rule_string_list_filtered
        rule_string_list_filtered = []
        for i in range(len(rule_string_list)):
            if i+1 not in falseRulesIndex:
                rule_string_list_filtered.append(rule_string_list[i])
        #print(rule_string_list_filtered)
        rule_tuple_filtered = string2tuple(rule_string_list_filtered)
        
        

        #rule_string_list_filtered = ['n[NODE_2].st = C -> n[NODE_1].st != C', 'x = true -> n[NODE_1].st != C', 'n[NODE_2].st = E -> n[NODE_2].data = auxDATA', 'x = true -> n[NODE_2].st != E', 'n[NODE_2].st = E -> n[NODE_1].st != C', 'n[NODE_1].data != auxDATA -> n[NODE_1].st != E', 'x = true -> n[NODE_1].st != E', 'n[NODE_2].data != auxDATA -> n[NODE_1].data = auxDATA', 'n[NODE_2].st = C -> n[NODE_2].data = auxDATA', 'n[NODE_2].st = C -> n[NODE_1].st != E', 'n[NODE_2].st = E -> x = false', 'n[NODE_2].data != auxDATA -> n[NODE_2].st != E', 'n[NODE_2].st = E -> n[NODE_1].st != E', 'x = true -> n[NODE_2].st != C', 'n[NODE_1].data != auxDATA -> n[NODE_1].st != C', 'n[NODE_1].data != auxDATA -> n[NODE_2].data = auxDATA', 'n[NODE_2].data != auxDATA -> n[NODE_2].st != C', 'n[NODE_2].st = C -> x = false', 'n[NODE_2].st != I & n[NODE_2].st != T -> x = false']
        #rule_tuple_filtered = string2tuple(rule_string_list_filtered)

        print('{}\nExpansion'.format('*' * 30))
        newFile = '{0}/{1}/middleDocument.txt'.format(data_dir, args.protocol)
        copyfile('{0}/{1}/{1}.m'.format(data_dir, args.protocol), newFile)
        prot_analyzer = Protocol(data_dir, args.protocol, '{0}/{1}/{1}.m'.format(data_dir, args.protocol), home_flag)
        aux_invs, _ = select(data_dir, args.protocol, args.abs_obj, home_flag, 1, rule_tuple_filtered,
                             rule_string_list_filtered, prot_analyzer, all_types)
    else:
        if os.path.exists('{}/{}/data/aux_invs.json'.format(data_dir, args.protocol)):
            aux_invs = joblib.load('{}/{}/data/aux_invs.json'.format(data_dir, args.protocol))
        else:
            aux_invs = list(map(lambda x: x.split(': ')[-1],
                                open('{}/{}/aux_invs.txt'.format(data_dir, args.protocol), 'r').read().split('\n')))

            aux_invs = list(map(lambda x: split_string_to_tuple(x), aux_invs))
        print(aux_invs[:2])

    prot_analyzer = Protocol(data_dir, args.protocol, '{0}/{1}/{1}.m'.format(data_dir, args.protocol), home_flag)
    print('{}\nRecheck rules by murphi'.format('*' * 30))
    abs_filename = "{1}/{0}/ABS_{0}.m".format(args.protocol, data_dir) if abs_filename is None else abs_filename
    #abs_filename:./protocols/mutdata/ABS_mutdata.m
    #iter_cmp(data_dir, args, all_types, aux_invs, abs_filename, prot_analyzer, max_cnt=max_cnt)
    cmp(data_dir, args, all_types, aux_invs, abs_filename, prot_analyzer)


def gen_no_scalar(data_dir, prot_name):
    abs_filename = "{0}/{1}/ABS_{1}_1".format(data_dir, prot_name)
    noscar_filename = "{}_no_scalar".format(abs_filename)

    if os.path.exists("{}.m".format(abs_filename)):
        content = open("{}.m".format(abs_filename), 'r').read()
        new_content = re.sub(r'scalarset\((.*?)\);', r'1..\1;', content)
        open("{}.m".format(noscar_filename), 'w').write(new_content)


def main(arguments):
    parser = argparse.ArgumentParser(
        description='{0}\n{1}\n{0}\n'.format('*' * 15, 'Learning-based CMP (L-CMP)'),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('-all', '--all', help="\'all\': go through all options in L-CMP", action="store_true")
    group.add_argument('-pre', '--preprocess', help="\'preprocess\': calculate reachable set only", action="store_true")
    group.add_argument('-l', '--learn', help="\'learn\': learn auxiliary invariants only", action="store_true")
    group.add_argument('-cmp', '--cmp', help="\'cmp\': conduct cmp only", action="store_true")

    parser.add_argument('-p', '--protocol', help="Name of the protocol under verification.",
                        type=str, required=True)
    parser.add_argument('-a', '--abs_obj', help="Object under abstraction",
                        type=str, default='NODE')
    parser.add_argument('-n', '--node_num', help="Number of normal nodes", type=int, default=2)
    parser.add_argument('-k', '--kmax', help="Max size of frequent itemset", type=int, default=3)
    parser.add_argument('-s', '--support', help="Minimum support threshold", type=float, default=0.0)
    parser.add_argument('-c', '--confidence', help="Minimum confidence threshold", type=float, default=1.0)
    parser.add_argument('-i', '--iter', help="Max iteration of strengthening", type=int, default=2)
    parser.add_argument('-src', '--srcfile', help="Path to the protocol under verification.", type=str)
    parser.add_argument('-out', '--outputfile', help="Path to the destination protocol.", type=str)
    parser.add_argument('-r', '--recalculate', help="Whether recalculate all the support files.", type=str,
                        choices=['y', 'n'], default='n')

    args = parser.parse_args(arguments)
    print(args)

    murphi_url = pre_checker(data_dir='./protocols/', prot_name=args.protocol, murphi_dir='./murphi_url.txt')

    data_dir = './protocols'
    if args.all or args.cmp:
        all(data_dir, args, murphi_url, recalculate=args.recalculate == 'y')
    elif args.preprocess:
        all(data_dir, args, murphi_url, end_with='pre', recalculate=args.recalculate == 'y')
    elif args.learn:
        all(data_dir, args, murphi_url, end_with='learn', recalculate=args.recalculate == 'y')
    else:
        print('Require parameter \"-all\" or \"-pre\" or \"-\l"')

    gen_no_scalar(data_dir, args.protocol)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

