import re
import os
import sys
import subprocess


def run_murphi(data_dir, prot_name, murphi_dir, aux_para=''):
    print('[call murphi]compile murphi to cpp....')
    print(murphi_dir, prot_name, data_dir)
    command1 = "{0}/src/mu {2}/{1}/{1}.m".format(murphi_dir, prot_name, data_dir)
    command2 = "g++ -ggdb -o {0}/{1}/{1}.o {0}/{1}/{1}.cpp -I {2}/include -lm".format(data_dir, prot_name,
                                                                                      murphi_dir)
    command3 = "{0}/{1}/{1}.o -m1000 {2}".format(data_dir, prot_name, aux_para)

    print('command1 = {}'.format(command1))
    print('command2 = {}'.format(command2))
    print('command3 = {}'.format(command3))

    print('compile murphi file to cpp....')

    process1 = subprocess.Popen(command1,
                                shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    (stdout, stderr) = process1.communicate()
    if not re.search(r'Code generated', stdout.decode('utf-8')):
        print('Wrong', stderr.decode('utf-8'))
        raise ValueError
        sys.exit()
    else:
        print('Code generated')

    print('compile .cpp to .o file....')
    try:
        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        (stdout, stderr) = process2.communicate()
    except:
        raise ValueError(stdout.decode('utf-8'))

    print('running .o file....')

    try:
        process = subprocess.Popen(command3, shell=True,
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process.communicate()
    except:
        raise ValueError(stdout.decode('utf-8'))
    else:
        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed.')
        counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
        if len(counter_ex):
            print("%s failed!" % ','.join(counter_ex))

        os.remove('{0}/{1}/{1}.cpp'.format(data_dir, prot_name))
        os.remove('{0}/{1}/{1}.o'.format(data_dir, prot_name))

    return counter_ex if len(counter_ex) else []

# check mutdata.m and translated associate rules
def run_murphi_all(data_dir, prot_name, checkFile_name, murphi_dir, aux_para=''):
    print('[call murphi]compile murphi to cpp....')
    command1 = "{0}/src/mu {2}/{1}/{3}.m".format(murphi_dir, prot_name, data_dir, checkFile_name)
    command2 = "g++ -ggdb -o {0}/{1}/{3}.o {0}/{1}/{3}.cpp -I {2}/include -lm".format(data_dir, prot_name,
                                                                                      murphi_dir, checkFile_name)
    command3 = "{0}/{1}/{3}.o -m1000 {2}".format(data_dir, prot_name, aux_para, checkFile_name)

    print('command1 = {}'.format(command1))
    print('command2 = {}'.format(command2))
    print('command3 = {}'.format(command3))

    print('compile murphi file to cpp....')

    process1 = subprocess.Popen(command1,
                                shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    (stdout, stderr) = process1.communicate()
    if not re.search(r'Code generated', stdout.decode('utf-8')):
        print('Wrong', stderr.decode('utf-8'))
        raise ValueError
        sys.exit()
    else:
        print('Code generated')

    print('compile .cpp to .o file....')
    try:
        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        (stdout, stderr) = process2.communicate()
    except:
        raise ValueError(stdout.decode('utf-8'))

    print('running .o file....')

    try:
        process = subprocess.Popen(command3, shell=True,
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process.communicate()
    except:
        raise ValueError(stdout.decode('utf-8'))
    else:
        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed.')
        counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
        print('counter_ex:{}'.format(counter_ex))
        if len(counter_ex):
            print("%s failed!" % ','.join(counter_ex))

        os.remove('{0}/{1}/{2}.cpp'.format(data_dir, prot_name, checkFile_name))
        os.remove('{0}/{1}/{2}.o'.format(data_dir, prot_name, checkFile_name))

    return counter_ex if len(counter_ex) else []