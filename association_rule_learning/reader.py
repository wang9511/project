import os


def read_rules(file_dir):
    rules = []
    try:
        fr = open(file_dir)
        content = list(map(lambda x: x.split(': ')[1], filter(lambda x: x, fr.read().split('\n'))))
        fr.close()
    except IOError as e:
        print(e)
    else:
        for line in content:
            pre = set(line.strip().split(' -> ')[0].split(' & '))
            cond = line.strip().split(' -> ')[1]
            rules.append((pre, cond))
        print('read %d' % (len(rules)))
        return rules
