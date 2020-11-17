

def transform(p):
    if p == 'NODE_1':
        return "i"
    elif p == 'NODE_2':
        return "j"
    else:
        print('Parameter {} out of range'.format(p))
        return ""