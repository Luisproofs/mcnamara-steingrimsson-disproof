"""Exact interval rank enumeration for a direct sum of two skew-layered permutations."""
from math import comb


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] = x
    for i, x in enumerate(b):
        c[i] += x
    return c


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                c[i+j] += x*y
    return c


def chunks(ch):
    return tuple(a for k in ch for a in [1]*k+[2])


def all_patterns(ch):
    f = [1]
    for k in reversed(ch):
        d = [1]*(k+1)
        v = add([0]*(k+1)+[1,1], [0,0]+[1]*k)
        f = add(d, mul(v, f))
    return f


def good(w):
    t = w.count(2)
    return [0]*len(w)+[comb(t,i) for i in range(t+1)]


def interval(c, d):
    u, v = chunks(c), chunks(d)
    assert len(u) == len(v) >= 2
    g, h = good(u), good(v)
    total = add(mul(g, all_patterns(d)), mul(all_patterns(c), h))
    both = add(mul(g,h), good(tuple(map(min,u,v))))
    return add(total, [-x for x in both])


def template(p, copies):
    k = 2*(2**p-1)
    return [k]*copies, ([2]*p+[0]*(k+1-3*p))*copies


def short_example():
    u = (1,)*8+(2,)+(1,)*9
    v = (2,)*4+(1,2)*5+(2,)*4
    fu = add([1]*19,[0,0]+mul([1]*9,[1]*10))
    fv = all_patterns([0]*4+[1]*5+[0]*4)
    a,b = good(u),good(v)
    positive = add(mul(a,fv),mul(fu,b))
    overlap = add(mul(a,b),good(tuple(map(min,u,v))))
    return u,v,add(positive,[-n for n in overlap])


def main():
    u,v,h = short_example()
    assert sum(u)+sum(v)==50
    assert h[37:40]==[78468,78022,78544]
    assert sum(h)==1125373
    print('Length-50 witness. Ranks 19, 20, 21:', *h[37:40])
    c,d = template(3,4)
    h = interval(c,d)
    assert h[121:124]==[318760232883761,314759367160492,318217445359443]
    print('Length-160 witness. Ranks 61, 62, 63:', *h[121:124])


if __name__ == '__main__':
    main()
