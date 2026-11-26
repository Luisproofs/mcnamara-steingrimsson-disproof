from math import comb
from random import Random
from functools import lru_cache
from itertools import product
from heapq import nsmallest
random=Random(123805)
# Coefficients at lengths d are digit d in a huge power-of-two base. Rank counts <= 2^n < 2^128 for candidates.
# For larger n just use 256. Sum extraction only at end.
shift=192
x=1<<shift
mask=x-1
def digits(p):
    h=[]
    while p:
        h.append(p&mask)
        p >>= shift
    return h
@lru_cache(15000)
def fg(u):
    f=1
    g=1
    end=[0]*max(u)
    for a in u:
        for t in range(a):
            end[t]=f<<(shift*(t+1))
        f=1+sum(end)
        g*=sum(x**t for t in range(1,a+1))
    return f,g
def test(u,v):
    f,g=fg(u)
    h,b=fg(v)
    m=fg(tuple(map(min,u,v)))[1]
    ranks=digits((g*h+f*b-g*b-m)>>(len(u)*shift))
    decreasing=False
    for i in range(1,len(ranks)):
        if ranks[i]<ranks[i-1]:
            decreasing=True
        elif ranks[i]>ranks[i-1] and decreasing:
            return ranks
def rec(w):
    return tuple(a for k in w for a in [1]*k+[2])
def shrink(u,v):
    while True:
        opts=[]
        for i in range(len(u)):
            for j in range(len(v)):
                if len(u)>2:
                    opts.append((u[:i]+u[i+1:],v[:j]+v[j+1:]))
        for i in range(len(u)):
            if u[i]>1: opts.append((u[:i]+(u[i]-1,)+u[i+1:],v))
            if v[i]>1: opts.append((u,v[:i]+(v[i]-1,)+v[i+1:]))
        random.shuffle(opts)
        hit=next(((a,b) for a,b in opts if test(a,b)),None)
        if not hit: return u,v
        u,v=hit
if __name__=='__main__':
    best=200
    for r in range(2,24):
        for k in range(1,r+1):
            for t in range(1,7):
                for b in range(1,6):
                    for s in range(1,5):
                        u=tuple([1]*(r-k)+[t]*k)
                        v=tuple([b]*min(s,r)+[1]*max(0,r-s))
                        if sum(u)+sum(v)>=best: continue
                        if test(u,v):
                            best=sum(u)+sum(v)
                            print('block',best,u,v,test(u,v),flush=True)
    for i in range(22000):
        r=random.randrange(2,min(best//2,22)+1)
        def word():
            q=random.randrange(1,r+1)
            lo=random.randrange(1,r-q+2)
            p=random.randrange(2,6)
            opts=[1]*(r-q)+[p]*q
            if random.randrange(2):
                random.shuffle(opts)
            else:
                opts=opts[lo:]+opts[:lo]
            return tuple(opts)
        u,v=word(),word()
        if sum(u)+sum(v)>=best:continue
        if test(u,v):
            best=sum(u)+sum(v)
            print('random',best,u,v,test(u,v),flush=True)
    if best==200:
        u,v=shrink(rec([14]*4),rec(([2]*3+[0]*6)*4))
        print('shrink',sum(u)+sum(v),u,v,test(u,v),flush=True)
