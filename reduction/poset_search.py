"""Construct all subpermutations of one top, then count ranks for every bottom by reachability."""
from functools import lru_cache
from collections import defaultdict
from itertools import permutations,product
from pathlib import Path
from random import Random
from binary_search import valley,coeffs,X

tables=[bytes(j-(j>v) for j in range(256)) for v in range(100)]

@lru_cache(30000)
def children(p):
    return tuple({(p[:i]+p[i+1:]).translate(tables[a]) for i,a in enumerate(p)
        if i==0 or abs(a-p[i-1])!=1})

def profiles(top,maximum=5000):
    # Supersets at one fixed rank are one contiguous band of bit positions.
    # Track only proper rank levels created so far.
    level={top:0}
    bands=[]
    initial=0
    while level:
        k=len(next(iter(level)))
        if initial+len(level)>maximum:return
        b=(1<<len(level))-1
        bands.append((initial,b))
        lower={}
        for j,(p,anc) in enumerate(level.items()):
            anc|=1<<(initial+j)
            if k>0:
                r=tuple(((anc>>s)&m).bit_count() for s,m in reversed(bands))
                yield p,r
            if k>1:
                for q in children(p):
                    lower[q]=lower.get(q,0)|anc
        initial+=len(level);level=lower

def inflate(p,w):
    return bytes(x for j in p for x in range(sum(w[:j]),sum(w[:j+1])))

def product_search():
    known={}
    for n in range(3,8):
        for p in permutations(range(n)):
            top=bytes(p)
            for lo,h in profiles(top):
                if len(h)>3:known.setdefault(h,(lo,top))
        print('product factors',n,len(known),flush=True)
    rep={h:sum(q*(X**i) for i,q in enumerate(h)) for h in known}
    bylen=sorted(rep,key=lambda h:len(known[h][1]))
    for j,h in enumerate(bylen):
        for v in bylen[:j+1]:
            c=coeffs(rep[h]*rep[v])
            if valley(c):
                print('PRODUCT seed',list(known[h][0]),list(known[h][1]),h,list(known[v][0]),list(known[v][1]),v,c,flush=True);return
    print('all product pairs',len(bylen)*(len(bylen)+1)//2,flush=True)

if __name__=='__main__':product_search()
