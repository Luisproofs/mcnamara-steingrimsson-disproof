"""Search binary capacity hosts using the published two-summand counting formula.
The all-pattern polynomial depends only on the unordered gaps between twos.
"""
from functools import lru_cache
from itertools import accumulate
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "permutation-experiments"))
from shrink_permutation import shrink, test as original_test
from math import comb

BITS = 64
X = 1 << BITS
MASK = X-1

def coeffs(p):
    d = p.to_bytes((p.bit_length()+BITS-1)//BITS*8,'little')
    return memoryview(d).cast('Q').tolist()

def valley(h):
    fallen = False
    for a,b in zip(h,h[1:]):
        if a>b: fallen=True
        if a<b and fallen:return True
    return False

def partitions(n,k,lo=0):
    if k==1:
        if n>=lo:yield (n,)
        return
    for a in range(lo,n//k+1):
        for q in partitions(n-a,k-1,a):yield (a,)+q

def word(gaps):
    w=[]
    for t in gaps[:-1]:
        w.extend([1]*t+[2])
    return tuple(w+[1]*gaps[-1])

@lru_cache(None)
def captypes(r,t):
    results=[]
    for gaps in partitions(r-t,t+1):
        w=word(gaps)
        f=1
        one=two=0
        for b in w:
            one=f*X
            if b==2:two=f*X**2
            f=1+one+two
        mask=sum(1<<i for i,b in enumerate(w) if b==2)
        results.append((f,w,mask))
    return results

def search(limit,marked=True):
    attempts=0
    for n in range(8,limit+1):
        for r in range(max(2,(n+3)//4),n//2+1):
            for t in range(max(0,n-3*r),(n-2*r)//2+1):
                s=n-2*r-t
                if s>r:continue
                for f,u,um in captypes(r,t):
                    for h,v,vm in captypes(r,s):
                        m=(um&vm).bit_count()
                        for p in range(m+1 if marked else 1):
                            a,b=(1+X)**(t-p),(1+X)**(s-p)
                            poly=a*h+b*f-X**(r+p)*a*b-(1+X)**(m-p)
                            attempts+=1
                            rank=coeffs(poly)
                            if valley(rank):
                                print('hit',n,r,p,u,v,rank,'tests',attempts,flush=True)
                                return
        if n%5==0: print('through',n,'tests',attempts,flush=True)
    print('finished',attempts,flush=True)

if __name__=='__main__':
    u=(1,)*8+(2,)+(1,)*9; v=(2,)*4+(1,2)*5+(2,)*4
    assert sum(map(sum,shrink(u,v)))==50
    search(int(sys.argv[1]) if len(sys.argv)>1 else 43)
