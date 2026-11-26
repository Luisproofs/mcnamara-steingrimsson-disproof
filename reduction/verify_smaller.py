"""Literal interval enumeration under arbitrary-position classical pattern containment."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from independent_permutation import make_top,skew_runs
from poset_search import children
from check_by_deletion import EXPECTED

def literal_sides(lower,right):
    from mixed import downset,indecomp,addsum
    assert indecomp(lower)
    L=downset(lower)
    R=downset(right)
    accepted=[set() for layer in R]
    accepted[len(lower)]={lower} & R[len(lower)]
    for k in range(len(lower)+1,len(R)):
        accepted[k]={w for w in R[k] if any(c in accepted[k-1] for c in children(w))}
    rows={}
    for i,A in enumerate(L):
        for j,B in enumerate(R):
            allowed=B if i==len(lower) else accepted[j]
            if allowed:
                rows.setdefault(i+j,set()).update(addsum(a,b) for a in A for b in allowed)
    return [len(rows[k]) for k in range(len(lower),len(lower)+len(right)+1)]

def encode(v):return bytes(x-1 for x in skew_runs(v))

if __name__=='__main__':
    u=(1,)*7+(2,)+(1,)*6
    v=(2,)+(2,1)*7
    h=literal_sides(encode(u),encode(v))
    assert tuple(h) == EXPECTED
    print('lower',tuple(x+1 for x in encode(u)))
    print('top',make_top(u,v))
    print('ranks',h,'total',sum(h),flush=True)
