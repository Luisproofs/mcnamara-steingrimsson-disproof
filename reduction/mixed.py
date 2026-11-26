"""Test an arbitrary indecomposable lower pattern on two sides of a direct sum.
Literal side patterns provide inputs to the earlier polynomial union formula.
Candidates are independently tested on the resulting ordinary interval.
"""
from poset_search import children,profiles
from binary_search import X,BITS,coeffs,valley
from random import Random
from functools import lru_cache
from itertools import permutations,product
@lru_cache(30000)
def indecomp(p):
    m=-1
    for i,b in enumerate(p[:-1]):
        m=max(m,b)
        if i==m:return False
    return len(p)>1

def downset(p):
    high=[{p}]
    while len(next(iter(high[-1])))>1:
        high.append({c for a in high[-1] for c in children(a)})
    return [{b''}]+list(reversed(high))

@lru_cache(5000)
def free(p):return sum(len(s)<<(BITS*i) for i,s in enumerate(downset(p)))

def addsum(u,v):
    return u+bytes(i+len(u) for i in v)

def bothways(top,cap=6000):
    level={top}; levels=[]
    while level:
        levels.append(sorted(level))
        if sum(map(len,levels))>cap:return
        level={q for p in level for q in children(p)} if len(next(iter(level)))>1 else set()
    levels.reverse()
    nodes=[a for l in levels for a in l]; offset={p:i for i,p in enumerate(nodes)}
    supers=[1<<i for i in range(len(nodes))]
    decomposed=0
    for i in reversed(range(len(nodes))):
        p=nodes[i]
        if len(p)>1 and not indecomp(p):decomposed|=1<<i
        for q in children(p):
            if q:supers[offset[q]] |= supers[i]
    masks=[];s=0
    for layer in levels:
        masks.append(((1<<len(layer))-1)<<s);s+=len(layer)
    ft=1+sum(len(l)<<(BITS*j) for j,l in enumerate(levels,1))
    for i,p in enumerate(nodes):
        if not indecomp(p) or supers[i]&decomposed:continue
        good=sum((supers[i]&m).bit_count()<<(BITS*j) for j,m in enumerate(masks[len(p)-1:]))
        yield p,ft,good

def skew(a,b):return bytes(x+len(b) for x in a)+b

def draw(rng,n):
    typ=rng.randrange(5)
    if n<=4 or typ==0:
        a=list(range(n));rng.shuffle(a);return bytes(a)
    i=rng.randrange(1,n)
    a=draw(rng,i);b=draw(rng,n-i)
    return addsum(a,b) if typ==1 else skew(a,b)

def run(trials):
    rng=Random(12049);checks=0;best=43;catalog={};tops=0
    for it in range(trials):
        n=rng.randint(5,15)
        top=draw(rng,n)
        if not indecomp(top):continue
        tops+=1
        for p,f,g in bothways(top):
            # Previously sampled hosts admitting this same bottom; both have
            # only indecomposable good patterns. Single-factor overlap vanishes
            # above the shorter side length.
            m=len(p)
            if top==p:continue
            row=catalog.setdefault(p,[])
            for other,h,b in [(p,free(p),1)]+row:
                if n+len(other)>=best:continue
                checks+=1
                combined=g*h+b*f-(g*b<<(BITS*m))
                start=min(len(other),n)-m+1
                if valley(coeffs(combined>>(BITS*start))):
                    best=n+len(other)
                    print('HIT',best,'bottom',list(p),'sides',list(other),list(top),'tail from rank',start,coeffs(combined>>(BITS*start)),flush=True)
            if not any((h,b)==(f,g) for _,h,b in row):
                if len(row)<32:row.append((top,f,g))
                elif rng.randrange(12)==0:row[rng.randrange(32)]=(top,f,g)
        if (it+1)%500==0:print('draws',it+1,'checks',checks,flush=True)
    print('final',tops,checks,best,flush=True)
if __name__=='__main__':
    import sys
    run(int(sys.argv[1]))
