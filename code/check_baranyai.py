# Constructs Baranyai 1-factorisations via the vertex-by-vertex induction used in the Lean proof
# (fractional assignment -> integral assignment by bipartite matching with capacities), then verifies.
from itertools import combinations
from math import comb
import sys
def match(rows, cap):  # rows: list of lists of allowed columns; cap: dict col->capacity. Kuhn with capacities
    assign={}; load={c:[] for c in cap}
    def aug(i,seen):
        for c in rows[i]:
            if c in seen: continue
            seen.add(c)
            if len(load[c])<cap[c]: load[c].append(i); assign[i]=c; return True
            for i2 in list(load[c]):
                if aug(i2,seen):
                    load[c].remove(i2); load[c].append(i); assign[i]=c; return True
        return False
    for i in range(len(rows)):
        if not aug(i,set()): return None
    return assign
def baranyai(n,k):
    assert n%k==0
    m=n//k; M=comb(n-1,k-1)
    A=[[frozenset() for _ in range(m)] for _ in range(M)]
    for j in range(n):
        rows=[sorted({S for S in A[i] if len(S)<k},key=sorted) for i in range(M)]
        cap={}
        for S in {S for r in A for S in r}:
            cap[S]=comb(n-j-1,k-len(S)-1) if len(S)<k else 0
        a=match(rows,cap); assert a is not None
        for i in range(M):
            t=A[i].index(a[i]); A[i][t]=A[i][t]|{j}
    return A
def verify(n,k,A):
    allk=set(frozenset(c) for c in combinations(range(n),k)); seen=[]
    for cls in A:
        assert all(len(S)==k for S in cls)
        assert sorted(v for S in cls for v in S)==list(range(n))
        seen+=cls
    assert len(seen)==len(allk) and set(seen)==allk
    return True
for n,k in [(4,2),(6,2),(6,3),(8,4),(9,3),(8,2),(10,5),(12,4),(12,3)]:
    A=baranyai(n,k); print(n,k,"classes",len(A),"ok",verify(n,k,A))
# negative control: k not dividing n -> C(n,k) not divisible by n/k-sized matchings / no perfect matching exists
for n,k in [(7,3),(5,2),(10,4)]:
    print(n,k,"k|n?",n%k==0,"perfect matching possible?", n%k==0)
