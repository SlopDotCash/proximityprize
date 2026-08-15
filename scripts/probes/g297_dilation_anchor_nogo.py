#!/usr/bin/env python3
"""G297 exact probe: the coefficient-1 cyclotomic anchor does not transport to W_2.

For G=mu_16 in F_113 and a in {1,2}, compute
  W_a(t)=#{(y,z) in G^2 : a*y-z=t},
  R_r(t)=#{(S,T): |S|=r, |T|=r-1, sum(S)-sum(T)=t},
  A_a(r)=p*sum_t W_a(t)R_r(t)-n^2*sum_t R_r(t).
All arithmetic is Python integer arithmetic. No FFT and no floating point are used.
"""
from __future__ import annotations
from math import comb

P=113
N=16


def factors(n:int)->list[int]:
    out=[]
    d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out


def primitive_root(p:int)->int:
    fs=factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
    raise RuntimeError('no primitive root')


def subgroup(p:int,n:int)->list[int]:
    root=primitive_root(p)
    h=pow(root,(p-1)//n,p)
    out=[]
    x=1
    for _ in range(n):
        out.append(x)
        x=x*h%p
    assert x==1 and len(set(out))==n
    return out


def subset_hist(G:list[int],p:int,max_r:int)->list[list[int]]:
    dp=[[0]*p for _ in range(max_r+1)]
    dp[0][0]=1
    used=0
    for x in G:
        used+=1
        for r in range(min(used,max_r),0,-1):
            for s,v in enumerate(dp[r-1]):
                if v:dp[r][(s+x)%p]+=v
    for r in range(max_r+1):
        assert sum(dp[r])==comb(len(G),r)
    return dp


def difference_corr(a:list[int],b:list[int],p:int)->list[int]:
    out=[0]*p
    for x,v in enumerate(a):
        if not v:continue
        for y,w in enumerate(b):
            if w:out[(x-y)%p]+=v*w
    assert sum(out)==sum(a)*sum(b)
    return out


def kernel(G:list[int],p:int,a:int)->list[int]:
    out=[0]*p
    for y in G:
        for z in G:out[(a*y-z)%p]+=1
    assert sum(out)==len(G)**2
    # For a != 0, W_a(t)=|aG intersect (G+t)|. At a=0, y has multiplicity n.
    if a:
        aG={a*y%p for y in G}
        Gs=set(G)
        for t in range(p):
            assert out[t]==sum(1 for x in aG if (x-t)%p in Gs)
    return out


def alignment(W:list[int],R:list[int],p:int,n:int)->int:
    return p*sum(x*y for x,y in zip(W,R))-n*n*sum(R)


def main()->None:
    G=subgroup(P,N)
    Gset=set(G)
    assert pow(2,N,P)!=1  # target coefficient lies outside G
    hist=subset_hist(G,P,6)
    family_W=[kernel(G,P,a) for a in range(P)]
    W1=family_W[1]
    W2=family_W[2]

    # Universal identities formalized in Lean: pointwise total mass and coset constancy.
    for t in range(P):
        assert sum(W[t] for W in family_W)==N*N
    for a in range(P):
        for u in G:
            assert family_W[a]==family_W[a*u%P]

    expected={
        5:(-2977296,1727120,4704416),
        6:(152176,-77440,-229616),
    }
    for r in (5,6):
        R=difference_corr(hist[r],hist[r-1],P)
        anchors=[alignment(W,R,P,N) for W in family_W]
        A1,A2=anchors[1],anchors[2]
        D=A2-A1
        assert (A1,A2,D)==expected[r]
        # Equal masses cancel the principal term exactly in the deformation.
        assert D==P*sum((x-y)*z for x,y,z in zip(W2,W1,R))
        # The complete coefficient family is zero-sum. The nonzero sum is exactly -A_0.
        assert sum(anchors)==0
        assert sum(anchors[1:])==-anchors[0]
        assert min(anchors)<0<max(anchors)
        # In this exact witness both signs also occur among nonzero quotient cosets. This is not
        # inferred from the full-family zero sum, where a=0 is a separate possible sign carrier.
        assert min(anchors[1:])<0<max(anchors[1:])
        # Nonzero coefficients factor through F_p^*/G, and each coset has one anchor value.
        unseen=set(range(1,P))
        coset_values=[]
        while unseen:
            a=min(unseen)
            coset={a*u%P for u in Gset}
            unseen-=coset
            vals={anchors[x] for x in coset}
            assert len(vals)==1
            coset_values.append(vals.pop())
        assert len(coset_values)==(P-1)//N
        print(
            f'p={P} n={N} r={r}: A1={A1:+d} A2={A2:+d} increment={D:+d}; '
            f'family sum=0, nonzero sum={sum(anchors[1:]):+d}=-A0, '
            f'nonzero range=[{min(anchors[1:]):+d},{max(anchors[1:]):+d}], '
            f'quotient cosets={len(coset_values)}'
        )
    assert expected[5][0]<0<expected[5][1]
    assert expected[6][1]<0<expected[6][0]
    print(
        'G297 PASS: coefficient profiles are coset-constant, the full anchor family sums to zero, '
        'and the same proper dyadic subgroup reverses A1/A2 sign transport at adjacent ranks.'
    )


if __name__=='__main__':main()
