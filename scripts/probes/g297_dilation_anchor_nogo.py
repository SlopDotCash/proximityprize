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


def require(condition: bool, message: str) -> None:
    """Keep the exact G297 coefficient certificate active under Python optimization."""
    if not condition:
        raise AssertionError(message)


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
    require(x==1 and len(set(out))==n, f"subgroup construction failed for p={p}, n={n}")
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
        require(
            sum(dp[r])==comb(len(G),r),
            f"subset histogram mass failed at r={r}",
        )
    return dp


def difference_corr(a:list[int],b:list[int],p:int)->list[int]:
    out=[0]*p
    for x,v in enumerate(a):
        if not v:continue
        for y,w in enumerate(b):
            if w:out[(x-y)%p]+=v*w
    require(sum(out)==sum(a)*sum(b), "difference correlation lost total mass")
    return out


def kernel(G:list[int],p:int,a:int)->list[int]:
    out=[0]*p
    for y in G:
        for z in G:out[(a*y-z)%p]+=1
    require(sum(out)==len(G)**2, f"kernel mass failed for coefficient a={a}")
    # For a != 0, W_a(t)=|aG intersect (G+t)|. At a=0, y has multiplicity n.
    if a:
        aG={a*y%p for y in G}
        Gs=set(G)
        for t in range(p):
            require(
                out[t]==sum(1 for x in aG if (x-t)%p in Gs),
                f"intersection formula failed for a={a}, t={t}",
            )
    return out


def alignment(W:list[int],R:list[int],p:int,n:int)->int:
    return p*sum(x*y for x,y in zip(W,R))-n*n*sum(R)


def main()->None:
    G=subgroup(P,N)
    Gset=set(G)
    require(pow(2,N,P)!=1, "target coefficient 2 unexpectedly lies in G")
    hist=subset_hist(G,P,6)
    family_W=[kernel(G,P,a) for a in range(P)]
    W1=family_W[1]
    W2=family_W[2]

    # Universal identities formalized in Lean: pointwise total mass and coset constancy.
    for t in range(P):
        require(
            sum(W[t] for W in family_W)==N*N,
            f"coefficient family total mass failed at t={t}",
        )
    for a in range(P):
        for u in G:
            require(
                family_W[a]==family_W[a*u%P],
                f"kernel coset invariance failed for a={a}, u={u}",
            )

    expected={
        5:(-2977296,1727120,4704416),
        6:(152176,-77440,-229616),
    }
    for r in (5,6):
        R=difference_corr(hist[r],hist[r-1],P)
        anchors=[alignment(W,R,P,N) for W in family_W]
        A1,A2=anchors[1],anchors[2]
        D=A2-A1
        require(
            (A1,A2,D)==expected[r],
            f"G297 exact witness pin failed at r={r}: {(A1,A2,D)}",
        )
        # Equal masses cancel the principal term exactly in the deformation.
        require(
            D==P*sum((x-y)*z for x,y,z in zip(W2,W1,R)),
            f"deformation identity failed at r={r}",
        )
        # The complete coefficient family is zero-sum. The nonzero sum is exactly -A_0.
        require(sum(anchors)==0, f"full coefficient family is not zero-sum at r={r}")
        require(sum(anchors[1:])==-anchors[0], f"nonzero family sum failed at r={r}")
        require(min(anchors)<0<max(anchors), f"full family lacks both signs at r={r}")
        # In this exact witness both signs also occur among nonzero quotient cosets. This is not
        # inferred from the full-family zero sum, where a=0 is a separate possible sign carrier.
        require(
            min(anchors[1:])<0<max(anchors[1:]),
            f"nonzero coefficient family lacks both signs at r={r}",
        )
        # Nonzero coefficients factor through F_p^*/G, and each coset has one anchor value.
        unseen=set(range(1,P))
        coset_values=[]
        while unseen:
            a=min(unseen)
            coset={a*u%P for u in Gset}
            unseen-=coset
            vals={anchors[x] for x in coset}
            require(len(vals)==1, f"coefficient values vary within coset {coset} at r={r}")
            coset_values.append(vals.pop())
        require(
            len(coset_values)==(P-1)//N,
            f"expected {(P-1)//N} nonzero cosets, got {len(coset_values)}",
        )
        print(
            f'p={P} n={N} r={r}: A1={A1:+d} A2={A2:+d} increment={D:+d}; '
            f'family sum=0, nonzero sum={sum(anchors[1:]):+d}=-A0, '
            f'nonzero range=[{min(anchors[1:]):+d},{max(anchors[1:]):+d}], '
            f'quotient cosets={len(coset_values)}'
        )
    require(expected[5][0]<0<expected[5][1], "rank-5 witness does not reverse anchor signs")
    require(expected[6][1]<0<expected[6][0], "rank-6 witness does not reverse anchor signs")
    print(
        'G297 PASS: coefficient profiles are coset-constant, the full anchor family sums to zero, '
        'and the same proper dyadic subgroup reverses A1/A2 sign transport at adjacent ranks.'
    )


if __name__=='__main__':main()
