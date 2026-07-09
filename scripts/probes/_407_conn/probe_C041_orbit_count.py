"""
C041 decisive test: orbit count of the MAX-BAD extremal stack set under the full
PGL2-normalizer-style group, at a PROPER subgroup mu_n < F_q^* (prize regime),
vs the F5 toy (full group => #400 trap).

Search reduction: the 2-dim RS code on n points lets us use codeword translation
to put each row into a canonical form (subtract the unique codeword agreeing on the
first k=2 coordinates, zeroing coords 0,1).  So we enumerate u0,u1 over the q^{n-k}
coset representatives, recover the orbit/extremal structure of the FULL stack space
exactly (translation is in the group).

We then count orbits of the extremal set under:
  G_noT  = <translation, scaling, gamma-shift, rotation>            (affine + rotation)
  G_full = G_noT + twisted inversion T (the C041 'decisive' generator)
"""
import itertools, sympy

def analyze(q, n, k):
    g0 = sympy.primitive_root(q)
    gen = pow(g0, (q-1)//n, q)
    xs = [pow(gen, i, q) for i in range(n)]
    proper = (q-1) > n
    # Vandermonde of first k columns to canonicalize via translation
    # codeword from coeffs:
    def cw(coeffs):
        return tuple(sum(coeffs[j]*pow(x,j,q) for j in range(k)) % q for x in xs)
    cws = [cw(c) for c in itertools.product(range(q),repeat=k)]
    cwset=set(cws)
    # admissible subsets, delta = 1/n
    floor_dn = (1*n)//n  # =1
    minS = n - floor_dn
    subsets = [S for r in range(minS, n+1) for S in itertools.combinations(range(n),r)]
    allbits=(1<<len(subsets))-1
    cache={}
    def ext(w):
        m=cache.get(w)
        if m is not None: return m
        m=0
        for bit,S in enumerate(subsets):
            if any(all(c[i]==w[i] for i in S) for c in cws):
                m|=1<<bit
        cache[w]=m; return m
    def badcount(u0,u1):
        e0,e1=ext(u0),ext(u1); both=e0&e1; cnt=0
        for g in range(q):
            line=tuple((a+g*b)%q for a,b in zip(u0,u1))
            if ext(line)&~both&allbits: cnt+=1
        return cnt
    # twisted inversion
    pos={x:i for i,x in enumerate(xs)}
    xinv={x:pow(x,q-2,q) for x in xs}
    sigma=[pos[xinv[xs[i]]] for i in range(n)]
    d=[pow(xs[i],k-1,q) for i in range(n)]
    def T(u): return tuple(d[i]*u[sigma[i]]%q for i in range(n))
    assert all(T(c) in cwset for c in cws), "T not a code symmetry!"

    # ---- canonical form via translation: solve for codeword agreeing on coords 0..k-1 ----
    import numpy as np
    V = [[pow(xs[i],j,q) for j in range(k)] for i in range(k)]  # k x k Vandermonde on first k pts
    # inverse mod q
    def matinv_modq(M):
        M=[row[:] for row in M]; m=len(M)
        I=[[1 if i==j else 0 for j in range(m)] for i in range(m)]
        for col in range(m):
            piv=None
            for r in range(col,m):
                if M[r][col]%q!=0: piv=r;break
            M[col],M[piv]=M[piv],M[col]; I[col],I[piv]=I[piv],I[col]
            inv=pow(M[col][col],q-2,q)
            M[col]=[(x*inv)%q for x in M[col]]; I[col]=[(x*inv)%q for x in I[col]]
            for r in range(m):
                if r!=col and M[r][col]%q!=0:
                    f=M[r][col]
                    M[r]=[(a-f*b)%q for a,b in zip(M[r],M[col])]
                    I[r]=[(a-f*b)%q for a,b in zip(I[r],I[col])]
        return I
    Vinv=matinv_modq(V)
    def canon(u):
        # coeffs c s.t. cw(c) agrees with u on first k coords: c = Vinv * u[0:k]
        c=[sum(Vinv[i][j]*u[j] for j in range(k))%q for i in range(k)]
        sub=cw(c)
        return tuple((u[i]-sub[i])%q for i in range(n))  # zeros on coords 0..k-1
    # representatives: words with coords 0..k-1 = 0 (the q^{n-k} coset reps)
    free=range(n-k)
    reps=[]
    for tail in itertools.product(range(q),repeat=n-k):
        reps.append(tuple([0]*k + list(tail)))
    # full group generators (acting on full stack, then we canonicalize for orbit bookkeeping)
    basisC=[cw([1 if j==t else 0 for j in range(k)]) for t in range(k)]
    s_scale=gen
    def gens(u0,u1,useT):
        out=[]
        for c in basisC:
            out.append((tuple((a+e)%q for a,e in zip(u0,c)),u1))
            out.append((u0,tuple((a+e)%q for a,e in zip(u1,c))))
        out.append((tuple(s_scale*a%q for a in u0),tuple(s_scale*a%q for a in u1)))
        out.append((tuple((a+b)%q for a,b in zip(u0,u1)),u1))
        out.append((tuple(u0[(i+1)%n] for i in range(n)),tuple(u1[(i+1)%n] for i in range(n))))
        if useT: out.append((T(u0),T(u1)))
        return out
    def canon_stack(s): return (canon(s[0]),canon(s[1]))

    # find max-bad over the reduced rep space (translation-invariant => exact)
    maxbad=-1; extremal=set()
    for u0 in reps:
        for u1 in reps:
            b=badcount(u0,u1)
            if b>maxbad: maxbad=b; extremal={(u0,u1)}
            elif b==maxbad: extremal.add((u0,u1))
    # but extremal set in canonical (reps) coords. Orbit walk on canonical reps:
    def orbit_count(useT):
        rem=set(extremal); norb=0; sizes=[]
        while rem:
            s=next(iter(rem)); seen={s}; fr=[s]
            while fr:
                cur=fr.pop()
                # apply gens in FULL coords then canonicalize back to a rep
                # but cur is canonical; lift to full = cur itself (coords0..k-1=0 is a valid full word)
                for t in gens(cur[0],cur[1],useT):
                    ct=canon_stack(t)
                    if ct not in seen:
                        seen.add(ct); fr.append(ct)
            orb_ext = seen & extremal
            sizes.append(len(orb_ext)); norb+=1
            rem-=seen
        return norb, sizes
    norb_noT, sizes_noT = orbit_count(False)
    norb_full, sizes_full = orbit_count(True)
    return dict(q=q,n=n,k=k,proper=proper,index=(q-1)//n,maxbad=maxbad,
                n_extremal=len(extremal),orbits_noT=norb_noT,orbits_full=norb_full,
                sizes_noT=sorted(sizes_noT,reverse=True)[:6],
                sizes_full=sorted(sizes_full,reverse=True)[:6])

if __name__=="__main__":
    for (q,n,k) in [(5,4,2),(13,4,2),(17,4,2),(29,4,2),(37,4,2)]:
        r=analyze(q,n,k)
        print(f"RS[F{r['q']},mu_{r['n']},k={r['k']}] proper={r['proper']} idx={r['index']}: "
              f"maxbad={r['maxbad']} #extremal(reps)={r['n_extremal']} "
              f"orbits(no T)={r['orbits_noT']} orbits(full,+T)={r['orbits_full']}")
        print(f"    top orbit sizes  no-T: {r['sizes_noT']}   full: {r['sizes_full']}")
