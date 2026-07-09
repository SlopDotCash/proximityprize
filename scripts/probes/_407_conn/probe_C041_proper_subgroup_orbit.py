"""
C041 attack: does the "single PGL2-normalizer orbit collapses the worst-case stack"
result survive at a PROPER multiplicative subgroup mu_n < F_q^* (the prize regime),
or is it an artifact of the F5 toy where domain (1,2,4,3)=<2> is the FULL group F_5^*
(q-1 = n = 4)?  Full group => #400 trap (false positive).

We test RS[F_q, mu_n, k] for several proper subgroups (n < q-1).
Generators of the symmetry group (mirroring the F5 probe + the C041 record):
  - codeword translation  (u0,u1) -> (u0+c0, u1) and (u0, u1+c1), c0,c1 in basis of C
  - whole-stack scaling   (u0,u1) -> (s*u0, s*u1)
  - gamma-shift           (u0,u1) -> (u0+u1, u1)
  - rotation              x -> g*x on the domain (multiplicative)   [mcaEvent_rs_rotate]
  - twisted inversion     (Tu)[i] = d(x_i) * u(sigma(x_i)), sigma: x->1/x, d(x)=x^{k-1}
                          [the Mobius/PGL2 generator; the C041 'decisive' move]

Claim under test (C041 / MCAMonomialEquivariance docstring):
  the worst-case (max-bad) extremal stacks form a SINGLE orbit under the FULL group
  (affine+rotation+twisted-inversion), so the eps_mca sup reduces to ONE representative.

Honesty: at F5 the domain is the full group -> any PGL2 toy collapse is the #400 trap.
The prize needs PROPER mu_n.  We check (a) the twisted inversion stabilizes the proper
code at all, and (b) the orbit count of the extremal set.
"""
import sys, itertools, sympy

def run(q, n, k, full_search_cap=None, verbose=True):
    g0 = sympy.primitive_root(q)
    gen = pow(g0, (q-1)//n, q)
    # domain in rotation order: x_i = gen^i
    xs = [pow(gen, i, q) for i in range(n)]
    proper = (q-1) > n
    # codewords: degree < k polynomials evaluated on xs.  Basis monomials 1,x,...,x^{k-1}.
    def cw(coeffs):
        return tuple(sum(coeffs[j]*pow(x, j, q) for j in range(k)) % q for x in xs)
    cws = [cw(c) for c in itertools.product(range(q), repeat=k)]
    cwset = set(cws)
    # admissible witness subsets for delta = (n - ceil... ) ; use radius matching the F5 probe:
    # F5 used subsets of size 3,4 for n=4,k=2 (size >= n-k+1 = agreement >= n-(delta n)).
    # delta = 1/4 at n=4 -> bad if line agrees with code on a (1-delta)n = 3-subset.
    # general: a stack is "explainable on S" if some codeword agrees on S; bad scalar g
    # = line u0+g u1 explainable on some admissible S but the PAIR is not jointly explainable.
    # We replicate the F5 probe's structure exactly: admissible subsets of size >= n-floor(delta n).
    import math
    dnum, dden = 1, n  # delta = 1/n  (matches F5: delta=1/4 at n=4); the extremal radius rung
    floor_dn = (dnum*n)//dden
    minS = n - floor_dn
    subsets = [S for r in range(minS, n+1) for S in itertools.combinations(range(n), r)]
    # per-word extension bitmask
    words_all = None
    # extension test for a single word (lazy, cached)
    cache = {}
    def ext(w):
        m = cache.get(w)
        if m is not None: return m
        m = 0
        for bit, S in enumerate(subsets):
            if any(all(c[i]==w[i] for i in S) for c in cws):
                m |= 1<<bit
        cache[w] = m
        return m
    allbits = (1<<len(subsets)) - 1
    def badcount(u0,u1):
        e0, e1 = ext(u0), ext(u1)
        both = e0 & e1
        cnt = 0
        for g in range(q):
            line = tuple((a+g*b)%q for a,b in zip(u0,u1))
            if ext(line) & ~both & allbits:
                cnt += 1
        return cnt

    # twisted inversion: sigma: x_i -> x_i^{-1} (a permutation of xs since mu_n is a group);
    # diagonal d(x)=x^{k-1}.  (Tu)[i] = d(x_i)*u[idx(1/x_i)].
    inv_index = {}
    xinv = {x: pow(x, q-2, q) for x in xs}
    pos = {x:i for i,x in enumerate(xs)}
    sigma = [pos[xinv[xs[i]]] for i in range(n)]   # i -> index of 1/x_i
    d = [pow(xs[i], k-1, q) for i in range(n)]
    def T(u):
        return tuple(d[i]*u[sigma[i]] % q for i in range(n))
    T_stab = all(T(c) in cwset for c in cws)

    # untwisted inversion (for contrast)
    def Tu_untw(u):
        return tuple(u[sigma[i]] for i in range(n))
    Tuntw_stab = all(Tu_untw(c) in cwset for c in cws)

    if verbose:
        print(f"--- RS[F{q}, mu_{n} (gen={gen}, xs={xs}), k={k}] proper={proper} index={(q-1)//n}")
        print(f"    delta=1/{n}, admissible |subsets|={len(subsets)}, |C|={len(cws)}")
        print(f"    twisted-inversion stabilizes code: {T_stab}; untwisted: {Tuntw_stab}")

    # group generators acting on a stack (u0,u1)
    cw1 = cw([0,1] + [0]*(k-2)) if k>=2 else cw([0])   # the 'x' codeword (a translation gen)
    cwx = cws[1] if len(cws)>1 else cws[0]
    # use a small generating set: translate by two basis codewords, scale by gen, shift, rotate, T
    basisC = [cw([1 if j==t else 0 for j in range(k)]) for t in range(k)]
    s_scale = gen  # a nonzero scalar (also a unit)
    def gens(u0,u1):
        out=[]
        for c in basisC:
            out.append((tuple((a+e)%q for a,e in zip(u0,c)), u1))
            out.append((u0, tuple((a+e)%q for a,e in zip(u1,c))))
        out.append((tuple(s_scale*a%q for a in u0), tuple(s_scale*a%q for a in u1)))
        out.append((tuple((a+b)%q for a,b in zip(u0,u1)), u1))
        out.append((tuple(u0[(i+1)%n] for i in range(n)), tuple(u1[(i+1)%n] for i in range(n))))
        out.append((T(u0), T(u1)))
        return out
    def gens_noT(u0,u1):
        return gens(u0,u1)[:-1]

    def orbit(stack, genfn):
        seen={stack}; fr=[stack]
        while fr:
            s=fr.pop()
            for t in genfn(*s):
                if t not in seen:
                    seen.add(t); fr.append(t)
        return seen

    return dict(q=q,n=n,k=k,proper=proper,index=(q-1)//n,T_stab=T_stab,
                Tuntw_stab=Tuntw_stab, badcount=badcount, gens=gens, gens_noT=gens_noT,
                orbit=orbit, cws=cws, words_iter=lambda: itertools.product(range(q),repeat=n))

if __name__ == "__main__":
    # 1) sanity: reproduce that twisted inversion stabilizes; show full-vs-proper distinction
    for (q,n,k) in [(5,4,2),(13,4,2),(17,4,2),(29,4,2)]:
        run(q,n,k,verbose=True)
        print()
