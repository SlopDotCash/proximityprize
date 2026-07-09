"""
SYMMETRIES lens probe 3: does the dihedral reflection act on the INDEX-SET level
(DyadicFourierUncertainty.powerSum / shift-closed index sets I subset Z/N)?

In DyadicFourierUncertainty, the object is f(X)=sum_{i in I} X^i, p_j(I)=f(zeta^j).
The cyclic dilation on mu_N corresponds to i -> i + c (shift) on indices I subset Z/N.
The inversion x -> x^{-1} on mu_N corresponds to i -> -i on indices.
The antipodal x -> -x = zeta^{N/2} * x corresponds to i -> i + N/2.
So Mobius sigma: x -> -x^{-1} corresponds on indices to  i -> N/2 - i.

CLAIM: the map rho: I -> {N/2 - i : i in I} is an involution on index sets that
(a) preserves cardinality |I|=a,
(b) maps a set with vanishing power sums p_1..p_{t-1}=0 to another such set
    (because p_j(rho I) = sum zeta^{j(N/2-i)} = zeta^{jN/2} * conj-ish... test exactly),
(c) hence is a free involution on the char-0 lacunary count C(N/tau, a/tau),
    so that count is EVEN unless rho has fixed points.

Test (b)+(c) exhaustively for small N=2^mu.
"""
import cmath, math, itertools

def probe(mu, t):
    N = 2**mu
    zeta = cmath.exp(2j*math.pi/N)
    def psum(I, j):
        return sum(zeta**((j*i) % N) for i in I)
    refl = lambda I: frozenset((N//2 - i) % N for i in I)
    results = {}
    for a in range(1, N+1):
        good = []
        for I in itertools.combinations(range(N), a):
            Iset = frozenset(I)
            if all(abs(psum(Iset, j)) < 1e-9 for j in range(1, t)):
                good.append(Iset)
        goodset = set(good)
        # check reflection preserves the good family
        closed = all(refl(I) in goodset for I in goodset)
        fixed = sum(1 for I in goodset if refl(I) == I)
        results[a] = (len(goodset), closed, fixed)
    return N, results

if __name__ == "__main__":
    for mu in [3, 4]:
        for t in [2, 3, 5]:
            N, res = probe(mu, t)
            print(f"N={N} t={t}:")
            for a, (cnt, closed, fixed) in res.items():
                if cnt > 0:
                    parity = "EVEN" if cnt % 2 == 0 else "ODD"
                    print(f"   a={a:2d}: count={cnt:4d} reflClosed={closed} #fixed={fixed} ({parity})")
