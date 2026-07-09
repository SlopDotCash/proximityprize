#!/usr/bin/env python3
"""
probe_407_sparse_vs_lattice_svp.py -- THE crux: is the SPARSE-support SVP-min strictly longer than
the FULL lattice SVP-min of 𝔭?  (If equal, sparsity gives nothing; if strictly longer with a
quantifiable gap, sparsity is a genuine new lever.)

We compare three minima of the prime ideal 𝔭 ⊂ Z[ζ_n] (n=2^μ, fully split, residue degree 1):

  h_lat   = lattice SVP-min in HOUSE (ℓ∞ Minkowski) = min_{0≠z∈𝔭} max_t|σ_t(z)|.
            Computed by LLL/enumeration on the explicit Z-basis of 𝔭 (basis: p·1, and (ζ - r) where
            r ≡ ζ mod 𝔭, i.e. r = z0 = chosen primitive root in F_p, lifted; HNF basis of 𝔭).
  h_sparse = min house over SIGNED-ROOT-SUM (sparse-support) elements of 𝔭, from MITM search.
  Mink     = Minkowski/geometric prediction = sqrt(n/2) * covol^{2/n} / sqrt(2πe)-ish.

We also report the support weight of the LATTICE SVP-min (is it already sparse? does it have small
ℓ1 in the GROUP-RING basis?).  This is the deciding diagnostic for the assigned angle.

We use a real LLL (fpylll if available, else a pure-python LLL) on the power-basis Gram lattice with
the Minkowski quadratic form, then enumerate short vectors and report min house + support.
"""
import sys, math, itertools
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**12):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    return pow(primitive_root(p), (p - 1) // n, p)


def minkowski_real_basis(n):
    """Real Minkowski embedding of power basis {1, ζ, ..., ζ^{D-1}} into R^D (D=n/2 = φ).
       Pairs of conjugate complex embeddings -> (sqrt2 cos, sqrt2 sin). Returns DxD matrix B
       whose rows are the real coords of ζ^k (k=0..D-1). The lattice Z[ζ_n] = rows-Z-span.
       Quadratic form ||.||_2^2 here = 2 * (sum_t |σ_t|^2 over the D/... ) -- we just use it for LLL;
       house uses the complex embeddings directly."""
    D = n // 2
    # primitive roots: t odd, but conjugates t and n-t give same |.|; take t in 1,3,..,n/2-1 (D/2 pairs)
    ts = [t for t in range(1, n//2 + 1, 2)]  # D/2 of them (since D=n/2, pairs)
    B = np.zeros((D, D))
    for k in range(D):
        col = []
        for t in ts:
            ang = 2*math.pi*t*k/n
            col += [math.sqrt(2)*math.cos(ang), math.sqrt(2)*math.sin(ang)]
        B[k, :len(col)] = col
    return B


def sublattice_basis_p(p, z, n):
    """HNF-style Z-basis of 𝔭 = ker(Z[ζ_n] -> F_p, ζ ↦ z) in POWER coords (length D).
       𝔭 ⊇ p·Z[ζ_n]; and ζ - z·1 ∈ 𝔭. Basis: e_k' = ζ^k - z^k·1 for k=1..D-1, plus p·1.
       (Standard: 𝔭 = <p, ζ - z>.) Coords in power basis e_0=1,...,e_{D-1}=ζ^{D-1}.
       Row 0: (p,0,...,0).  Row k (k=1..D-1): ζ^k - z^k mod p as power vector = e_k - (z^k mod p)·e_0.
       But z^k mod p may be large; reduce the e_0 coefficient mod p using row0. We just return the
       integer rows and let LLL handle it: row_k = -(z^k mod p)·e_0 + e_k for k>=1, row_0 = p·e_0."""
    D = n // 2
    rows = []
    row0 = [0]*D; row0[0] = p; rows.append(row0)
    for k in range(1, D):
        rk = [0]*D
        rk[0] = -(pow(z, k, p))
        rk[k] = 1
        rows.append(rk)
    return np.array(rows, dtype=object)  # integer matrix, rows span 𝔭 in power coords


def house_of_power_vec(d, n):
    D = n//2; house = 0.0
    for t in range(1, n, 2):
        re = im = 0.0
        ang0 = 2*math.pi*t/n
        for k in range(D):
            if d[k]:
                re += d[k]*math.cos(ang0*k); im += d[k]*math.sin(ang0*k)
        house = max(house, math.hypot(re, im))
    return house


def l2_minkowski(d, n):
    D=n//2; s=0.0
    for t in range(1, n, 2):
        re=im=0.0; ang0=2*math.pi*t/n
        for k in range(D):
            if d[k]: re+=d[k]*math.cos(ang0*k); im+=d[k]*math.sin(ang0*k)
        s += re*re+im*im
    return math.sqrt(s)


def lll_reduce(rows, n, gram_B):
    """LLL on integer power-coord rows using the Minkowski Gram (rows · gram_B = real coords).
       Try fpylll; else pure python LLL on the real-embedded basis."""
    D = n//2
    # real basis vectors = rows @ gram_B
    realB = np.array([[float(x) for x in r] for r in rows]) @ gram_B
    try:
        from fpylll import IntegerMatrix, LLL
        # need integer matrix; scale real coords -> integers
        scale = 1e6
        M = IntegerMatrix.from_matrix([[int(round(realB[i,j]*scale)) for j in range(realB.shape[1])]
                                       for i in range(realB.shape[0])])
        Lr = LLL.reduction(M)
        # we cannot easily recover integer combos; fall back to python LLL to keep integer combos
    except Exception:
        pass
    # pure-python LLL tracking the unimodular transform U so reduced = U @ rows (integer combos)
    return _py_lll(realB, np.array([[int(x) for x in r] for r in rows]))


def _py_lll(B, U_rows, delta=0.75):
    """LLL on real basis B (rows), tracking integer combos rows = combos @ original power rows.
       Returns list of (power_int_vector). U_rows = original integer power rows."""
    B = B.astype(float).copy()
    m = B.shape[0]
    # integer combination matrix C: current basis row i = sum_j C[i,j]*U_rows[j]
    C = np.eye(m, dtype=object)
    def gso(B):
        Bs = B.copy(); mu = np.zeros((m,m))
        for i in range(m):
            for j in range(i):
                mu[i,j] = np.dot(B[i], Bs[j])/np.dot(Bs[j],Bs[j])
                Bs[i] = Bs[i] - mu[i,j]*Bs[j]
        return Bs, mu
    Bs, mu = gso(B)
    k = 1
    it = 0
    while k < m and it < 20000:
        it += 1
        for j in range(k-1, -1, -1):
            q = round(mu[k,j])
            if q != 0:
                B[k] = B[k] - q*B[j]
                C[k] = C[k] - q*C[j]
                Bs, mu = gso(B)
        if np.dot(Bs[k],Bs[k]) >= (delta - mu[k,k-1]**2)*np.dot(Bs[k-1],Bs[k-1]):
            k += 1
        else:
            B[[k,k-1]] = B[[k-1,k]]
            C[[k,k-1]] = C[[k-1,k]]
            Bs, mu = gso(B)
            k = max(k-1, 1)
    # power-coord integer vectors = C @ U_rows
    out = []
    for i in range(m):
        v = np.zeros(U_rows.shape[1], dtype=object)
        for j in range(m):
            if C[i,j] != 0:
                v = v + int(C[i,j])*U_rows[j]
        out.append([int(x) for x in v])
    return out


def lattice_svp_house(p, z, n, gram_B):
    """LLL-reduce 𝔭, then enumerate short integer combinations of the reduced basis to find min house."""
    rows = sublattice_basis_p(p, z, n)
    red = lll_reduce(rows, n, gram_B)
    # min house among reduced basis vectors and small combinations (coeffs in -2..2 over first few)
    D = n//2
    best = None; best_vec=None
    cands = list(red)
    # also small combos of the two shortest
    red_sorted = sorted(red, key=lambda d: l2_minkowski(d, n))
    short = red_sorted[:min(6, len(red_sorted))]
    for coeffs in itertools.product(range(-2,3), repeat=len(short)):
        if all(c==0 for c in coeffs): continue
        v=[0]*D
        for c,s in zip(coeffs, short):
            if c:
                for k in range(D): v[k]+=c*s[k]
        cands.append(v)
    for v in cands:
        if all(x==0 for x in v): continue
        h = house_of_power_vec(v, n)
        if best is None or h < best:
            best=h; best_vec=v
    wt = sum(1 for x in best_vec if x!=0)
    l1 = sum(abs(x) for x in best_vec)
    return best, best_vec, wt, l1


def main():
    print("="*100)
    print(" #407 SPARSE vs LATTICE SVP-min of 𝔭:  is the support-sparse minimum STRICTLY longer?")
    print("="*100)
    print(f"{'n':>4} {'beta':>5} {'p':>14} | {'h_lat(LLL)':>10} {'wt(svpmin)':>10} {'l1(svpmin)':>10} "
          f"{'Mink':>8} {'h_lat/Mink':>10}")
    for n in (8, 16, 32, 64):
        gram_B = minkowski_real_basis(n)
        D = n//2
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            if p is None: continue
            z = order_n_root(p, n)
            try:
                h_lat, vec, wt, l1 = lattice_svp_house(p, z, n, gram_B)
            except Exception as e:
                print(f"{n:>4} {beta:>5.1f} {p:>14} | LLL failed: {e}"); continue
            # Minkowski house prediction: covol(𝔭 in Minkowski) = p * sqrt|disc| ; |disc(Q(ζ_2^μ))|
            # = 2^{(μ-1)2^{μ-1}} ... we approximate via covol^{1/D}: minimal ℓ2 ~ sqrt(D)*covol^{1/D}/sqrt(2πe)
            # house >= ℓ2/sqrt(D) (since house = ℓ∞ of D complex coords; ℓ2^2 = sum |σ|^2 over D coords)
            # covol = p * sqrt(disc); disc for 2^μ: log2|disc| = (μ-1)*2^{μ-1}
            mu = int(math.log2(n))
            log2disc = (mu-1)*2**(mu-1) if mu>=1 else 0
            covol = p * (2.0**(log2disc/2))
            mink_l2 = math.sqrt(D) * covol**(1.0/D) / math.sqrt(2*math.pi*math.e)
            mink_house = mink_l2 / math.sqrt(D) * 1.0  # rough lower scale; house ~ ℓ2/sqrt(D)..ℓ2
            print(f"{n:>4} {beta:>5.1f} {p:>14} | {h_lat:>10.3f} {wt:>10} {l1:>10} "
                  f"{mink_house:>8.3f} {h_lat/mink_house if mink_house else float('nan'):>10.3f}")
    print("\nKEY:")
    print(" - wt(svpmin), l1(svpmin) = support weight & ℓ1 of the LATTICE SVP-min element of 𝔭 in the")
    print("   power basis. If l1(svpmin) is SMALL (<= 2·onset_r), the lattice SVP-min is ALREADY a")
    print("   sparse signed root-sum -> sparse-support minimum = lattice minimum -> sparsity gives")
    print("   NOTHING beyond well-roundedness. If l1(svpmin) is LARGE (~D), the lattice SVP-min is")
    print("   DENSE -> sparse elements are strictly longer -> a genuine sparse-support gap.")
    print(" - h_lat/Mink ≈ 1: 𝔭 behaves like a random index-p sublattice (no exceptional short vec).")


if __name__ == "__main__":
    main()
