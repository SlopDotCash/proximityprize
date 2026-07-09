#!/usr/bin/env python3
"""ADVERSARIAL VERIFICATION of finding F3 (#407 p-defect onset).

CLAIM (F3): E_r(mu_n) computed mod p (the F_p additive energy of the order-n
dyadic subgroup) equals the CHARACTERISTIC-0 value E_r^(0) until r ~ beta, then
INFLATES (the "p-defect"). Reported: n=32,beta=4 -> +0.7% at r=4, +4% at r=5.
Also: the 4th moment (r=2) is EXACTLY char-0 (= 3n^2 - 3n).

DEFINITIONS (made precise, fresh code):
  mu_n = order-n multiplicative subgroup of F_p* (n=2^mu, n | p-1).
  E_r^{Fp}  := #{(x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_j  (mod p)}
            = sum_t a_r(t)^2,  a_r = r-fold ADDITIVE convolution (mod p) of the
              mu_n indicator; computed EXACTLY via FFT over Z/p.
  E_r^{(0)} := char-0 additive energy = same count with mu_n the abstract n-th
              roots of unity in C (equality of complex sums, no mod-p coincidence).

CHAR-0 METHOD (exact, prime-free):  n = 2^mu => Z[zeta_n] = Z[x]/(x^{n/2}+1).
  A multiset of exponents {i_1..i_r} subset (Z/n) maps to a complex sum
  zeta^{i_1}+...+zeta^{i_r}. Two complex sums are EQUAL iff their canonical
  reduced vectors agree, where the reduced vector c in Z^{n/2} is
      c_k = (#exponents == k)  -  (#exponents == k + n/2),   k = 0..n/2-1
  (because zeta^{k+n/2} = -zeta^k).  E_r^(0) = sum over reduced-vectors v of
  N(v)^2 where N(v) = # of r-tuples in (Z/n)^r whose reduced vector is v.
  We get the full distribution {N(v)} EXACTLY by an r-fold convolution of the
  single-root distribution over the finite group (Z/(n/2))^{?}... implemented
  here directly by exact polynomial powering: represent the count generating
  object as a dict mapping reduced-vector(tuple) -> count, and raise the
  single-root distribution to the r-th convolution power.  E_r^(0) = sum c^2.

  This is independent of p, exact integer arithmetic.

CROSS-CHECK: also compute E_r at two MODERATE generic primes P1,P2 (~1e5) far
  from the prize prime; for the small r tested they must equal the prime-free
  char-0 value -- a fully independent confirmation that the prime-free reduction
  is correct.

E_r^{Fp} via FFT: validated exact (sum a_r == n^r, residual tiny).
Also reports (2r-1)!! * n^r (leading 'all-free Sidon' term, NOT exact char-0).
"""
import sys, math
from collections import defaultdict
from itertools import product
import numpy as np


def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True


def odd_part(x):
    while x % 2 == 0: x //= 2
    return x


def primitive_root(p):
    phi = p-1; facs = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs): return g
    raise RuntimeError


def subgroup(p, n):
    g = primitive_root(p)
    eta = pow(g, (p-1)//n, p)
    H = [pow(eta, i, p) for i in range(n)]
    assert len(set(H)) == n, "subgroup not order n"
    return H


def energy_Fp(p, n, r):
    """EXACT E_r = sum_t a_r(t)^2 (mod-p r-fold convolution of mu_n indicator)."""
    H = subgroup(p, n)
    ind = np.zeros(p, dtype=np.float64)
    for h in H:
        ind[h] += 1.0
    F = np.fft.rfft(ind)
    Fr = F ** r
    a = np.fft.irfft(Fr, n=p)
    a_round = np.rint(a)
    max_err = float(np.max(np.abs(a - a_round)))
    total = float(a_round.sum())
    ok = (abs(total - n**r) < 0.5) and (max_err < 0.49)
    E = float(np.sum(a_round * a_round))
    return int(round(E)), ok, max_err, total


def char0_energy_exact(n, r):
    """EXACT char-0 additive energy of n-th roots of unity (n=2^mu), prime-free.
    Reduced-vector key in Z^{n/2} via zeta^{k+n/2} = -zeta^k.
    Builds N(v) = #{r-tuples in (Z/n)^r with reduced vector v} by exact
    convolution-powering, then E_r^(0) = sum_v N(v)^2."""
    assert n & (n-1) == 0, "n must be a power of 2"
    half = n // 2

    def reduced_key_of_tuple(t):
        c = [0] * half
        for e in t:
            k = e % n
            if k < half:
                c[k] += 1
            else:
                c[k - half] -= 1
        return tuple(c)

    # single-root distribution: e in 0..n-1 -> key
    # convolve r times.  state: dict key(tuple len half) -> count
    base = defaultdict(int)
    for e in range(n):
        c = [0] * half
        k = e % n
        if k < half:
            c[k] += 1
        else:
            c[k - half] -= 1
        base[tuple(c)] += 1
    # base has n entries each count 1 (keys e_k and -e_k distinct)
    state = {(0,) * half: 1}
    for _ in range(r):
        new = defaultdict(int)
        for ka, va in state.items():
            for kb, vb in base.items():
                key = tuple(ka[i] + kb[i] for i in range(half))
                new[key] += va * vb
        state = new
    total = sum(state.values())
    assert total == n ** r, f"char0 tuple count {total} != {n**r}"
    E = sum(v * v for v in state.values())
    return E


def char0_bruteforce_smalln(n, r):
    """Independent O(n^r) brute force for tiny cases (validation only)."""
    cnt = defaultdict(int)
    half = n // 2
    for t in product(range(n), repeat=r):
        c = [0] * half
        for e in t:
            if e < half: c[e] += 1
            else: c[e - half] -= 1
        cnt[tuple(c)] += 1
    return sum(v * v for v in cnt.values())


def char0_largeprime_consensus(n, r, want=3, start_m=120000, jump=70001):
    """`want` generic LARGE primes (P ~ n*1.2e5 .. ); a value that all agree on
    is the char-0 energy (no single-prime defect survives across independent
    large primes). Returns (Ps, vals, consensus_or_None)."""
    Ps = []; used = set()
    target_m = start_m
    base = n * target_m + 1
    cand = base - (base % n) + 1
    while len(Ps) < want:
        if cand > 3 and is_prime(cand) and odd_part((cand-1)//n) > 1 and cand not in used:
            Ps.append(cand); used.add(cand)
            target_m += jump
            base = n * target_m + 1
            cand = base - (base % n) + 1
            continue
        cand += n
    vals = []
    for P in Ps:
        E, ok, err, tot = energy_Fp(P, n, r)
        assert ok, f"consensus FFT not exact P={P}"
        vals.append(E)
    consensus = vals[0] if len(set(vals)) == 1 else None
    return Ps, vals, consensus


def find_prize_prime(n, beta, used):
    p_target = int(round(n ** beta))
    base = p_target - (p_target % n) + 1
    cand = base
    tries = 0
    while tries < 5_000_000:
        if cand > 3 and is_prime(cand) and odd_part((cand-1)//n) > 1 and cand not in used:
            used.add(cand)
            return cand
        cand += n
        tries += 1
    raise RuntimeError(f"no prize prime n={n} beta={beta}")


def double_factorial_leading(n, r):
    df = 1
    for k in range(1, 2*r, 2):
        df *= k
    return df * (n ** r)


def main():
    print("=" * 110)
    print("F3 ADVERSARIAL VERIFICATION: p-defect onset for E_r(mu_n) in F_p vs char-0")
    print("=" * 110)

    # --- self-validation of the prime-free char-0 routine ---
    print("\n[self-check] prime-free char-0 vs O(n^r) brute force (tiny cases):")
    for (n, r) in [(8, 2), (8, 3), (16, 2), (16, 3)]:
        e1 = char0_energy_exact(n, r)
        e2 = char0_bruteforce_smalln(n, r)
        print(f"   n={n} r={r}:  conv={e1}  brute={e2}  match={e1==e2}")

    # independent confirmation that exact char-0 == large-prime consensus
    print("\n[cross-check] exact char-0 == 3-large-prime consensus (P ~ n*1.2e5):")
    for n in (16, 32):
        for r in (2, 3, 4):
            E0 = char0_energy_exact(n, r)
            Ps, vals, cons = char0_largeprime_consensus(n, r)
            print(f"   n={n} r={r}: exact={E0}  consensus={cons}  primes_agree={cons is not None}"
                  f"  match={cons == E0}  vals={vals}")

    used = set()
    PMAX_FFT = 5_000_000  # cap full-p FFT to keep float exactness + speed
    for n in (16, 32):
        for beta in (4, 5):
            p = find_prize_prime(n, beta, used)
            m = (p - 1) // n
            print(f"\n### n={n} beta={beta} -> p={p} (p^(1/beta)={p**(1/beta):.2f} vs n={n};"
                  f" m={m}; odd_part(m)={odd_part(m)})")
            if p > PMAX_FFT:
                print(f"   [SKIP full-p FFT: p={p} > {PMAX_FFT} (float-exactness/speed cap)]")
                continue
            print(f"{'r':>2} {'E_r^Fp':>18} {'E_r^char0':>18} {'defect':>14} "
                  f"{'rel_defect':>11} {'(2r-1)!!n^r':>16}")
            for r in range(2, 6):
                Efp, ok_fp, err_fp, tot_fp = energy_Fp(p, n, r)
                if not ok_fp:
                    print(f"{r:>2}  FFT NOT EXACT (err={err_fp:.2e}, tot={tot_fp} vs {n**r})")
                    continue
                E0 = char0_energy_exact(n, r)
                lead = double_factorial_leading(n, r)
                defect = Efp - E0
                rel = defect / E0 if E0 else 0.0
                print(f"{r:>2} {Efp:>18} {E0:>18} {defect:>14} {rel:>11.4%} {lead:>16}")
    print("\n" + "=" * 110)
    print("GUIDE: defect==0 => F_p matches char-0; defect>0 => p-defect (extra mod-p collisions).")
    print("  r=2 defect must be 0 (4th moment = char-0 = 3n^2-3n). F3: onset of defect>0 at r ~ beta.")
    print("=" * 110)


if __name__ == "__main__":
    main()
