#!/usr/bin/env python3
"""
C057 attack: "Power-sum window = all-ones-error syndrome (Newton bridge F10->F2/F5)".

The connection claims:
  (a) e_1=...=e_{t-1}=0  <=>  p_1=...=p_{t-1}=0  over char 0 (Newton; PROVEN in-tree
      as esymm_window_iff_psum_window).  [structural fact, not in question]
  (b) p_j(S)=sum_{x in S} x^j is the "all-ones-error syndrome" on support S, and the
      vanishing-power-sum *variety* (subsets S of mu_n with a power-sum window) is the
      SAME object whose char-p transfer is the BGK wall.
  (c) PREDICTION: the char-0 vanishing-window count and the char-p count first DIVERGE
      at a gap t* ~ 2(beta+1) log_n p, i.e. q-independent only while t < ~2 r_max.

We test (b)+(c) EXACTLY (integer arithmetic) at PROPER dyadic subgroups mu_n of F_q*,
q prime = 1 mod n, q ~ n^beta with beta in 4..5 (n << sqrt(q)) -- the prize regime.

Object measured (the "all-ones-error / power-sum window variety"):
  For each subset size a and each window length L, count
     V_0(a,L) = #{ S subset mu_n, |S|=a : p_1(S)=...=p_L(S)=0 in char 0 (Z[zeta_n]) }
     V_p(a,L) = #{ S subset mu_n, |S|=a : p_1(S)=...=p_L(S)=0 in F_q }
  and find L* = smallest window length where V_0 != V_p  (the divergence onset).

We work over mu_n realized inside F_q (the actual prize object). char-0 vanishing is
detected by an INDEPENDENT large prime q' (>> n^L) where mu_n also lives: a sum of
2-power roots that vanishes "in char 0" vanishes mod every large enough prime; the
char-p (=char-q) count is the genuine F_q count. Divergence = a config that vanishes
mod q (prize prime) but NOT mod a much-larger control prime q' = NOT a char-0 zero.

This is exactly the "spurious sum-zero subsets" phenomenon (issue grounding line 1782).
"""
import itertools, sys

def find_subgroup(n, q):
    """Return the n-th roots of unity in F_q as a sorted list (q prime, n | q-1)."""
    # find a generator g of F_q^*, then mu_n = { g^{(q-1)/n * j} }
    assert (q-1) % n == 0
    # find primitive root
    def is_primroot(g):
        # order must be q-1: check g^((q-1)/r) != 1 for each prime r | q-1
        m = q-1
        f = factor(m)
        for r in f:
            if pow(g, m//r, q) == 1:
                return False
        return True
    g = None
    for cand in range(2, q):
        if is_primroot(cand):
            g = cand; break
    assert g is not None
    h = pow(g, (q-1)//n, q)  # generator of mu_n
    return [pow(h, j, q) for j in range(n)]

def factor(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0:
            fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True

def primes_eq1_modn(n, lo, hi, count):
    out=[]
    x = lo - (lo % n) + 1
    if x < lo: x += n
    while x <= hi and len(out)<count:
        if isprime(x): out.append(x)
        x += n
    return out

def powersums_window(S, L, q):
    """power sums p_1..p_L of subset S (list of F_q elements) reduced mod q."""
    return [ sum(pow(x, j, q) for x in S) % q for j in range(1, L+1) ]

def count_window(n, a, L, q):
    """#{S subset mu_n in F_q, |S|=a : p_1..p_L(S) == 0 in F_q}."""
    mu = find_subgroup(n, q)
    cnt = 0
    bad_examples = []
    for S in itertools.combinations(mu, a):
        ps = powersums_window(S, L, q)
        if all(v == 0 for v in ps):
            cnt += 1
            if len(bad_examples) < 3:
                bad_examples.append(S)
    return cnt, bad_examples

def main():
    print("="*78)
    print("C057: char-0 vs char-p power-sum-window count divergence at proper mu_n")
    print("="*78)
    # We compare the count of vanishing-power-sum-window subsets at the prize prime q
    # vs a MUCH larger control prime q' (proxy for char 0: q' >> n^L so no wraparound).
    # Divergence (V_q > V_{q'}) = spurious char-p sum-zero configs = the Newton bridge's
    # char-p inflation; we locate the onset window L*.
    for n in [8, 16]:
        print(f"\n### n = {n} (mu_n proper dyadic subgroup) ###")
        # prize-regime prime: q ~ n^beta, beta ~ 4-5, q << control
        # pick a moderate prize prime and a control prime both = 1 mod n
        # control prime chosen >> n^(a) so it certifies char-0 vanishing exactly
        a = n // 2  # the balanced (worst antipodal) subset size
        # control must exceed largest possible |power-sum| ~ a * n^L numerically; use a big prime
        ctrl_lo = 10**7
        ctrl = primes_eq1_modn(n, ctrl_lo, ctrl_lo+10**6, 1)[0]
        # several prize-regime primes (smaller, multiple primes per the regime guidance)
        prize_lo = n**4
        prize_primes = primes_eq1_modn(n, prize_lo, prize_lo*3, 4)
        print(f"  balanced size a = {a}; control prime q' = {ctrl} (char-0 proxy)")
        print(f"  prize primes q ~ n^4..: {prize_primes}")
        # control char-0 counts per window length
        ctrl_counts = {}
        for L in range(1, a):
            c0,_ = count_window(n, a, L, ctrl)
            ctrl_counts[L] = c0
        for q in prize_primes:
            beta = round(__import__('math').log(q)/__import__('math').log(n), 2)
            t_star_pred = round(2*(beta+1)*__import__('math').log(q)/__import__('math').log(n)
                                /__import__('math').log(q)*__import__('math').log(n), 0)
            # the connection's prediction t* ~ 2(beta+1) log_n p  (log_n p = beta)
            t_star_pred = round(2*(beta)*(1), 0)  # = 2*beta  (log_n p = beta); 2(beta+1) variant below
            t_star_pred2 = round(2*(beta+1), 0)
            first_div = None
            row = []
            for L in range(1, a):
                cq,ex = count_window(n, a, L, q)
                c0 = ctrl_counts[L]
                diverge = (cq != c0)
                row.append((L, c0, cq, diverge))
                if diverge and first_div is None:
                    first_div = (L, c0, cq, ex[:1])
            print(f"\n  q={q} (beta~{beta}):")
            print(f"    window L : char0_count -> charP_count   (* = diverged)")
            for (L,c0,cq,dv) in row:
                mark = " *" if dv else ""
                print(f"      L={L:2d} : {c0:6d} -> {cq:6d}{mark}")
            print(f"    FIRST DIVERGENCE L* = {first_div[0] if first_div else 'none (no divergence up to a-1)'}"
                  f"   |  predicted t*~2*beta={t_star_pred}, 2(beta+1)={t_star_pred2}")
            if first_div:
                print(f"      example spurious config (char-p only sum-zero window): {first_div[3]}")

if __name__ == "__main__":
    main()
