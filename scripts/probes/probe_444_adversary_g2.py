#!/usr/bin/env python3
"""
probe_444_adversary_g2.py  (#444 SEAM A -- ADVERSARIAL refutation of conjecture G2)

CONJECTURE G2 (to refute):
  For explicit 2-power RS codes (domain mu_n, n=2^mu, prize-shaped prime p~n^4, index>=2),
  the worst-case WINDOW LIST size L*(n,rho,eta) -- the max over ALL received words u of the
  number of distinct deg<k polys agreeing with u on >= s=round((rho+eta)n) points -- is
  BOUNDED (constant) in n, AND is achieved by a LOW-WEIGHT word (weight <= 2, i.e. x^a+x^b).

ATTACK (this file):
  At n=16 (rho=1/8 k=2; rho=1/16 k=1) and n=32 (rho=1/16 k=2; rho=1/32 k=1), >=2 prize primes:
    1. weight-2 FULL scan (baseline best L and exps), ones + random coeffs.
    2. weight-3 FULL scan (ones), + sampled random coeffs.
    3. weight-4 SAMPLED scan (ones + random).
    4. ADVERSARIAL constructions:
        (a) words supported near exponent n/4 (maximize single-fibre term
            B=#{y in mu_N : (F-u_e)^2 = y (G-u_o)^2}),
        (b) words = restriction of a high-degree poly chosen with many mu_n-roots-of-difference,
        (c) word = fixed deg<k codeword + sparse high-exponent perturbation.
    5. n-GROWTH check: does any word at n=32 beat the best at n=16 (same rate family)?

  Refute G2 if ANY higher-weight (3,4) or adversarial word gives STRICTLY larger window list
  than the best weight-2 word at the same (n,rho), OR if L* grows from n=16 to n=32.

Decoder logic copied verbatim from probe_444_higher_weight_refuter.py /
probe_444_worstword_exponent.py: find_window_prime, subgroup, poly_mul, interp_coeffs,
peval, list_RS, word_vals, is_correlated.  Exact arithmetic mod p, proper subgroup,
window s=round((rho+eta)n) with eta=rho clamped s>=k,<=n, exclude correlated dirs {0,n/2}.
"""
import itertools, random
from math import comb
from sympy import isprime, primitive_root


# ----------------------- VERBATIM DECODER SUBSTRATE -----------------------
def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta)
    base = target - (target % n) + 1
    p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n


def subgroup(n, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)
    elts, x = [], 1
    for _ in range(n):
        elts.append(x); x = (x * zeta) % p
    assert len(set(elts)) == n, "subgroup degenerate"
    return elts


def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r


def interp_coeffs(xs, ys, p):
    k = len(xs); c = [0] * k
    for i in range(k):
        num = [1]; den = 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p); sc = (ys[i] * inv) % p
        for t in range(len(num)): c[t] = (c[t] + sc * num[t]) % p
    return tuple(c)


def peval(c, x, p):
    r = 0
    for a in reversed(c): r = (r * x + a) % p
    return r


def list_RS(uvals, elts, k, s, p):
    """# distinct deg<k polys agreeing with u on >= s pts of mu_n (exact full enumeration)."""
    n = len(elts); seen = set()
    for T in itertools.combinations(range(n), k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen: continue
        ag = sum(1 for i in range(n) if peval(c, elts[i], p) == uvals[i])
        if ag >= s: seen.add(c)
    return len(seen)


def word_vals(elts, exps, coeffs, p):
    return [sum(coeffs[t] * pow(x, exps[t], p) for t in range(len(exps))) % p for x in elts]


def is_correlated(exps, n):
    """exclude correlated-direction words: exponent SET reduced mod n lies entirely in {0,n/2}."""
    h = n // 2
    return all((e % n) in (0, h) for e in exps)


# ----------------------- ATTACK DRIVERS -----------------------
COEFF_RANDOM_COUNT = 4  # random coeff vectors per exponent tuple


def window_s(n, k, eta):
    rho = k / n
    s = round((rho + eta) * n)
    return max(min(s, n), k)


def scan_weight_full_ones(n, k, s, p, elts, weight):
    """Full exponent scan, all-ones coeffs. Returns (bestL, best_exps)."""
    best = (-1, None)
    for exps in itertools.combinations(range(1, n), weight):
        if is_correlated(exps, n):
            continue
        uv = word_vals(elts, exps, (1,) * weight, p)
        L = list_RS(uv, elts, k, s, p)
        if L > best[0]:
            best = (L, exps)
    return best


def scan_weight_sampled(n, k, s, p, elts, weight, n_samples, with_random, seed):
    """Sampled exponent tuples; ones + optional random coeffs. Returns (bestL, best_exps, best_coeffs)."""
    rng = random.Random(seed)
    all_exps = list(itertools.combinations(range(1, n), weight))
    all_exps = [e for e in all_exps if not is_correlated(e, n)]
    samp = all_exps if len(all_exps) <= n_samples else rng.sample(all_exps, n_samples)
    best = (-1, None, None)
    for exps in samp:
        uv = word_vals(elts, exps, (1,) * weight, p)
        L = list_RS(uv, elts, k, s, p)
        if L > best[0]:
            best = (L, exps, (1,) * weight)
        if with_random:
            for _ in range(COEFF_RANDOM_COUNT):
                coeffs = tuple(rng.randrange(1, p) for _ in range(weight))
                uv = word_vals(elts, exps, coeffs, p)
                L = list_RS(uv, elts, k, s, p)
                if L > best[0]:
                    best = (L, exps, coeffs)
    return best


def adv_near_quarter(n, k, s, p, elts, seed):
    """Adversarial: words supported near exponent n/4 to inflate the single-fibre term.
       Build weight-2,3,4 words with all exponents clustered in [n/4 - w, n/4 + w]."""
    rng = random.Random(seed)
    q = n // 4
    half = max(2, n // 8)
    band = [e for e in range(max(1, q - half), min(n, q + half + 1)) if (e % n) not in (0, n // 2)]
    best = (-1, None, None)
    for weight in (2, 3, 4):
        if len(band) < weight:
            continue
        combos = list(itertools.combinations(band, weight))
        rng.shuffle(combos)
        for exps in combos[:200]:
            for coeffs in [(1,) * weight] + [tuple(rng.randrange(1, p) for _ in range(weight)) for _ in range(2)]:
                uv = word_vals(elts, exps, coeffs, p)
                L = list_RS(uv, elts, k, s, p)
                if L > best[0]:
                    best = (L, exps, coeffs)
    return best


def adv_many_root_diff(n, k, s, p, elts, seed):
    """Adversarial: word = restriction of a high-degree poly designed so that (word - codeword)
       has many roots on mu_n for several codewords simultaneously. We take products of
       (x^a - x^b) style factors evaluated on mu_n -- words with structured low Fourier support
       that align with multiple k-subsets. Implemented as: random sparse high-degree polys
       (weight up to 5, exponents drawn from the full range incl. high ones), keep worst."""
    rng = random.Random(seed)
    best = (-1, None, None)
    for _ in range(400):
        weight = rng.randint(2, 5)
        exps = tuple(sorted(rng.sample(range(1, n), weight)))
        if is_correlated(exps, n):
            continue
        coeffs = tuple(rng.randrange(1, p) for _ in range(weight))
        uv = word_vals(elts, exps, coeffs, p)
        L = list_RS(uv, elts, k, s, p)
        if L > best[0]:
            best = (L, exps, coeffs)
    return best


def adv_codeword_plus_perturb(n, k, s, p, elts, seed):
    """Adversarial: word = fixed deg<k codeword f(x) + sparse high-exponent perturbation c*x^e.
       This sits a true codeword at full agreement, then a perturbation may spawn extra near
       codewords. Scan f over random low-deg polys, perturbations over single/double monomials."""
    rng = random.Random(seed)
    best = (-1, None, None)
    for _ in range(300):
        # random codeword f, deg < k
        fc = tuple(rng.randrange(0, p) for _ in range(k))
        base = [peval(fc, x, p) for x in elts]
        # perturbation: 1 or 2 monomials at exponents >= k (so not absorbed into the codeword space)
        pw = rng.randint(1, 2)
        pexps = tuple(sorted(rng.sample(range(k, n), pw)))
        if is_correlated(pexps, n):
            continue
        pcoeffs = tuple(rng.randrange(1, p) for _ in range(pw))
        uv = [(base[i] + sum(pcoeffs[t] * pow(elts[i], pexps[t], p) for t in range(pw))) % p
              for i in range(n)]
        L = list_RS(uv, elts, k, s, p)
        if L > best[0]:
            best = (L, ("codeword", fc, "perturb", pexps, pcoeffs), pcoeffs)
    return best


# ----------------------- ORCHESTRATION -----------------------
def run():
    # (n, k, eta=rho, label).  eta=rho per dossier midpoint -> s=2k.
    configs = [
        (16, 2, 0.125,   "n16_rho1/8 (k=2)"),
        (16, 1, 0.0625,  "n16_rho1/16 (k=1)"),
        (32, 2, 0.0625,  "n32_rho1/16 (k=2)"),
        (32, 1, 0.03125, "n32_rho1/32 (k=1)"),
    ]
    primes_betas = [4.0, 4.4]  # two structurally distinct prize-shaped primes

    # accumulate worst-L per (rate-family) to do the n-growth comparison
    summary = {}  # label -> dict
    family_best = {}  # rate-family key -> {n: worstL}

    for (n, k, eta, label) in configs:
        s = window_s(n, k, eta)
        rho = k / n
        family = f"k={k}_eta=rho"  # k=1 and k=2 families; compare same k across n
        print(f"\n########## {label}: n={n} k={k} rho={rho:.5f} eta={eta} s={s} ##########")
        print(f"  C(n,k)={comb(n,k)} k-subsets per word")

        primes = []
        for pb in primes_betas:
            pp = find_window_prime(n, pb)
            if pp not in primes:
                primes.append(pp)

        overall_w2 = -1
        overall_best_any = (-1, None, None, None)  # (L, source, exps, prime)

        for p in primes:
            elts = subgroup(n, p)
            print(f"  --- prime p={p} (index m=(p-1)/n={(p-1)//n}) ---")

            # weight 2 full (ones)
            L2, e2 = scan_weight_full_ones(n, k, s, p, elts, 2)
            print(f"    weight-2 FULL ones        : L={L2} exps={e2}")
            # weight 2 random coeffs (sampled exps, with random)
            b2r = scan_weight_sampled(n, k, s, p, elts, 2, 10**9, True, seed=11 + p % 97)
            print(f"    weight-2 ones+random      : L={b2r[0]} exps={b2r[1]} coeffs={'ones' if b2r[2]==(1,1) else b2r[2]}")
            w2 = max(L2, b2r[0])
            overall_w2 = max(overall_w2, w2)

            # weight 3 full ones
            L3, e3 = scan_weight_full_ones(n, k, s, p, elts, 3)
            print(f"    weight-3 FULL ones        : L={L3} exps={e3}")
            # weight 3 sampled random
            b3r = scan_weight_sampled(n, k, s, p, elts, 3, 120, True, seed=23 + p % 89)
            print(f"    weight-3 sampled+random   : L={b3r[0]} exps={b3r[1]}")

            # weight 4 sampled ones+random
            b4 = scan_weight_sampled(n, k, s, p, elts, 4, 160, True, seed=31 + p % 83)
            print(f"    weight-4 sampled ones+rand: L={b4[0]} exps={b4[1]}")

            # adversarial constructions
            aq = adv_near_quarter(n, k, s, p, elts, seed=41 + p % 71)
            print(f"    adv near-n/4 cluster      : L={aq[0]} exps={aq[1]}")
            amr = adv_many_root_diff(n, k, s, p, elts, seed=53 + p % 67)
            print(f"    adv many-root-diff (rand) : L={amr[0]} exps={amr[1]}")
            acp = adv_codeword_plus_perturb(n, k, s, p, elts, seed=67 + p % 61)
            print(f"    adv codeword+perturb      : L={acp[0]} perturb_exps={acp[1][3] if acp[1] else None}")

            # track best of ALL methods for this prime
            for (L, src, exps) in [
                (L2, "w2", e2), (b2r[0], "w2r", b2r[1]),
                (L3, "w3", e3), (b3r[0], "w3r", b3r[1]),
                (b4[0], "w4", b4[1]),
                (aq[0], "adv_q", aq[1]), (amr[0], "adv_root", amr[1]),
                (acp[0], "adv_cwp", acp[1]),
            ]:
                if L > overall_best_any[0]:
                    overall_best_any = (L, src, exps, p)

        verdict = ("HIGHER-WEIGHT/ADV BEATS w2" if overall_best_any[0] > overall_w2
                   else "weight-2 is worst (tie or strictly best)")
        print(f"  >>> best weight-2 L = {overall_w2}")
        print(f"  >>> best ANY-method L = {overall_best_any[0]} via {overall_best_any[1]} "
              f"exps={overall_best_any[2]} p={overall_best_any[3]}")
        print(f"  >>> {verdict}")

        summary[label] = {
            "n": n, "k": k, "s": s, "rho": rho,
            "best_w2": overall_w2, "best_any": overall_best_any,
            "higher_beats": overall_best_any[0] > overall_w2,
        }
        family_best.setdefault(family, {})[n] = max(
            family_best.get(family, {}).get(n, -1), overall_best_any[0])

    # ----------------------- FINAL VERDICT -----------------------
    print("\n\n==================== FINAL G2 VERDICT ====================")
    print(f"{'config':<22} {'best_w2':>8} {'best_any':>9} {'higher_beats?':>14}")
    any_higher = False
    for label, d in summary.items():
        hb = d["higher_beats"]
        any_higher = any_higher or hb
        print(f"{label:<22} {d['best_w2']:>8} {d['best_any'][0]:>9} {str(hb):>14}")

    print("\nn-GROWTH check (same k family, best ANY-method L):")
    growth = False
    for family, byn in sorted(family_best.items()):
        ns = sorted(byn)
        seq = " -> ".join(f"n={nn}:L={byn[nn]}" for nn in ns)
        grew = len(ns) >= 2 and byn[ns[-1]] > byn[ns[0]]
        growth = growth or grew
        print(f"  {family}: {seq}   {'GROWS' if grew else 'flat/shrinks'}")

    print("\n---------------------------------------------------------")
    if any_higher:
        print("VERDICT: G2 REFUTED -- a higher-weight or adversarial word strictly beats weight-2.")
        for label, d in summary.items():
            if d["higher_beats"]:
                print(f"  WITNESS @ {label}: L={d['best_any'][0]} (vs w2={d['best_w2']}) "
                      f"via {d['best_any'][1]}, exps={d['best_any'][2]}, p={d['best_any'][3]}")
    elif growth:
        print("VERDICT: G2 REFUTED (growth) -- worst-case L grows with n (not constant).")
    else:
        print("VERDICT: G2 SURVIVES -- weight-2 is the worst word at every tested (n,rho),")
        print("         and worst-case L does not grow from n=16 to n=32 in any rate family.")
    print("=========================================================")


if __name__ == "__main__":
    run()
