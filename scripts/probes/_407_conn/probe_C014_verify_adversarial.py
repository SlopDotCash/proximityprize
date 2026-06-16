"""
ADVERSARIAL re-verification of the C014 REFUTED verdict.

Independent reimplementation (NOT reusing the attacker's code) of the three claims:
  (1) the C014 'section' c -> gamma_c = -coeff_k(c) is NOT injective on the RS[k+1] list,
  (2) the section's image is NOT contained in the bad set (most listed gamma are not bad),
  (3) the reverse bound  I >= poly*|list|  collapses: worst I/|list| << 1.

Regime: GENUINELY PROPER dyadic subgroup mu_n of F_q*, n=2^mu, q prime, q=1 mod n, n^2 < q
(prize-shaped n << sqrt q). We test MULTIPLE proper-subgroup primes to rule out a single-prime
artifact, including a fresh one the attacker did NOT use.

Exact integer arithmetic. Monomial line u1 = X^k, k=1 (RS[k+1]=q^2 codewords, feasible).

For each random received word u0 (general, not a codeword) and each radius floor t:
  - I(delta)  = # bad gamma : exists witness S, |S|>=t, line u0+gamma*X^k explained by an
                RS[k] codeword on S, AND no joint pair (RS[k] cw=u0 on S) & (RS[k] cw=X^k on S).
  - |list|    = # RS[k+1] codewords agreeing with u0 on >= t coords.
  - section non-injective? two list cws share leading coeff (=> same gamma).
  - fraction of listed gamma that are actually bad.
"""

import itertools

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def proper_subgroup_prime(n, qmin, qmax):
    """smallest prime q in [qmin,qmax], q=1 mod n, q>n^2 (proper subgroup)."""
    q = qmin
    while q <= qmax:
        if q > n*n and q % n == 1 and is_prime(q):
            return q
        q += 1
    return None

def mu_n(n, q):
    def order(a):
        o, x = 1, a % q
        while x != 1:
            x = (x*a) % q; o += 1
        return o
    g = next(c for c in range(2, q) if order(c) == q-1)
    h = pow(g, (q-1)//n, q)
    out, x = [], 1
    for _ in range(n):
        out.append(x); x = (x*h) % q
    assert len(set(out)) == n
    return out

def ev(coeffs, dom, q):
    return tuple(sum(c*pow(x, j, q) for j, c in enumerate(coeffs)) % q for x in dom)

def agree(a, b):
    return sum(1 for x, y in zip(a, b) if x == y)

def run(n, q, k, trials=40, seed=7):
    import random
    rng = random.Random(seed)
    dom = mu_n(n, q)
    Xk = ev([0]*k + [1], dom, q)               # X^k eval vector (coeff_k = 1)
    rsk  = [ev(list(c), dom, q) for c in itertools.product(range(q), repeat=k)]      # RS[k]
    rsk1 = [(ev(list(c), dom, q), c[k]) for c in itertools.product(range(q), repeat=k+1)]  # RS[k+1] + coeff_k

    print(f"n={n} mu_{n}, q={q}  (q%n={q%n}, n^2={n*n}<q:{n*n<q}, proper)  k={k}")
    print(f"  {'t':>2} {'delta':>6} {'maxI':>5} {'maxList':>8} {'worstI/list':>14} "
          f"{'secNonInj':>10} {'listedG':>8} {'badG':>6} {'fracBad':>8}")
    for t in range(1, n+1):
        delta = 1 - t/n
        anyI = []; anyL = []; noninj = False; tot_g = 0; tot_bad = 0
        worst = None
        for _ in range(trials):
            u0 = tuple(rng.randrange(q) for _ in range(n))
            listed = [(e, (-ck) % q) for (e, ck) in rsk1 if agree(e, u0) >= t]
            L = len(listed)
            bad = set()
            for e, gamma in listed:
                S = [i for i in range(n) if e[i] == u0[i]]
                if len(S) < t:
                    continue
                v0_ok = any(all(c[i] == u0[i] for i in S) for c in rsk)
                v1_ok = any(all(c[i] == Xk[i] for i in S) for c in rsk)
                if not (v0_ok and v1_ok):
                    bad.add(gamma)
            I = len(bad)
            gammas = [g for (_, g) in listed]
            if len(set(gammas)) != len(gammas):
                noninj = True
            tot_g += len(set(gammas))
            tot_bad += len(set(gammas) & bad)
            anyI.append(I); anyL.append(L)
            if L > 0:
                r = I / L
                if worst is None or r < worst[2]:
                    worst = (I, L, r)
        if not anyI or max(anyL) == 0:
            continue
        fb = (tot_bad / tot_g) if tot_g else 0.0
        ws = f"{worst[0]}/{worst[1]}={worst[2]:.3f}" if worst else "-"
        print(f"  {t:>2} {delta:>6.3f} {max(anyI):>5} {max(anyL):>8} {ws:>14} "
              f"{str(noninj):>10} {tot_g:>8} {tot_bad:>6} {fb:>8.3f}")

if __name__ == "__main__":
    import sys
    # mu_8 over TWO distinct proper-subgroup primes (q=281 is FRESH, not in attacker's run)
    for q in [233, 281]:   # both = 1 mod 8, both > 64 = n^2, both prime
        assert is_prime(q) and q % 8 == 1 and q > 64
        run(8, q, 1, trials=15)
        print(); sys.stdout.flush()
