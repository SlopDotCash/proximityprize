"""
C014 probe: is the 'reverse bound' (I(delta) >= poly * |list(RS[k+1])|) the
witness-spread realizer of the super-code list?

Forward bridge (PROVEN in-tree, badScalars_monomial_card_le_listSize):
    I(delta) = #{bad gamma of line (u0, X^k) for RS[k]}  <=  |L(k+1, u0, delta)|
where L(k+1, u0, delta) = { c in RS[k+1] : c agrees with u0 on >= (1-delta)n points }.

C014 claims the REVERSE  I(delta) >= poly * |L(k+1)|  is "pinned" by the two
MCAWitnessSpread lemmas (unique_bad_gamma_common_witness + the set form), via a
"section" of the list  c -> (gamma_c = -coeff_k(c), S_c = agreement set)  whose image
must avoid the common-witness collapse.

We test, at PROPER-SUBGROUP mu_n primes (n=2^mu, n^2 << q, q ~ n^beta), with the
monomial line u1 = X^k:
  (A) the FORWARD bound  I <= |list|       (sanity; should always hold)
  (B) the REVERSE direction in the form C014 needs:
       does the list inject (sectionwise) into the bad set?  i.e. is the map
       c -> gamma_c = -coeff_k(c) (i) INJECTIVE on the list and (ii) landing in
       the bad set?  If either fails, the 'section' does not exist and I CANNOT
       be bounded below by |list|.
  (C) the true governing quantity Lambda_2(2delta) (interleaved list, doubled radius)
       and the proven ceiling  I <= 1 + 2(n-t)*Lambda_2  (O85/O89), to locate the
       reverse correctly.

We count exactly over the field, enumerating RS codewords by polynomial coeffs.
We keep k small so RS[k] / RS[k+1] enumeration is q^k / q^{k+1} (feasible for small q).
"""

import itertools, sys

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def find_subgroup_prime(n, beta_lo, beta_hi):
    """Find prime q ~ n^beta with q = 1 mod n, n^2 << q (proper subgroup)."""
    import math
    target_lo = max(int(n**beta_lo), n*n + 1)   # enforce proper subgroup n^2 < q
    target_hi = int(n**beta_hi)
    q = target_lo - (target_lo % n) + 1
    if q <= target_lo:
        q += n
    while q <= target_hi:
        if q > n*n and is_prime(q):
            return q
        q += n
    return None

def subgroup_mu(n, q):
    """The order-n multiplicative subgroup mu_n of F_q* (q = 1 mod n)."""
    # find a generator g of F_q*, then mu_n = g^{(q-1)/n} powers
    # brute force a primitive root
    def order(a):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
        return o
    g = None
    for cand in range(2, q):
        if order(cand) == q-1:
            g = cand; break
    h = pow(g, (q-1)//n, q)  # element of order n
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x); x = (x*h) % q
    assert len(set(mu)) == n
    return mu

def poly_eval(coeffs, x, q):
    """Evaluate poly with given coeff list (low->high) at x mod q."""
    acc = 0
    p = 1
    for c in coeffs:
        acc = (acc + c*p) % q
        p = (p*x) % q
    return acc

def evals(coeffs, domain, q):
    return tuple(poly_eval(coeffs, x, q) for x in domain)

def agreement(a, b):
    return sum(1 for x,y in zip(a,b) if x==y)

def run(n, q, k, beta_label, max_u0=200, seed=12345):
    import random
    rng = random.Random(seed)
    domain = subgroup_mu(n, q)
    assert len(domain) == n
    # codeword list of RS[k]   (deg < k):  enumerate all q^k polys
    # codeword list of RS[k+1] (deg < k+1): enumerate all q^{k+1} polys
    # we only need EVALUATION vectors; index by them.
    # X^k evaluation vector (the monomial far direction)
    Xk = evals([0]*k + [1], domain, q)  # poly X^k has coeff_k = 1

    # Precompute RS[k+1] eval vectors with their X^k coefficient (= coeffs[k]).
    rsk1 = []  # list of (evalvec, coeff_k)
    for coeffs in itertools.product(range(q), repeat=k+1):
        ev = evals(list(coeffs), domain, q)
        rsk1.append((ev, coeffs[k]))
    # RS[k] eval vectors (for joint-pair / pairJointAgreesOn tests)
    rsk = [evals(list(coeffs), domain, q) for coeffs in itertools.product(range(q), repeat=k)]
    rsk_set = set(rsk)

    # choose threshold t (witness floor) = ceil((1-delta) n); we sweep deltas via t.
    results = []
    for t in range(1, n+1):
        delta = 1 - t/n
        # ------- I(delta): exact bad-scalar count for line (u0, X^k) over RS[k] -------
        # mcaEvent(gamma): exists S, |S|>=t, exists w in RS[k] with w = u0 + gamma*Xk on S,
        #                  AND NO joint pair (v0,v1) in RS[k]^2 with v0=u0, v1=Xk on S.
        # For a fixed u0 and gamma:
        #   line point  L_gamma(x) = u0(x) + gamma*Xk(x).
        #   gamma is "explainable" if some RS[k] codeword agrees with L_gamma on >= t pts;
        #   the witness set is the agreement set. By the bridge, this equals:
        #   exists q' in RS[k+1] with coeff_k = -gamma agreeing with u0 on >= t pts.
        #   gamma is BAD if additionally that witness set S carries NO joint pair.
        #
        # We compute, per random u0, the exact bad set and the RS[k+1] list.
        agg_I = []
        agg_list = []
        agg_lambda2 = []
        agg_section_inj = []   # is c->gamma injective on list?
        agg_section_into_bad = []  # fraction of list whose gamma is bad
        ntrials = min(max_u0, 25 if k>=2 else 60)
        for _ in range(ntrials):
            # random u0 NOT necessarily a codeword (general received word over the domain)
            u0 = tuple(rng.randrange(q) for _ in range(n))
            # list of RS[k+1] codewords agreeing with u0 on >= t points, with their gamma=-coeff_k
            listed = []
            for ev, ck in rsk1:
                if agreement(ev, u0) >= t:
                    listed.append((ev, (-ck) % q))
            list_size = len(listed)
            # bad gamma set: gamma is bad iff exists witness S (|S|>=t) on which
            # (u0,Xk) is line-explained for gamma but no joint pair.
            # By bridge: gamma explainable <=> some RS[k+1] poly q' with coeff_k=-gamma
            # agrees with u0 on >=t pts.  The witness S = that agreement set.
            # gamma BAD <=> exists such S with NO joint pair (v0=u0 & v1=Xk on S).
            # joint pair on S exists iff (some RS[k] cw = u0 on S) AND (some RS[k] cw = Xk on S).
            # Xk in RS[k+1]\RS[k] (deg exactly k), so "RS[k] cw = Xk on S" means some deg<k poly
            # interpolates Xk on S.  Compute per candidate S.
            bad = set()
            badgammas_via_section = set()
            for ev, gamma in listed:
                # witness set S = agreement(ev,u0) positions
                S = tuple(i for i in range(n) if ev[i]==u0[i])
                if len(S) < t:
                    continue
                # joint pair on S?  need v0 in RS[k] with v0=u0 on S  AND v1 in RS[k] with v1=Xk on S
                v0_ok = any(all(c[i]==u0[i] for i in S) for c in rsk)
                v1_ok = any(all(c[i]==Xk[i] for i in S) for c in rsk)
                joint = v0_ok and v1_ok
                if not joint:
                    bad.add(gamma)
                # the C014 "section" sends EVERY list element to its gamma regardless
                badgammas_via_section.add(gamma)
            I = len(bad)
            # interleaved list Lambda_2 at doubled radius (joint floor a = 2t-n):
            a = 2*t - n
            lam2 = 0
            if a >= 1:
                # pairs (g1,g2) in RS[k]^2 jointly agreeing with (u0, Xk) on >= a points
                # to keep it cheap, count distinct joint-agreement >= a
                for c1 in rsk:
                    s1 = set(i for i in range(n) if c1[i]==u0[i])
                    if len(s1) < a:
                        continue
                    for c2 in rsk:
                        joint_set = sum(1 for i in s1 if c2[i]==Xk[i])
                        if joint_set >= a:
                            lam2 += 1
            agg_I.append(I)
            agg_list.append(list_size)
            agg_lambda2.append(lam2)
            # section injective on list? distinct list elements with same gamma => not injective
            gammas = [g for (_,g) in listed]
            inj = (len(set(gammas)) == len(gammas))
            agg_section_inj.append(inj)
            into_bad = (len(set(gammas) & bad), len(set(gammas)))
            agg_section_into_bad.append(into_bad)
        if not agg_I:
            continue
        maxI = max(agg_I); maxlist = max(agg_list)
        # reverse-bound violation: list large but I small at SAME stack
        worst_ratio = 0.0
        worst = None
        for I,L in zip(agg_I, agg_list):
            if L > 0:
                r = I / L
                if worst is None or r < worst_ratio:
                    worst_ratio = r; worst = (I,L)
        any_noninj = any(not b for b in agg_section_inj)
        # how often does a listed gamma FAIL to be bad?
        tot_listed_g = sum(b for (_,b) in agg_section_into_bad)
        tot_bad_among = sum(a_ for (a_,_) in agg_section_into_bad)
        results.append({
            't': t, 'delta': round(delta,3),
            'maxI': maxI, 'maxlist': maxlist,
            'maxlambda2': max(agg_lambda2),
            'worst_I_over_list': (worst, round(worst_ratio,3)) if worst else None,
            'section_ever_noninjective': any_noninj,
            'listed_gammas_total': tot_listed_g,
            'of_which_bad': tot_bad_among,
        })
    return domain, results

if __name__ == "__main__":
    import sys
    configs = [
        # (n, beta_lo, beta_hi, k) -- GENUINELY proper subgroup: n^2 << q (n < sqrt(q))
        (8, 2.6, 3.2, 1),   # mu_8, q ~ n^2.7 ~ 250..500, n^2=64 << q : k=1, RS[k+1]=q^2 feasible
        (8, 3.0, 3.6, 1),   # mu_8, q ~ n^3 ~ 512.. : deeper proper subgroup
    ]
    if "--heavy" in sys.argv:
        configs += [
            (16,2.4, 2.7, 1),   # mu_16, q ~ 16^2.5 ~ 1024.., n^2=256 << q
            (8, 2.05,2.3, 2),   # mu_8 k=2, q just above n^2 (proper, RS[k+1]=q^3 < 3M)
        ]
    for (n, blo, bhi, k) in configs:
        q = find_subgroup_prime(n, blo, bhi)
        if q is None:
            print(f"no prime for n={n} beta in [{blo},{bhi}]"); continue
        # proper-subgroup sanity: n < sqrt(q)?  n^2 < q
        proper = (n*n < q)
        print(f"\n=== n={n} (mu_{n}), q={q} (q=1 mod n: {q%n==1}), n^2<q: {proper}, k={k}, "
              f"RS[k+1] enum size q^(k+1)={q**(k+1)} ===")
        if q**(k+1) > 3_000_000:
            print(f"  (skipping: RS[k+1] enumeration too large = {q**(k+1)})")
            continue
        domain, res = run(n, q, k, f"beta~2")
        print(f"  mu_{n} = {domain}")
        print(f"  {'t':>2} {'delta':>6} {'maxI':>5} {'maxList':>8} {'maxLam2':>8} "
              f"{'worst I/list':>20} {'sec_noninj':>10} {'listedG':>8} {'ofWhichBad':>10}")
        for r in res:
            print(f"  {r['t']:>2} {r['delta']:>6} {r['maxI']:>5} {r['maxlist']:>8} "
                  f"{r['maxlambda2']:>8} {str(r['worst_I_over_list']):>20} "
                  f"{str(r['section_ever_noninjective']):>10} "
                  f"{r['listed_gammas_total']:>8} {r['of_which_bad']:>10}")
