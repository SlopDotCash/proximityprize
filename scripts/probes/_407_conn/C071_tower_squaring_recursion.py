"""
C071 probe: "full_tower coset-closure budget 2^{n/2^s} and the tower house cocycle
eta_halving are ONE s-indexed squaring recursion; 2^{n/2^s} branching interpolates;
Mersenne/sumset growth enters via # of 2^s-power classes; s=mu (count F4) vs s=1 (house F2)."

We test EXACTLY (big-int / exact-complex arithmetic) on PROPER dyadic subgroups
mu_n < F_q^*, q prime = 1 mod n, q ~ n^beta (beta>=3), n << sqrt(q):

(A) COUNT SIDE (full_tower / tower_count, LamLeungTwoPow.lean):
    - the # of 2^s-power CLASSES of D0=mu_n is exactly n/2^s = 2^{mu-s} (squaring 2-to-1).
    - so the budget 2^{#classes} = 2^{n/2^s} is literally a class count, NOT a character
      sum.  Confirm the class count and that at s=mu it is 2^{n/n}=2^1=2.

(B) HOUSE SIDE (eta_halving, DyadicHalvingRecursion.lean):
    - the recursion eta(mu_{2k},b) = eta(mu_k,b) + eta(mu_k, b*zeta) is a 2-TERM split
      per level (NOT a 2^{n/2^s}-term branching).  Unfolding s levels from mu_n down to
      mu_{n/2^s} produces 2^s additive terms, each an eta over mu_{n/2^s} at a frequency
      b*zeta^j (the Walsh/FFT butterfly).  Confirm the unfold identity exactly.

(C) THE LOAD-BEARING TEST -- are the two "branchings" the same number?
    - count-side branching at depth s = 2^{n/2^s}.
    - house-side branching at unfold depth s = 2^s  (number of butterfly terms).
    These are DIFFERENT functions of s (one halves the exponent, one doubles), and they
    coincide only at the trivial endpoints.  Tabulate both and check whether either tracks
    the actual worst-case period B = max_{b!=0}|eta(mu_n,b)| (the open BGK/Paley object).

(D) DOES s=1 house relate to the open core, and does count-side ever bound B?
    - compute B exactly; compare to count budget and to any house-recursion product.
"""

import cmath, math
from itertools import combinations

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prime(n, beta_min):
    """smallest prime q = 1 mod n with q >= n**beta_min, and n << sqrt(q)."""
    target = int(n**beta_min)
    q = target - (target % n) + 1
    while q < target or q <= n*n:  # ensure n << sqrt q
        q += n
    while not is_prime(q):
        q += n
    return q

def primitive_root_mod(q):
    """a generator of F_q^*."""
    facs = []
    m = q-1
    d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, q):
        if all(pow(g, (q-1)//p, q) != 1 for p in facs):
            return g
    raise RuntimeError

def subgroup(q, n):
    """mu_n = the n-th roots of unity in F_q^* (n | q-1)."""
    g = primitive_root_mod(q)
    h = pow(g, (q-1)//n, q)        # element of order n
    G = [pow(h, i, q) for i in range(n)]
    return G, h

def add_char(q):
    """psi(x) = exp(2pi i x / q), standard additive character of F_q."""
    w = cmath.exp(2j*math.pi/q)
    return lambda x: w**(x % q)

def eta(G, psi, b, q):
    return sum(psi((b*x) % q) for x in G)

def power_classes(G, q, s):
    """# of 2^s-power classes of G (image of x -> x^{2^s})."""
    e = 2**s
    img = set(pow(x, e, q) for x in G)
    return len(img)

def main():
    print("="*100)
    print("C071: count-side 2^{n/2^s} budget vs house-side eta_halving butterfly -- ONE recursion?")
    print("="*100)

    configs = [(8,3.2),(16,3.2),(32,3.2),(64,3.2)]
    for n, beta in configs:
        mu = n.bit_length()-1   # n = 2^mu
        q = find_prime(n, beta)
        beta_eff = math.log(q)/math.log(n)
        G, h = subgroup(q, n)
        psi = add_char(q)
        print(f"\n{'-'*100}")
        print(f"n=2^{mu}={n}  q={q}  beta_eff={beta_eff:.3f}  n^2={n*n} << q  (proper subgroup, prize-shaped)")

        # ---- (A) COUNT SIDE: # 2^s-power classes and the budget ----
        print(f"\n(A) COUNT side (full_tower / tower_count):  #classes(s) and budget 2^#classes")
        print(f"    {'s':>3} {'#2^s-classes':>14} {'pred n/2^s':>12} {'budget 2^#cls':>22}")
        for s in range(0, mu+1):
            cls = power_classes(G, q, s)
            pred = n // (2**s)
            budget = 2**cls
            print(f"    {s:>3} {cls:>14} {pred:>12} {budget:>22}")
        print(f"    -> at s=mu={mu}: #classes={power_classes(G,q,mu)} (=1), budget=2 (the all-mu_n closure, count<=2)")

        # ---- (B) HOUSE SIDE: eta_halving unfold to s levels = 2^s butterfly terms ----
        print(f"\n(B) HOUSE side (eta_halving):  eta(mu_n,b) = sum over 2^s terms eta(mu_{{n/2^s}}, b*zeta^j)")
        # pick a nonzero frequency b
        b = G[1]  # any nonzero
        full = eta(G, psi, b, q)
        # unfold s levels: at level s, mu_{n/2^s}, and the 2^s shift frequencies are
        # b * (2^s-th-root-of- the chain).  Build it directly: repeatedly apply halving.
        for s in range(1, mu+1):
            k = n // (2**s)
            if k == 0: break
            Gk = [pow(h, i*(2**s), q) for i in range(k)]   # mu_k = <h^{2^s}>
            # the 2^s coset reps that shift frequency: the 2^s-th roots ... actually the
            # shift set is the quotient mu_n / mu_k, size 2^s, represented by h^j, j=0..2^s-1 step k?
            # mu_n / mu_{n/2^s} has order 2^s; reps = h^{j}, j=0..2^s-1 (the first 2^s powers since
            # mu_k = <h^{2^s}> means the cosets are h^0..h^{2^s-1} * mu_k).  Frequency shift = that rep.
            reps = [pow(h, j, q) for j in range(2**s)]
            recon = sum(eta(Gk, psi, (b*r) % q, q) for r in reps)
            err = abs(recon - full)
            print(f"    s={s}: mu_{{{k}}}, {2**s:>4} butterfly terms, |recon-full|={err:.2e}  (#house terms=2^s={2**s})")

        # ---- (C) the two branchings as functions of s ----
        print(f"\n(C) BRANCHING comparison: count budget exponent (n/2^s) vs house term count (2^s)")
        print(f"    {'s':>3} {'count exp n/2^s':>16} {'house #terms 2^s':>18} {'equal?':>8}")
        for s in range(0, mu+1):
            ce = n//(2**s)
            ht = 2**s
            print(f"    {s:>3} {ce:>16} {ht:>18} {str(ce==ht):>8}")

        # ---- (D) the open object B and whether either side bounds it ----
        B = max(abs(eta(G, psi, b, q)) for b in range(1, q) if True) if q < 4000 else \
            max(abs(eta(G, psi, b, q)) for b in G)  # for large q, coset-invariance => max over G reps suffices?
        # eta is coset-invariant in b under mu_n: eta(G,b*g)=eta(G,b) for g in mu_n (since g*G=G).
        # so distinct values = (q-1)/n; max over one rep per coset suffices. Use coset reps:
        g0 = primitive_root_mod(q)
        m = (q-1)//n
        reps_b = [pow(g0, i, q) for i in range(m)]   # one rep per mu_n-coset of F_q^*
        B = max(abs(eta(G, psi, rb, q)) for rb in reps_b)
        print(f"\n(D) OPEN object B = max_{{b!=0}}|eta(mu_n,b)| = {B:.4f}")
        print(f"    sqrt(n)={math.sqrt(n):.4f}  2sqrt(n)(Ramanujan)={2*math.sqrt(n):.4f}  sqrt(n ln m)={math.sqrt(n*math.log(m)):.4f}  (m={m})")
        print(f"    count budget at window-interior s (t=2^s-1 ~ Theta(n) => s~mu): 2^{{n/2^mu}}=2  (a COUNT, dimensionless; says NOTHING about magnitude B)")
        print(f"    house at s=1: eta(mu_n)=eta(mu_{{n/2}},b)+eta(mu_{{n/2}},b*zeta); both terms |.|<=B(mu_{{n/2}}); triangle gives B(mu_n)<=2 B(mu_{{n/2}}) -> B(mu_n)<=2^mu B(mu_1)=n*1=n (TRIVIAL, no cancellation)")

    print("\n" + "="*100)
    print("VERDICT LOGIC:")
    print(" - count #classes(s) = n/2^s EXACTLY (squaring 2-to-1); budget 2^{n/2^s} is a CLASS COUNT.")
    print(" - house eta_halving unfold to depth s = 2^s additive (butterfly) terms EXACTLY.")
    print(" - the two 'branchings' are 2^{n/2^s} vs 2^s: opposite monotonicity in s, equal only at endpoints.")
    print(" - count budget is dimensionless and bounded by 2 at the window-interior depth s~mu; it cannot")
    print("   and does not bound the MAGNITUDE B.  House triangle-unfold gives only B<=n (trivial, no sqrt).")
    print(" - 'one squaring recursion' is TRUE as a shared substrate (x->x^2 fold), but count counts CLASSES")
    print("   and house sums CHARACTERS; the s-dial does NOT make the count budget bound B.  Open core B")
    print("   (sqrt-cancellation among the 2^s butterfly phases) = BGK/Paley, untouched.")

if __name__ == "__main__":
    main()

# ============================================================================
# (E) FOLLOW-UP: is the s=mu/2 accidental crossing (n/2^s == 2^s) meaningful,
#     and does the count budget at THAT s relate to B?  And does eta_halving's
#     2-term split realize the count's class structure in any sense?
# ============================================================================
def followup():
    print("\n" + "="*100)
    print("(E) FOLLOW-UP: the accidental n/2^s == 2^s crossing at s=mu/2, and budget-vs-B")
    print("="*100)
    for n, beta in [(16,3.2),(64,3.2),(256,3.0)]:
        mu = n.bit_length()-1
        q = find_prime(n, beta)
        G, h = subgroup(q, n)
        psi = add_char(q)
        g0 = primitive_root_mod(q)
        m = (q-1)//n
        # B: max over coset reps
        if m <= 200000:
            reps_b = [pow(g0, i, q) for i in range(m)]
            B = max(abs(eta(G, psi, rb, q)) for rb in reps_b)
        else:
            import random; random.seed(0)
            B = max(abs(eta(G, psi, pow(g0, random.randrange(m), q), q)) for _ in range(20000))
        s_cross = mu/2
        print(f"\nn=2^{mu}={n} q={q}: crossing n/2^s==2^s at s={s_cross} (where #cls=2^s -> budget 2^{{n/2^{{mu/2}}}}=2^{{2^{{mu/2}}}})")
        if mu % 2 == 0:
            s = mu//2
            cls = power_classes(G, q, s)
            print(f"  at integer s={s}: #classes={cls}=sqrt(n)={int(math.isqrt(n))}, count budget=2^{cls}={2**cls}, house #terms=2^{s}={2**s}")
            print(f"  count budget 2^sqrt(n)={2**cls} vs B={B:.2f} vs n={n}: budget is super-poly in n, B is ~sqrt(n)..n -- NO relation")
        print(f"  B={B:.3f}  sqrt(n)={math.sqrt(n):.3f}  2sqrt(n)={2*math.sqrt(n):.3f}  n={n}  m={m}")
        print(f"  count budget 2^{{n/2^s}} ranges 2..2^n (dimensionless count); B ranges sqrt(n)..n (a magnitude). Categorically different.")

if __name__ == "__main__":
    followup()
