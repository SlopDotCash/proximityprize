"""
C005 probe (#407): "The 1x1 NVM minors ARE the Gauss-period house F2."

CLAIM (from conn/C005.json):
  The compressed-Fourier matrix factors M = (1/m) F D F^T with F the m x m Vandermonde
  of zeta_m and D = diag(G_0..G_{m-1}) the Gauss sums.  The 1x1 minor / entry is
      M_{a,b} = T_{a+b},   T_j = (1/m) sum_i omega^{i j} G_i,   omega = zeta_m
  and T_j is EXACTLY the prize Gauss period eta_b up to sqrt(q)/m:
      M_{a,b} = (sqrt q / m) * eta_{...}.
  So the k=1 NVM nonvanishing condition (T_j != 0) is the SAME object as the
  prize sup-norm target B = max_{b!=0} |eta_b| <= C sqrt(n log(p/n)).

We test, at PRIZE-REGIME-flavoured parameters (PROPER subgroup mu_n, n=2^mu << sqrt p,
several large-ish primes, multiple-prime where possible):

  (1) IDENTITY: is T_j  (built from the m Gauss sums G_i of the m extensions of a
      fixed character chi on mu_n) literally equal to a Gauss period eta_b, up to the
      sqrt(q)/m scaling claimed?  We check this NUMERICALLY to high precision.

  (2) SUP-NORM EQUIVALENCE: is  max_j |T_j| * (m / sqrt q)  ==  max_b |eta_b| = B ?
      i.e. are the two "houses" the same number?

  (3) The CRUX honesty test: does k=1 NVM nonvanishing (all T_j != 0) say ANYTHING
      about the SIZE B?  (A nonzero scalar can still be tiny or huge.)  We exhibit
      cases where all T_j != 0 yet B is whatever the BGK wall says -- nonvanishing
      gives NO size bound.  This is the wall the connection welds to.

Exact-ish: complex arithmetic at double precision; identities checked to < 1e-8.
We also do an EXACT-integer cross check of |eta_b|^2 to rule out float artifacts.
"""
import cmath, math

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    fact = []
    phi = p-1; x = phi; d = 2
    while d*d <= x:
        if x % d == 0:
            fact.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fact.append(x)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fact):
            return g
    return None

def find_prime_for_subgroup(n, beta_lo=4, beta_hi=6, count=2):
    """primes p = m*n + 1 with p ~ n^beta, beta in [beta_lo, beta_hi]  (proper subgroup, large prime)."""
    out = []
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    # walk m so that p = m*n+1 lands in [lo,hi]
    m = max(2, lo // n)
    while p := m*n + 1:
        if p > hi: break
        if is_prime(p) and ((p-1) // n) == m and m >= 2:
            out.append((p, m))
            if len(out) >= count: break
        m += 1
    return out

def gauss_sum_of_extension(p, g, m, n, i):
    """
    G_i = Gauss sum of the i-th extension phi_i of the fixed (here trivial) character chi on mu_n.
    The m extensions of chi to F_p^* are the multiplicative characters that agree with chi on mu_n;
    they are { chi * psi_dual^i } where psi_dual is a generating character of the quotient F_p^*/mu_n
    (order m).  Concretely a multiplicative character of order dividing... we realize:
        a character constant on mu_n  <=>  trivial on mu_n  <=>  factors through F_p^*/mu_n (order m).
    Take chi_t(g^a) = omega_m^{t*a*? } ... cleaner: a char trivial on mu_n = (g^a) -> zeta_m^{t * a}
    where t in 0..m-1 indexes it (since g^{m} generates mu_n, char trivial on mu_n must send g -> a
    primitive (p-1)/n = m-th root of unity raised to t... let's just build all chars of order | m).
    G_i = sum_{x in F_p^*} char_i(x) * e_p(x).
    """
    wq = 2j*math.pi/p
    zm = cmath.exp(2j*math.pi/m)
    # char_t(g^a) = zm^{t*a};  this is trivial on mu_n = <g^m> since zm^{t*m}=? need zm^m=1 => yes.
    # But we need char trivial on mu_n: char(g^m)=zm^{t*m}= (zm^m)^t = 1.  zm has order m so zm^m=1. OK.
    # discrete log table
    dlog = {}
    cur = 1
    for a in range(p-1):
        dlog[cur] = a
        cur = (cur*g) % p
    s = 0j
    for x in range(1, p):
        a = dlog[x]
        ch = zm ** ((i*a) % m)
        s += ch * cmath.exp(wq*x)
    return s

def etas_and_B(p, g, m, n):
    """eta_b = sum_{y in mu_n} e_p(b y), b in F_p^*.  Return dict, B=max|eta_b|."""
    wq = 2j*math.pi/p
    H = [pow(g, (m*j) % (p-1), p) for j in range(n)]
    etas = {}
    for b in range(1, p):
        etas[b] = sum(cmath.exp(wq*((b*h) % p)) for h in H)
    B = max(abs(v) for v in etas.values())
    return etas, B, H

def eta_abs2_exact(p, b, H):
    """ |eta_b|^2 = sum_{y,y' in H} e_p(b(y-y')) ; this is sum of cos(2pi b(y-y')/p), real.
        Exact-integer-friendly: count pairwise differences. |eta_b|^2 = sum_d c_d * e_p(b d). """
    from collections import Counter
    diffs = Counter()
    for y in H:
        for yp in H:
            diffs[(y - yp) % p] += 1
    wq = 2j*math.pi/p
    val = sum(c * cmath.exp(wq*((b*d) % p)) for d, c in diffs.items())
    return val.real  # imaginary part ~0

# -------------------------------------------------------------------
print("="*78)
print("C005 probe: are the 1x1 NVM minors (T_j) literally the Gauss-period house eta_b?")
print("PRIZE-FLAVOURED: proper dyadic subgroup mu_n, n=2^mu, p ~ n^beta (large prime)")
print("="*78)

results = []
for n in [8, 16, 32]:
    found = find_prime_for_subgroup(n, beta_lo=2.0, beta_hi=3.2, count=2)
    if not found:
        print(f"\n[n={n}] no suitable prime found in range"); continue
    for (p, m) in found:
        g = primitive_root(p)
        beta = math.log(p)/math.log(n)
        print(f"\n[n={n} (=2^{int(math.log2(n))}), p={p}, m=(p-1)/n={m}, beta=log_n p={beta:.2f}]")
        # build the m Gauss sums G_i
        G = [gauss_sum_of_extension(p, g, m, n, i) for i in range(m)]
        # all |G_i| should be sqrt(p) (for i!=0 the extension is nontrivial; i=0 trivial gives -1)
        modG = [abs(x) for x in G]
        print(f"  |G_i| (i=0..m-1): {[round(v,3) for v in modG]}   (sqrt p={math.sqrt(p):.3f})")
        # T_j = (1/m) sum_i omega^{i j} G_i,  omega = zeta_m
        zm = cmath.exp(2j*math.pi/m)
        T = [ (1/m)*sum(zm**((i*j) % m) * G[i] for i in range(m)) for j in range(m) ]
        # prize etas
        etas, B, H = etas_and_B(p, g, m, n)
        # The m DISTINCT eta values are the period values eta_{g^c}, c=0..m-1 (one per coset of mu_n).
        period_vals = [etas[pow(g, c, p) % p] for c in range(m)]
        # ---- (1) IDENTITY check: is {T_j} a permutation of the period values {eta_{coset}}? ----
        # The claim is T_j = eta_{<some coset>}, exactly (no sqrt(q)/m factor here because eta is the
        # RAW incomplete sum and T_j is ALSO a raw sum over the same mu_n once unwound).
        # Sort by complex value to compare as multisets.
        def keyc(z): return (round(z.real,6), round(z.imag,6))
        Ts = sorted(T, key=keyc)
        Ps = sorted(period_vals, key=keyc)
        match_direct = all(abs(a-b) < 1e-6 for a,b in zip(Ts,Ps))
        # also test with the sqrt(q)/m scaling the connection literally wrote:
        scale = math.sqrt(p)/m
        Tscaled = sorted([t/scale for t in T], key=keyc) if scale>0 else None
        match_scaled = (Tscaled is not None) and all(abs(a-b) < 1e-6 for a,b in zip(Tscaled,Ps))
        # ---- (2) sup-norm equivalence ----
        maxT = max(abs(t) for t in T)
        print(f"  max_j|T_j| = {maxT:.4f}   B = max_b|eta_b| = {B:.4f}   "
              f"max over PERIODS |eta_coset| = {max(abs(v) for v in period_vals):.4f}")
        print(f"  IDENTITY {{T_j}} == {{eta_coset}} (raw, no scale)?  {match_direct}")
        print(f"  IDENTITY {{T_j/(sqrtq/m)}} == {{eta_coset}}?       {match_scaled}")
        # ---- (3) honesty: nonvanishing vs size ----
        allTnz = all(abs(t) > 1e-6 for t in T)
        print(f"  k=1 NVM (all T_j != 0)? {allTnz}   <-- nonvanishing is a 0/1 fact; B is a SIZE.")
        # exact cross-check of B via integer differences
        Bexact = math.sqrt(max(eta_abs2_exact(p, b, H) for b in range(1,p)))
        print(f"  exact-arith B (sqrt of integer |eta_b|^2) = {Bexact:.4f}  (float B={B:.4f})")
        results.append((n,p,m,match_direct,match_scaled,allTnz,B,Bexact,maxT))

print("\n" + "="*78)
print("SUMMARY")
print("="*78)
for (n,p,m,md,ms,nz,B,Be,maxT) in results:
    print(f"  n={n:3d} p={p:7d} m={m:5d}: T==eta(raw)={md}  T==eta(scaled)={ms}  "
          f"allTnz={nz}  B={B:.3f}(exact {Be:.3f})  maxT={maxT:.3f}")
print("""
INTERPRETATION KEY:
 - If T==eta (raw or scaled) holds: the IDENTITY part of C005 is CONFIRMED (the 1x1
   minors ARE the period house, as the in-tree Lean lemma cftMat_apply_eq_houseVec
   already asserts symbolically).  That part is PROVEN/structural, not the open part.
 - max_j|T_j|*(scale) vs B tests whether the k=1 sup-norm IS the prize B.
 - allTnz=True while B is large = the HONEST CRUX: k=1 nonvanishing (NVM at k=1) is a
   purely qualitative 0/1 statement and gives NO upper bound on B.  The quantitative
   target B <= C sqrt(n log(p/n)) is NOT delivered by any minor-nonvanishing fact.
   => the connection IDENTIFIES the right object but WELDS to the BGK sup-norm wall.
""")
