"""
probe_444_gapped_product.py  (#444 — O_P=1 proxy, NEW gapped-product reformulation)

Claim under test (NEW handle for the closable O_P=1 proxy face):

  Binding far-line direction d_gamma(x) = x^{n/2+1} + gamma * x^{n/2-1} on mu_n.
  A bad gamma <=> exists f, deg f < k, with f agreeing with d_gamma on a set T, |T| >= s.
  Multiplying by x^{n/2+1} (and using chi(x)=x^{n/2}, chi^2=1) this is EQUIVALENT to:

      psi_f(x) := f(x) * x^{n/2+1} - x^2   is CONSTANT (= gamma) on T.

  i.e. T is a level set of psi_f, and as a polynomial identity over F_p:

      psi_f(X) - gamma  =  V_T(X) * W(X),     V_T = prod_{t in T}(X - t),  deg W = n/2 - c.

  The support of psi_f - gamma is  {0, 2} U [n/2+1, n/2+k]  -- a heavily GAPPED polynomial
  (exponents 1 and 3..n/2 are forced ZERO; exponent 2 has coeff -1; exponent 0 is -gamma).

We verify, at n=16 (binding a=9,b=7), over F_p with mu_16 (p=65537):
  (A) the level-set reformulation: bad gamma (interpolation defn) == constant-value of some
      psi_f on >= s points.
  (B) #bad gamma and O_P (orbit count) at the binding depth c=3 (expect 9 = 1 + 8*1, O_P=1).
  (C) the gapped support of psi_f - gamma for every bad (f, gamma).
  (D) the pinned low-degree coefficients: [X^1]=0, [X^j]=0 (3<=j<=n/2), [X^2]=-1.
"""
import itertools, sys

p = 65537            # 2^16 + 1, prime, ==1 mod 16  -> mu_16 exists
n = 16
k = 4                # deg f < k  (rate rho = k/n = 1/4)
a, b = n//2 + 1, n//2 - 1   # binding direction x^9 + gamma x^7
c = 3                # binding agreement depth; s = k + c = 7
s = k + c

# ---- build mu_n ----
# find a generator g of F_p^*, then w = g^{(p-1)/n} has order n
def order(x):
    o, cur = 1, x
    while cur != 1:
        cur = (cur * x) % p; o += 1
    return o

g = 3
while order(g) != p - 1:
    g += 1
w = pow(g, (p - 1) // n, p)
assert order(w) == n
mu = [pow(w, i, p) for i in range(n)]   # mu_n
muset = set(mu)

# ---- interpolation test: does deg<k poly interpolate the s values (x_j, y_j)? ----
# y_j = d_gamma(x_j) = x_j^a + gamma x_j^b.  deg<k interpolation of s>k points exists
# iff all order-(>=k+1) divided differences vanish, i.e. the (s) x (k) Vandermonde-extended
# system is consistent. Simplest: build the s-point interpolation, check it has deg<k.
def vandermonde_solve_lowdeg(xs, ys):
    """Return True if a polynomial of degree < k passes through all (xs[i], ys[i])."""
    # Lagrange/Newton: fit unique deg<s poly; check coeffs of X^k..X^{s-1} are 0.
    # Build Newton divided differences.
    m = len(xs)
    coef = list(ys)
    for j in range(1, m):
        for i in range(m - 1, j - 1, -1):
            denom = (xs[i] - xs[i - j]) % p
            coef[i] = ((coef[i] - coef[i - 1]) * pow(denom, p - 2, p)) % p
    # coef are Newton coeffs; poly degree = highest i with coef[i]!=0 (in Newton basis,
    # leading term degree equals index). deg<k  <=>  coef[k..]==0.
    return all(coef[i] % p == 0 for i in range(k, m))

# ---- (A)+(B): enumerate bad gamma at binding depth via agreement on size-s subsets ----
# A gamma is bad if SOME size-s subset T of mu_n admits deg<k interpolation of d_gamma|_T.
# For each size-s subset T, the interpolation is consistent for at most a 1-dim family of
# gamma (it pins gamma). We collect the gammas.
bad_gamma = set()
bad_records = []   # (gamma, T, f_coeffs)
# For each T, solve for (f, gamma): f deg<k (k unknowns) + gamma (1 unknown) = k+1 unknowns;
# constraints: f(t)*? ... easier: f(t) + gamma*? no -- use d_gamma agreement directly.
# d_gamma(t) = t^a + gamma t^b ; want f(t) = d_gamma(t) for t in T, f deg<k.
# Unknowns: c_0..c_{k-1} (f), gamma. Equations (|T|=s): sum_i c_i t^i - gamma t^b = t^a.
# Linear system  M [c;gamma] = rhs,  M is s x (k+1).  Solvable => consistent => bad gamma.
def solve_system(T):
    rows = []
    rhs = []
    for t in T:
        row = [pow(t, i, p) for i in range(k)] + [(-pow(t, b, p)) % p]
        rows.append(row); rhs.append(pow(t, a, p))
    # Gaussian elimination over F_p on augmented [rows | rhs], s x (k+2)
    A = [r[:] + [rhs[i]] for i, r in enumerate(rows)]
    ncol = k + 1
    piv = []
    r = 0
    for col in range(ncol):
        pr = None
        for rr in range(r, len(A)):
            if A[rr][col] % p != 0:
                pr = rr; break
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        inv = pow(A[r][col], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for rr in range(len(A)):
            if rr != r and A[rr][col] % p != 0:
                f = A[rr][col]
                A[rr] = [(A[rr][j] - f * A[r][j]) % p for j in range(ncol + 1)]
        piv.append(col); r += 1
        if r == len(A): break
    # consistency: any row all-zero in coeff cols but nonzero rhs => inconsistent
    for rr in range(len(A)):
        if all(A[rr][j] % p == 0 for j in range(ncol)) and A[rr][ncol] % p != 0:
            return None
    # gamma is determined iff column k (gamma) is a pivot; else free (degenerate, skip).
    if k not in piv:
        return 'free'   # degenerate direction (every gamma works) -- not the binding case
    # back out gamma value
    sol = [0] * ncol
    # reconstruct from RREF
    for idx, col in enumerate(piv):
        sol[col] = A[idx][ncol] % p
    gamma = sol[k]
    fcoef = sol[:k]
    return (gamma, fcoef)

free_seen = 0
for T in itertools.combinations(mu, s):
    res = solve_system(T)
    if res is None:
        continue
    if res == 'free':
        free_seen += 1
        continue
    gamma, fcoef = res
    if gamma % p == 0:
        # gamma=0 trivial branch; record separately
        bad_gamma.add(0)
        continue
    bad_gamma.add(gamma)
    if len(bad_records) < 2000:
        bad_records.append((gamma, T, fcoef))

nz = sorted(x for x in bad_gamma if x != 0)
has_zero = 0 in bad_gamma
print(f"[B] n={n} k={k} c={c} s={s} binding x^{a}+g*x^{b}")
print(f"    #bad gamma (nonzero) = {len(nz)} ; gamma=0 bad? {has_zero} ; degenerate-T skipped={free_seen}")

# orbit count O_P: nonzero bad gammas under multiplication by g^{a-b}=w^2 (d=gcd(a-b,n)=2)
d = 2
mult = pow(w, a - b, p)   # = w^2
orbits = []
remaining = set(nz)
while remaining:
    x0 = next(iter(remaining))
    orb = set()
    cur = x0
    for _ in range(n // d):
        orb.add(cur); cur = (cur * mult) % p
    orbits.append(orb)
    remaining -= orb
print(f"    orbit size n/d = {n//d} ; #orbits O_P = {len(orbits)} ; #bad = {has_zero} + (n/d)*O_P "
      f"= {int(has_zero) + (n//d)*len(orbits)} (matches {len(nz)+int(has_zero)}? "
      f"{int(has_zero)+(n//d)*len(orbits) == len(nz)+int(has_zero)})")

# ---- (A) level-set reformulation + (C)(D) gapped support ----
def psi_minus_gamma_coeffs(fcoef, gamma):
    """coeffs of psi_f(X) - gamma = sum_i fcoef[i] X^{n/2+1+i} - X^2 - gamma, as dict exp->coef."""
    co = {}
    for i, ci in enumerate(fcoef):
        e = n//2 + 1 + i
        co[e] = (co.get(e, 0) + ci) % p
    co[2] = (co.get(2, 0) - 1) % p
    co[0] = (co.get(0, 0) - gamma) % p
    return {e: v for e, v in co.items() if v % p != 0}

def eval_poly_on(co, x):
    return sum(v * pow(x, e, p) for e, v in co.items()) % p

ok_levelset = 0
ok_gapped = 0
ok_pinned = 0
checked = 0
allowed_support = set([0, 2]) | set(range(n//2 + 1, n//2 + k + 1))
for gamma, T, fcoef in bad_records:
    checked += 1
    co = psi_minus_gamma_coeffs(fcoef, gamma)
    # (A) psi_f constant = gamma on T  <=>  psi_f - gamma vanishes on T
    if all(eval_poly_on(co, t) == 0 for t in T):
        ok_levelset += 1
    # (C) support inside {0,2} U [n/2+1, n/2+k]
    if set(co.keys()) <= allowed_support:
        ok_gapped += 1
    # (D) pinned: [X^1]=0 (absent), [X^j]=0 for 3<=j<=n/2 (absent), [X^2]=-1
    pin = (1 not in co) and all(j not in co for j in range(3, n//2 + 1)) and (co.get(2, 0) == (p - 1))
    if pin:
        ok_pinned += 1

print(f"[A] level-set reformulation: psi_f - gamma vanishes on T : {ok_levelset}/{checked}")
print(f"[C] gapped support subset {{0,2}} U [{n//2+1},{n//2+k}] : {ok_gapped}/{checked}")
print(f"[D] pinned low coeffs ([X^1]=0, [X^3..n/2]=0, [X^2]=-1) : {ok_pinned}/{checked}")
print()
print("VERDICT: if all four are full counts, the gapped-product reformulation of the O_P=1")
print("proxy is confirmed -- bad gamma == constant level-values of the GAPPED polynomial psi_f,")
print("and O_P=1 == the gapped-product variety V_T*W has a single nonzero-gamma coset.")
