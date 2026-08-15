"""G97 probe (v2): pin the EXACT census->sup inflation mechanism.

Objects (Fable G74/G96 convention):
  eta_b = sum_{x in mu_n} e_p(b x),  b in F_p.
  |eta_0| = n (DC term).
  M = max_{b != 0} |eta_b|          (the single-embedding 'wall').
  Depth-r census  p*E_r = sum_{b} |eta_b|^{2r}  (sum over ALL b incl 0).

Two distinct inflation sources when extracting M from the census:
  (A) DC term: p*E_r >= |eta_0|^{2r} = n^{2r}, and n >= M (often n > M),
      so (p*E_r)^{1/2r} >= n >= M -- already >= the wall from DC alone.
  (B) Even the DC-SUBTRACTED census  p*E_r - n^{2r} = sum_{b!=0}|eta_b|^{2r}
      is a sum over the Frobenius M-orbit (size K = #{b!=0 : |eta_b|=M}) PLUS
      lower terms, so it is >= K * M^{2r}, giving
      (p*E_r - n^{2r})^{1/2r} >= K^{1/2r} * M > M  when K >= 2.

Confirm: (i) n >= M at every adversarial cell (DC dominates the wall);
         (ii) the DC-subtracted census still overshoots M by K^{1/2r} > 1
              at every finite rung r, i.e. census CANNOT reach the sup.
"""
import cmath
import math


def prime_factors(n):
    f = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f


def spectrum(n, p):
    g = None
    pf = set(prime_factors(n))
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n // q, p) != 1 for q in pf):
            g = cand
            break
    if g is None:
        return None
    mu = [pow(g, k, p) for k in range(n)]
    return [abs(sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in mu))
            for b in range(p)]


def v2(m):
    c = 0
    while m % 2 == 0:
        m //= 2
        c += 1
    return c


cells = [(8, 257), (16, 257), (16, 65537), (32, 257), (32, 193), (32, 577)]
print("  n      p  v2    n      M   n>=M?  K(M-orbit)  |  "
      "DC-subtracted (p*E_r - n^2r)^(1/2r)/M, r=1..6")
for n, p in cells:
    etas = spectrum(n, p)
    if etas is None:
        print(f"{n:>3}{p:>7}  no subgroup")
        continue
    M = max(etas[b] for b in range(1, p))
    K = sum(1 for b in range(1, p) if abs(etas[b] - M) < 1e-6)
    ndc = etas[0]
    ratios = []
    for r in range(1, 7):
        dcsub = sum(etas[b] ** (2 * r) for b in range(1, p))  # excludes b=0
        ext = dcsub ** (1.0 / (2 * r))
        ratios.append(ext / M)
    print(f"{n:>3}{p:>7}{v2(p-1):>4}{ndc:>6.1f}{M:>8.3f}   {ndc>=M-1e-9!s:>5}   {K:>6}      |  "
          + " ".join(f"{x:.4f}" for x in ratios))
