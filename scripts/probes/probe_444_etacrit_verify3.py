#!/usr/bin/env python3
"""
probe_444_etacrit_verify3.py  (#444 Verify-3)

Verify the eta_crit formula and the widening-gap claim.

CLAIM under test:
  At the window radius, c = s - k = eta*n, s = (rho+eta)*n, k = rho*n.
  Action-Orbit norm ceiling:  p <= s^{n/(2c)} = s^{1/(2 eta)}.
  Boundary (clean/wall): log2(p) = (1/(2 eta)) * log2(s).
  Prize: log2(p) = 128 + mu  (p ~ n*2^128, n = 2^mu).
  Approx closed form:  eta_crit ~ mu / (2*(128+mu))     [drops the log2(rho+eta) term]

We do BOTH:
  (1) the approximate closed form mu/(2(128+mu));
  (2) the EXACT eta_crit solving  log2(p) = log2((rho+eta)*n) / (2*eta),
      i.e.  2*eta*(128+mu) = mu + log2(rho+eta).   [keeps the log2(rho+eta) term]
  and compare to eta_delta* = Theta(1/log n).

eta_delta* models (KKH26, eta = c0 / log n; n = 2^mu):
   - log = log2:  eta_delta* = c0 / mu
   - log = ln:    eta_delta* = c0 / (mu*ln2)
We report a band c0 in {0.5, 1.0, 1.5} for log2, plus 1/mu as the headline ("~1/mu").
"""
import math

LOG2 = math.log(2.0)

def log2(x):
    return math.log(x) / LOG2

def eta_crit_approx(mu):
    """mu / (2*(128+mu)) -- the synthesis' stated approx (drops log2(rho+eta))."""
    return mu / (2.0 * (128.0 + mu))

def eta_crit_exact(mu, rho):
    """
    Solve  log2(p) = log2(s)/(2 eta),  s = (rho+eta)*n,  log2(n)=mu, log2(p)=128+mu.
    => (128+mu) = (mu + log2(rho+eta)) / (2 eta)
    => g(eta) := 2*eta*(128+mu) - mu - log2(rho+eta) = 0.
    g is increasing in eta on (0, ...) (both 2*eta*(.) up and -log2(rho+eta) up as eta grows,
    since log2(rho+eta) increases so -log2 decreases... check sign carefully), solve by bisection.
    """
    L = 128.0 + mu
    def g(eta):
        return 2.0*eta*L - mu - log2(rho + eta)
    # bracket: at eta->0+, g-> -mu - log2(rho) ; for rho<1, log2(rho)<0 so -log2(rho)>0,
    # g(0+) = -mu + |log2(rho)| which is negative for mu>>. At eta=1, g(1)=2L-mu-log2(rho+1)>0.
    lo, hi = 1e-12, 1.0
    glo, ghi = g(lo), g(hi)
    # If g(lo) >= 0 already, eta_crit is effectively 0 (the boundary is below any meaningful eta):
    # this happens only at tiny mu where log2(rho) dominates mu. Return ~0 (clean everywhere).
    if glo >= 0:
        return 0.0
    assert glo < 0 < ghi, f"no bracket: g(lo)={glo}, g(hi)={ghi}"
    for _ in range(200):
        mid = 0.5*(lo+hi)
        if g(mid) > 0:
            hi = mid
        else:
            lo = mid
    return 0.5*(lo+hi)

print("="*100)
print("eta_crit verification (#444 Verify-3)")
print("="*100)
print("Prize: log2(p) = 128 + mu,  n = 2^mu,  rho = k/n,  c = (s-k) = eta*n,  s = (rho+eta)*n")
print("Boundary: log2(p) = log2(s)/(2 eta).   Clean iff eta > eta_crit.")
print()

mus = [20, 25, 30, 35, 40]
rhos = [(0.125, "1/8"), (0.0625, "1/16")]

hdr = f"{'mu':>3} {'rho':>5} {'log2p':>6} | {'eta_crit_approx':>16} {'eta_crit_EXACT':>15} | {'1/mu':>7} {'c0=0.5/mu':>10} {'c0=1.5/mu':>10} | {'dstar<crit?':>11} {'gap(exact-1/mu)':>15}"
print(hdr)
print("-"*len(hdr))

rows = []
for mu in mus:
    for rho, rlabel in rhos:
        ea = eta_crit_approx(mu)
        ex = eta_crit_exact(mu, rho)
        eds_headline = 1.0/mu          # "eta_delta* ~ 1/mu"
        eds_lo = 0.5/mu
        eds_hi = 1.5/mu
        clean = "NO" if eds_headline < ex else "YES-CLEAN"
        gap = ex - eds_headline
        rows.append((mu, rho, rlabel, ea, ex, eds_headline, eds_lo, eds_hi, clean, gap))
        print(f"{mu:>3} {rlabel:>5} {128+mu:>6} | {ea:>16.5f} {ex:>15.5f} | {eds_headline:>7.5f} {eds_lo:>10.5f} {eds_hi:>10.5f} | {clean:>11} {gap:>15.5f}")

print()
print("="*100)
print("WIDENING-GAP CHECK  (gap = eta_crit_exact - eta_delta*; does it grow with mu?)")
print("="*100)
for rho, rlabel in rhos:
    print(f"\n rho={rlabel}:")
    prev_gap = None
    for mu in mus:
        ex = eta_crit_exact(mu, rho)
        for c0lab, c0 in [("1/mu", 1.0), ("0.5/mu", 0.5), ("1.5/mu", 1.5)]:
            eds = c0/mu
            gap = ex - eds
            tag = ""
            if c0 == 1.0:
                if prev_gap is not None:
                    tag = "  WIDENS" if gap > prev_gap else "  shrinks"
                prev_gap = gap
            print(f"   mu={mu:>3}  eta_crit_exact={ex:.5f}  eta_dstar({c0lab})={eds:.5f}  gap={gap:+.5f}{tag if c0==1.0 else ''}")

print()
print("="*100)
print("LIMIT BEHAVIOUR (mu -> large): eta_crit -> ?  eta_delta* -> 0")
print("="*100)
for mu in [40, 80, 160, 320, 1000, 10000]:
    ex = eta_crit_exact(mu, 0.125)
    ea = eta_crit_approx(mu)
    print(f"   mu={mu:>6}  eta_crit_approx={ea:.6f}  eta_crit_exact(rho=1/8)={ex:.6f}  1/mu={1.0/mu:.6f}")

print()
print("Note: eta_crit_approx = mu/(2(128+mu)) -> 1/2 as mu->inf.")
print("      eta_crit_exact differs by the log2(rho+eta) correction (rho+eta<1 => log2<0 => raises threshold slightly).")

# Is there ANY mu (in a wide sweep) where eta_delta* >= eta_crit?
print()
print("="*100)
print("SEARCH: any mu in [4, 100000] with eta_delta*(=1/mu or 1.5/mu) >= eta_crit_exact?  (would make delta* CLEAN)")
print("="*100)
found = []
for mu in range(4, 100001):
    ex = eta_crit_exact(mu, 0.0625)  # rho=1/16 gives the SMALLEST eta_crit (largest c, hardest)... check both
    for c0 in (1.0, 1.5, 2.0):
        if c0/mu >= ex:
            found.append((mu, c0, c0/mu, ex))
if found:
    print(f"   FOUND {len(found)} crossings (delta* would be clean):")
    for mu, c0, eds, ex in found[:20]:
        print(f"     mu={mu} c0={c0} eta_dstar={eds:.5f} eta_crit={ex:.5f}")
else:
    print("   NONE. eta_delta* < eta_crit for ALL mu in [4,100000] and c0 in {1,1.5,2}. delta* NEVER clean.")
# also report the small-mu crossover for c0=1 just to be complete
print()
print("   (For reference: smallest mu where 1/mu < eta_crit_exact, i.e. delta* enters the wall:)")
for rho, rlabel in rhos:
    for mu in range(2, 60):
        ex = eta_crit_exact(mu, rho)
        if 1.0/mu < ex:
            print(f"     rho={rlabel}: delta* in wall for all mu >= {mu}  (at mu={mu}: 1/mu={1.0/mu:.5f} < eta_crit={ex:.5f})")
            break
