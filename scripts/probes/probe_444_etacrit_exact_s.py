#!/usr/bin/env python3
"""
probe_444_etacrit_exact_s.py  — does eta_crit use s=(rho+eta)n (correct) or s=n (KB shortcut)?

The norm-bound contradiction is:  defect needs |C| >= p^{2 eta}; |C| <= s; so need p^{2 eta} <= s,
i.e. NO defect when  p^{2 eta} > s  <=>  eta > log(s)/(2 log p) =: eta_crit.

CRITICAL: s = (rho+eta)*n at the relevant radius, NOT n. eta_crit is therefore an IMPLICIT
equation: eta_crit = log((rho+eta_crit) n) / (2 log p). Solve it self-consistently and check
whether the FLOOR delta = (1-rho) - eta_crit still exceeds Johnson 1-sqrt(rho).

Also: the KB uses log p = (128+mu) bits and log s = mu bits (s~n). Compare both.
"""
import math

def solve_etacrit(rho, mu):
    """Solve eta = log2((rho+eta)*2^mu) / (2*(128+mu)) by fixed-point iteration."""
    logp2 = 128 + mu  # log2 p
    eta = 0.09
    for _ in range(200):
        s = (rho + eta) * (2**mu)
        if s <= 1:
            s = 2
        eta_new = math.log2(s) / (2*logp2)
        if abs(eta_new - eta) < 1e-12:
            break
        eta = eta_new
    return eta

print("### eta_crit solved self-consistently with s=(rho+eta)n vs KB shortcut s=n ###")
print(f"{'mu':>4} {'rho':>7} {'Johnson':>8} {'cap':>7} {'ec(s=n)':>8} {'ec(exact)':>10} "
      f"{'floor_exact':>12} {'floor>J?':>9} {'margin':>8}")
broken = []
for mu in [25, 30, 35, 40]:
    for rho in [1/2, 1/4, 1/8, 1/16]:
        logp2 = 128 + mu
        ec_kb = mu / (2*logp2)              # s = n shortcut
        ec_exact = solve_etacrit(rho, mu)   # s = (rho+eta) n
        cap = 1 - rho
        johnson = 1 - math.sqrt(rho)
        floor_exact = cap - ec_exact
        ok = floor_exact > johnson
        if not ok:
            broken.append((mu, rho, floor_exact, johnson))
        print(f"{mu:>4} {rho:>7.4f} {johnson:>8.4f} {cap:>7.4f} {ec_kb:>8.4f} {ec_exact:>10.4f} "
              f"{floor_exact:>12.4f} {str(ok):>9} {floor_exact-johnson:>8.4f}")

print()
if broken:
    print("!!! FLOOR FAILS to beat Johnson at:", broken)
else:
    print("Floor (with exact-s eta_crit) still beats Johnson at every prize rate.")

# Also: the binding uses a=s (deg x^a). Is s ~ n or s ~ (rho+eta) n? In the incidence
# #{S: first c power sums vanish}, |S|=s=(rho+eta)n and c=s-k=eta*n. So s<n strictly.
# eta_crit uses THIS s. The KB's "s~n" overstates log s, making eta_crit too big (conservative
# for the floor => the floor with the true smaller eta_crit is even STRONGER). Confirm sign:
print("\nNote: true s=(rho+eta)n < n => log s < log n => eta_crit(exact) < eta_crit(KB s=n).")
print("So the floor is if anything STRONGER with exact s. The KB shortcut is conservative.")
