import math
# Regime pinning. q-1 = n*m, with n=2^mu the FFT domain (mu<=40 realistic for NTT),
# and the spec demands ANTI-COLLISION / security index m = (q-1)/n >= 2^128 (so soundness err ~ 1/m or n/q etc).
# Directive claim: "m held constant ~2^128 as n grows => n=Theta(q) positive proportion."
# Test: is n>=sqrt(q)? density n/q? exponent beta = log_n(p).
print(f"{'mu':>4} {'n=2^mu':>10} {'log2 q':>8} {'density=n/q':>14} {'n>=sqrt(q)?':>12} {'beta=log_n p':>14} {'q^? exponent':>14}")
for mu in [10, 20, 30, 32, 40]:
    n = 2**mu
    m = 2**128                      # the held-constant index
    q = n*m + 1                     # q-1 = n*m
    log2q = math.log2(q)
    density = n/q                   # = 1/m
    sqrtq = q**0.5
    beta = math.log(q, n)           # n = p^{1/beta}
    expo = mu/(mu+128)              # n = q^{mu/(mu+128)}
    print(f"{mu:>4} 2^{mu:<8} {log2q:>8.1f} 2^{math.log2(density):>10.1f}   {'YES' if n>=sqrtq else 'NO':>12} {beta:>14.3f} q^{expo:>11.4f}")
print()
print("Key facts:")
print("  density = n/q = 1/m = 2^-128  (CONSTANT, the thinnest regime; independent of mu)")
print("  n = q^{mu/(mu+128)}: ranges q^0.072 (mu=10) .. q^0.238 (mu=40) -- all BELOW q^{1/4}")
print("  n >= sqrt(q) is FALSE by 2^{64-mu/2} >= 2^44")
print()
print("So: 'm constant' does NOT mean n=Theta(q). n=Theta(q) needs m=O(1), but m=2^128 is a HUGE constant.")
print("n is the SMALL factor. POSITIVE-PROPORTION PREMISE IS AN ARITHMETIC ERROR. Regime is THIN.")
