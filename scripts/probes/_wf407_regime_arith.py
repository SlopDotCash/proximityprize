import math
ln2=math.log(2)
print("=== REGIME ARITHMETIC: spectral target vs best-provable, both framings ===\n")

# Prize spec: eps* = 2^-128, q = p ~ n * 2^128, so index m = (p-1)/n ~ 2^128 CONSTANT.
M_BITS=128
m = 2**M_BITS
logm = M_BITS*ln2  # natural log of m ~ 88.7

print("NEW fixed-index framing: m = 2^128 constant, n -> infinity")
print(f"  log m (nat) = {logm:.2f},  log_2 m = {M_BITS}")
print("  Target floor: B <= C*sqrt(n*log m) = C*sqrt(88.7)*sqrt(n) ~ 9.4*C*sqrt(n)")
print("  Ramanujan 2sqrt(n): target/Ramanujan = C*sqrt(log m)/2 = %.2f*C  >> 1  => RAMANUJAN FALSE\n" % (math.sqrt(logm)/2))

print("Regime parameter beta = log_n(p) = 1 + 128/log2(n)  -> 1 as n->inf:")
for nbits in [20,30,32,40,60,128,256,512]:
    n=2**nbits
    p=n*m
    beta=math.log(p,2)/nbits  # log_n p in bits-ratio = log2 p / log2 n
    rmax = 2*beta - 3    # reliable moment depth from CharSumMomentDeepWall
    ropt = math.log(p)   # optimal depth ~ ln q
    # best provable moment bound at r=rmax (if rmax>=1): (q E_rmax)^{1/2rmax} ~ q^{1/2rmax} sqrt(rmax n)
    print(f"  n=2^{nbits:<4} log_n p(beta)={beta:6.3f}  r_max(reliable)={rmax:7.2f}  r_opt(~ln q)={ropt:7.1f}  ratio r_opt/r_max={ropt/rmax if rmax>0 else float('inf'):8.2f}")

print()
print("=== THE SPECTRAL VERDICT ON RAMANUJAN-EXCESS ===")
print("Measured: B ~ sqrt(2 n ln m). Ramanujan cap 2sqrt(n) is EXCEEDED by factor sqrt(ln m / 2).")
print(f"At prize m=2^128: excess factor = sqrt(ln m /2) = sqrt({logm:.1f}/2) = {math.sqrt(logm/2):.2f}x over Ramanujan.")
print("So spectral-graph Ramanujan (B<=2sqrt(n)) is the WRONG (too strong, FALSE) target.")
print("The right target B<=C sqrt(n log m) is an EVT-of-Gauss-periods statement, NOT a spectral-gap bound.")
