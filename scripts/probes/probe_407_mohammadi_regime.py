import math

# ============================================================================
# DICTIONARY (CRITICAL):
#   My object:  mu_n = dyadic subgroup of size n = 2^a in F_q^*, a up to 40.
#               m = (q-1)/n ~ 2^128 held CONSTANT (positive-proportion regime).
#               eta_b = sum_{x in mu_n} psi(b x),   M = max_{b != 0} |eta_b|.
#   Mohammadi:  H = group of N-th powers, |H| = (q-1)/N.  S(a,H) = sum_{h in H} psi_a(h).
#               S_N(a) = sum_{x in F_q} psi_a(x^N) = 1 + N * S(a,H).
#   MATCH: mu_n = H  =>  |H| = n  =>  N = (q-1)/n = m.
#   So Mohammadi's index "N" = my m ~ 2^128, and S(a,H) = eta_a.
#   Therefore:  M = max_a |S(a,H)| = (1/m) * max_a |S_m(a) - 1| ~ (1/m) max_a |S_m(a)|.
# ============================================================================

# Prize: q ~ n * 2^128, q prime (so F_q has NO proper subfields; subfield conditions vacuously hold).
# log2 q ~ a + 128.  M target: C * sqrt(n log(q/n)) = C*sqrt(n * 128 ln2).

def log2(x): return math.log(x, 2)

print("="*100)
print("Mohammadi bound translated to the prize subgroup-sum M = max|eta_b|, via M = (1/m)*max|S_m(a)|")
print("Prize: q = n*2^128 (prime), n=2^a, m=(q-1)/n ~ 2^128 CONSTANT.")
print("="*100)
print()
print(f"{'a':>3} {'log2 n':>7} {'log2 q':>8} {'log2 m':>8} | "
      f"{'Weil/m':>10} {'Cor7/m(log2)':>14} {'trivial=n':>10} {'target M':>10} {'log2(targetM)':>14}")
print("-"*100)

for a in [10, 20, 30, 32, 35, 40]:
    n = 2.0**a
    log2q = a + 128.0           # q ~ n*2^128
    q = 2.0**log2q
    m = q / n                   # = (q-1)/n ~ 2^128, but exact m = (q-1)/n
    N = m                       # Mohammadi's index N = m
    log2m = log2(m)

    # ----- Weil bound (eq 4):  max|S_N(a)| < (N-1) q^{1/2}.  => M < (N-1)q^{1/2}/N ~ q^{1/2}. -----
    weil_SN = (N-1.0)*q**0.5
    weil_M = weil_SN / N        # ~ q^{1/2}  (this is just |H| <= ... trivial-ish; actually ~ sqrt(q))
    log2_weil_M = log2(weil_M)

    # ----- Mohammadi Corollary 7: depends on where N=m sits relative to q^{1/2}. -----
    # Here N = m ~ 2^128, q^{1/2} = 2^{(a+128)/2}.  For a < 128: q^{1/2} = 2^{(a+128)/2}.
    #   a=40 => q^{1/2}=2^84. m=2^128 >> q^{1/2}. So N = m is in the LARGE-N regime (N > q^{1/2+...}).
    # Corollary 7 only covers N up to q^{1/2 + 1/68 - eps}.  q^{1/2+1/68} = 2^{(a+128)*(1/2+1/68)}.
    q_half = q**0.5
    q_half_168 = q**(0.5 + 1.0/68.0)
    log2_qhalf = log2(q_half)
    log2_q_half_168 = log2(q_half_168)

    # Best Mohammadi estimate (the n=q^{1/2+1/68} top line of Cor 7): q^{229/264} N^{17/66}
    # but ONLY valid for N <= q^{1/2+1/68}.  Check if m falls in range.
    in_range = (N <= q_half_168)
    moh_SN_top = q**(229.0/264.0) * N**(17.0/66.0)
    moh_M_top = moh_SN_top / N
    log2_moh_M = log2(moh_M_top)

    # target M = C*sqrt(n log(q/n)), C=1.5
    targetM = 1.5*math.sqrt(n * math.log(q/n))
    log2_target = log2(targetM)

    print(f"{a:>3} {a:>7} {log2q:>8.1f} {log2m:>8.1f} | "
          f"2^{log2_weil_M:>6.1f}   2^{log2_moh_M:>9.1f}   2^{a:>6}   {targetM:>10.1f} 2^{log2_target:>10.2f}")
    print(f"       N=m=2^{log2m:.1f}  vs  q^(1/2)=2^{log2_qhalf:.1f}  q^(1/2+1/68)=2^{log2_q_half_168:.1f}  "
          f"=> m in Mohammadi range? {in_range}")
print()
