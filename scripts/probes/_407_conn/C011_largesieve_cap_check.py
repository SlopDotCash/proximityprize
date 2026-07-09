"""
C011 sub-claim (ii) audit: the W-largesieve r-validity cap.

Connection asserts: ManyTermResultantBound char-0 energy valid exactly when
  q > (2r)^{phi(n)} = (2r)^{n/2}
and that "logs give r-validity cap at r ~ log q/(n log r) -- the SAME r~beta=log_n q
at the production index."

Take logs of q > (2r)^{n/2}:
  log q > (n/2) log(2r)
  log(2r) < (2/n) log q
  r < (1/2) exp( (2/n) log q ) = (1/2) q^{2/n}.

The connection's claimed form r ~ log q/(n log r) is what you get from a DIFFERENT
(wrong) rearrangement. Let's check BOTH and see whether either equals beta=log_n q.

beta = log_n q = log q / log n.   Production: n=2^mu, q~n^beta, beta in {4,5}.
"r ~ log q/(n log r)" : with r~beta, RHS = log q/(n log beta).
   = (beta log n)/(n log beta). For n=2^32, beta=5: = 5*32*ln2/(2^32 * ln5) ~ 1.6e-8. NOT 5.

So even the connection's OWN stated cap formula r~log q/(n log r), if you actually
plug numbers, gives r ~ 1e-8 (i.e. r=0), NOT beta. The "SAME r~beta" claim is false:
the largesieve cap has n (=2^mu) in the denominator, which crushes it to O(1)/below-1
for every prize n, completely decoupled from beta.
"""
import math
from sympy import isprime

def find_prime_q(n, beta):
    target = n**beta
    k = (target - 1 + n - 1)//n
    while True:
        q = 1 + k*n
        if q >= target and isprime(q):
            return q
        k += 1

print(f"{'mu':>3} {'beta':>4} {'logn_q(=b)':>10} {'r_cap_correct':>14} "
      f"{'conn_form(r~b)':>16} {'match_beta?':>11}")
print("-"*72)
for mu in [8,16,24,32]:
    n = 2**mu
    for beta in [4,5]:
        q = find_prime_q(n, beta)
        bq = math.log(q)/math.log(n)
        # correct cap:  r < (1/2) q^{2/n}
        r_cap = 0.5*math.exp((2.0/n)*math.log(q))
        # connection's stated form r ~ log q/(n log r), self-consistent fixed point near r~beta:
        conn = math.log(q)/(n*math.log(max(bq,1.0001)))
        match = (abs(r_cap-beta)<=1.0) or (abs(conn-beta)<=1.0)
        print(f"{mu:>3} {beta:>4} {bq:>10.3f} {r_cap:>14.6f} {conn:>16.3e} {str(match):>11}")

print()
print("Conclusion: the W-largesieve r-cap is (1/2) q^{2/n}, which -> 1/2 as n grows because")
print("n=2^mu sits in the EXPONENT denominator 2/n. It is O(1) (<1, i.e. r*=0) for every prize n,")
print("INDEPENDENT of beta. It does NOT coincide with beta=log_n q. The connection's claim that")
print("'logs give r~beta=log_n q' is arithmetically false -- there is no production index at which")
print("(2r)^{n/2}<q allows r as large as beta=4-5 (would need q > (2*4)^{2^31} = astronomically big).")
print()
print("Cross-check: what q WOULD be needed for r_cap >= beta=5 at n=2^32?")
n = 2**32
r = 5
need_log2q = (n/2)*math.log2(2*r)
print(f"  need log2 q > (n/2)*log2(2r) = (2^31)*log2(10) = {need_log2q:.3e}  (vs prize log2 q <= 256)")
print(f"  short by factor ~ {need_log2q/256:.3e} in the log. SAME structural wall as W-anomaly/KU,")
print("  but the crossover depths are NOT a common beta -- they are 2*beta-3, O(1), and a size-cap.")
