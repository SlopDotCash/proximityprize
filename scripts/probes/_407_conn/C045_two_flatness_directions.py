"""
C045 attack PART 2: the LOGICAL crux.

The connection claims: "max_b ||eta_b||^2 <= sum_b ||eta_b||^2 = q*n gives only
sqrt(q) per word (the Johnson sqrt(n) deficit), with equality EXACTLY the flat
spectrum", and that this flat-spectrum equality IS the Johnson-extremal flat
S_j profile (one object, two faces).

This part checks WHETHER the two "flat" / two "CS-equality" conditions are the
same object. There are TWO distinct Cauchy-Schwarz / 2nd-moment steps:

  STEP-J (Johnson, JohnsonSecondMomentFrontier): over n COORDINATES,
     (sum_j S_j)^2 <= n * sum_j S_j^2.
     Equality  <=>  S_j FLAT (all coordinates carry equal #agreements).
     This is the cauchySchwarz_eq_iff_flat lemma. Johnson is TIGHT when flat.

  STEP-P (Parseval / period 2nd moment, SubgroupGaussSumSecondMoment): over q
     FREQUENCIES,  max_b ||eta_b||^2 <= sum_b ||eta_b||^2 = q*n.
     This is a TRIVIAL "max <= sum" bound (NOT Cauchy-Schwarz). Equality
     <=>  ALL mass on ONE frequency, i.e. spectrum a SINGLE SPIKE (the OPPOSITE
     of flat). And it gives B <= sqrt(q*n), which is WORSE than the trivial
     |eta_b| <= n (since q*n >> n^2 when q>>n). So STEP-P's "equality case" is
     spiky, not flat; and the bound it yields is vacuous.

So the connection's bridge has THREE problems we test:
 (P1) STEP-P is max<=sum, whose equality is a SPIKE, not flat. The Johnson
      equality is flat. They are NOT the same configuration; they are OPPOSITE.
 (P2) The quantity the prize cares about is max_{b != 0} ||eta_b|| = B (the
      Paley/BGK object). The 2nd moment / "Var = n" controls only the AVERAGE,
      which is consistent with ANY B in [sqrt(n), n]. So Var=n does NOT pin B;
      it is BLIND to the worst-case the prize needs.
 (P3) Even granting a bridge, what bound would the period 2nd moment give for B?
      Pure max<=sum: B <= sqrt(qn). Pure 4th-moment (genuine CS on the spectrum):
      B^2 <= sqrt(q * sum_b ||eta||^4). Compute the ACTUAL 4th moment and see what
      B-bound CS gives, vs true B. If CS-from-moments saturates at the flat
      spectrum, that flat is the AVERAGE-flat (all nonzero b equal), which is the
      Salem-Zygmund extremal -- and check whether the TRUE spectrum is that flat
      (it is NOT, from part 1: B/sqrt(n) grows).
"""
import cmath, math
from sympy import isprime, primitive_root

def subgroup_mu_n(q, n):
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)
    G, x = [], 1
    for _ in range(n):
        G.append(x); x = (x*h) % q
    return G

def eta_sq(q, G, b):
    s = 0j; w = 2*math.pi*b/q
    for y in G: s += cmath.exp(1j*w*y)
    return abs(s)**2

def main():
    cases = [(8,1009),(16,7681),(32,12289),(64,65537)]
    print(f"{'n':>3} {'q':>6} | {'B=max_{b!=0}||eta||':>18} {'sqrt(n)':>8} {'sqrt(qn)':>9} "
          f"{'B/sqrt(qn)':>10} | {'CS_4thmom_bound_on_B':>20} {'B/CSbound':>10} | "
          f"{'sphere/flat predicts':>20}")
    for n, q in cases:
        if not isprime(q) or (q-1)%n: continue
        G = subgroup_mu_n(q, n)
        sq = [eta_sq(q,G,b) for b in range(1,q)]   # b != 0
        sq0 = eta_sq(q,G,0)                          # = n^2 exactly
        Bsq = max(sq); B = math.sqrt(Bsq)
        # full 2nd moment over ALL b (incl 0): q*n. Over b!=0: q*n - n^2.
        m2_nz = sum(sq)                              # ~ q*n - n^2
        # 4th moment over b != 0
        m4_nz = sum(s*s for s in sq)
        # genuine Cauchy-Schwarz bound on B from moments:
        #   B^2 = max sq <= (sum sq^2 / sum_count?) no -> use: max x <= sqrt(sum x^2)
        #   B^2 <= sqrt(m4_nz)   (since max <= L2 norm of the vector of sq's)
        cs_B = math.sqrt(math.sqrt(m4_nz))
        # what a TRULY flat nonzero spectrum would give: each ||eta||^2 = m2_nz/(q-1) ~ n
        flat_val = m2_nz/(q-1)
        sphere_flat_B = math.sqrt(flat_val)   # this is ~ sqrt(n): the "Salem-Zygmund extremal"
        print(f"{n:3d} {q:6d} | {B:18.4f} {math.sqrt(n):8.3f} {math.sqrt(q*n):9.2f} "
              f"{B/math.sqrt(q*n):10.4f} | {cs_B:20.4f} {B/cs_B:10.4f} | "
              f"flat={sphere_flat_B:.3f}(=sqrt(n)~{math.sqrt(n):.2f})")
    print()
    print("READING:")
    print(" * B/sqrt(qn) is TINY -> the max<=sum (STEP-P) bound sqrt(qn) is wildly loose; vacuous.")
    print(" * The 'flat nonzero spectrum' value ~ sqrt(n): that is the Johnson/Salem-Zygmund extremal.")
    print("   But the TRUE B is STRICTLY above sqrt(n) and the gap (B/sqrt(n)) GROWS -> the spectrum")
    print("   is NOT flat; the open problem is precisely the DEVIATION from flat, which Var=n cannot see.")
    print(" * CS-from-4th-moment bound (cs_B) is closer than sqrt(qn) but still ABOVE true B; it is the")
    print("   genuine moment-method route (face 3 of the open core) -- needs E_r(mu_n), NOT just Var.")

if __name__ == "__main__":
    main()
