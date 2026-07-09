"""
C015 probe: lift the averaging list LOWER bound (averaging_list_lower_bound,
|{deg<k+1 polys agreeing with u0 on >= k+t pts}| >= C(n,k+t)/q^t) from the
DEGENERATE stack (w,0) to a NON-DEGENERATE monomial stack (u0, X^k), and measure
the loss list-count -> distinct-bad-gamma-count -> actual-mcaEvent count.

Bridge (badScalars_monomial_eq_degreeLTSucc):
  gamma is a BAD scalar of line (u0, X^k) for RS[k] at radius delta
   <=>  EXISTS deg<(k+1) poly q with coeff_k(q) = -gamma agreeing with u0 on a
        witness set S, |S| >= (1-delta)n
   AND  (for an actual mcaEvent) the pair (u0, X^k) is NOT jointly agreeable by a
        single codeword on S  (¬ pairJointAgreesOn).

PRIZE REGIME: domain = mu_n (dyadic subgroup), q prime = 1 mod n, q >> n.
We test F_q = F_12289, n in {8,16,32}, proper subgroups; exact integer arithmetic.

Question 1 (the attack plan): does a real non-degenerate (u0, X^k) realize the
C(n,k+t)/q^t averaging list with DISTINCT X^k-coefficients (distinct bad gamma)?
Question 2: of those distinct-coeff lifted polys, how many give an actual mcaEvent
(non-matchable second row)? i.e. how much does the list count degrade to bad-count?
"""
import itertools, sys

def subgroup(q, n):
    # multiplicative subgroup of order n in F_q^*
    assert (q-1) % n == 0
    # find generator g of F_q^*
    def order(a):
        o=1; x=a%q
        while x!=1:
            x=(x*a)%q; o+=1
        return o
    g=None
    for cand in range(2,q):
        if order(cand)==q-1:
            g=cand; break
    h=pow(g,(q-1)//n,q)          # generator of subgroup of order n
    S=[pow(h,i,q) for i in range(n)]
    assert len(set(S))==n
    return S

def poly_eval(coeffs, x, q):
    # coeffs low->high
    r=0
    for c in reversed(coeffs):
        r=(r*x+c)%q
    return r

def lagrange_interp(points, q):
    # points: list of (x,y); return coeff list (low->high) of interpolating poly
    n=len(points)
    coeffs=[0]*n
    for j in range(n):
        xj,yj=points[j]
        # basis poly numerator / denom
        num=[1]  # low->high
        den=1
        for m in range(n):
            if m==j: continue
            xm=points[m][0]
            # multiply num by (X - xm)
            newnum=[0]*(len(num)+1)
            for i,c in enumerate(num):
                newnum[i]=(newnum[i]+c*(-xm))%q
                newnum[i+1]=(newnum[i+1]+c)%q
            num=newnum
            den=(den*(xj-xm))%q
        inv=pow(den%q,q-2,q)
        scale=(yj*inv)%q
        for i,c in enumerate(num):
            coeffs[i]=(coeffs[i]+c*scale)%q
    return coeffs

def deg_lt_k_poly_through(points, q, k):
    """Return coeff(low->high, padded to len k) of the unique deg<k poly through
    exactly k points, or None if it doesn't exist / degree too high."""
    if len(points)!=k: return None
    c=lagrange_interp(points, q)
    # c has length k; deg<k automatically
    return c

def main():
    q=12289
    results=[]
    for n in [8,16]:
        D=subgroup(q,n)
        # rate ~1/4 style: k = n//4; t=1 so a=k+1, list ~ C(n,k+1)/q  (tiny here)
        # but the averaging count C(n,a)/q^t is the REVERSE bound. We instead do the
        # direct measurement: pick a non-degenerate received word u0 that has MANY
        # deg<k+1 explanations, count distinct leading coeffs and non-matchable ones.
        for k in [n//4, n//2]:
            if k<1: continue
            t=1
            a=k+t   # = k+1 agreement points -> deg<k+1 poly fixed by a points
            # witness threshold: need |S| >= a (so agreement on a points <=> deg<k+1 poly)
            # delta corresponds to (1-delta)n = a, i.e. delta = 1-a/n.
            # The averaging list reverse bound: choose u0 = eval of g = X^k*(X - c0)
            # (a degree k+1 word), the Round-5 explicit word. Then perturbations
            # pS = g - coeff_a(g)*nodal_S agree with g on the a points of S.
            # For the MONOMIAL stack we want u0 received word and count lifted polys.
            #
            # Construction realizing the averaging list at a NON-degenerate stack:
            # Take g0 = X^k * (X - c0), degree k+1, c0 in subgroup. u0 := eval(g0) on D.
            # For each a-subset S of D, the deg<a=k+1 interpolant qS through {(x, u0(x)): x in S}
            # agrees with u0 on S. Its leading (X^k) coeff = -gamma is a candidate bad scalar.
            c0=D[1]
            g0=[0]*(k+2)
            # g0 = X^{k+1} - c0 X^k
            g0[k+1]=1; g0[k]=(-c0)%q
            u0={x: poly_eval(g0,x,q) for x in D}
            # enumerate a-subsets (cap to keep it fast)
            subsets=list(itertools.combinations(D,a))
            total_sub=len(subsets)
            leading_coeffs={}   # gamma -> count of subsets producing it
            distinct_polys=set()
            for S in subsets:
                pts=[(x,u0[x]) for x in S]
                c=lagrange_interp(pts,q)   # length a = k+1, deg<k+1
                # leading coeff at degree k
                lead=c[k] if len(c)>k else 0
                gamma=(-lead)%q
                leading_coeffs.setdefault(gamma,0)
                leading_coeffs[gamma]+=1
                distinct_polys.add(tuple(c))
            # Now: which of these lifted polys give a TRUE mcaEvent, i.e. the pair
            # (u0, X^k) is NOT jointly matchable on S by a single codeword?
            # pairJointAgreesOn C S u0 u1: EXISTS w0,w1 in C (deg<k) with w0=u0 and w1=u1=X^k on S.
            # u1 = X^k restricted to S agrees with codeword w1 (deg<k) on S iff X^k|_S extends to deg<k poly.
            # Since X^k itself is degree k (NOT <k), generically NO deg<k poly agrees with X^k on k+1 pts.
            # So check: for each S (size a=k+1): is there a deg<k poly agreeing with u0 on S AND a deg<k poly agreeing with X^k on S?
            # joint-match needs BOTH rows simultaneously explainable by deg<k codewords on the SAME S.
            xk={x: pow(x,k,q) for x in D}
            mca_subsets=0
            explainable_u0_subsets=0  # deg<k+1 explanation exists (always, by interp) -> that's the line-witness
            for S in subsets:
                # row0: does a deg<k poly (a points determine deg<a poly; <k needs k pts) agree with u0 on all a=k+1 pts?
                # deg<k poly through k+1 points exists iff the unique deg<=k interpolant has zero leading coeff...
                # Actually: a deg<k poly agreeing with u0 on k+1 points exists iff interpolant of any k of them
                # also passes through the (k+1)th, i.e. the (k+1)-point data lies on a deg<k poly.
                pts=[(x,u0[x]) for x in S]
                ci=lagrange_interp(pts,q)  # deg < k+1
                row0_lowdeg = (len(ci)<=k or all(ci[j]==0 for j in range(k,len(ci))))
                pts1=[(x,xk[x]) for x in S]
                ci1=lagrange_interp(pts1,q)
                row1_lowdeg = (len(ci1)<=k or all(ci1[j]==0 for j in range(k,len(ci1))))
                # joint matchable on S <=> both rows are deg<k on S
                joint = row0_lowdeg and row1_lowdeg
                # mcaEvent: line u0+gamma*X^k matches a codeword (deg<k) on S AND NOT joint.
                # The line matches a deg<k codeword on S for the SPECIFIC gamma = leading-coeff-based value:
                # u0 + gamma*X^k = (deg<k poly) on S  <=>  qS = interp(u0) has leading coeff -gamma (always realizable, one gamma per S).
                # So for EACH S there's exactly one gamma making the line deg<k on S. That fires mcaEvent iff NOT joint.
                if not joint:
                    mca_subsets+=1
                explainable_u0_subsets+=1
            distinct_bad_gamma=len(leading_coeffs)
            # how many distinct gamma come from a NON-jointly-matchable S?
            bad_gammas=set()
            for S in subsets:
                pts=[(x,u0[x]) for x in S]
                ci=lagrange_interp(pts,q)
                row0_lowdeg = all(ci[j]==0 for j in range(k,len(ci)))
                pts1=[(x,xk[x]) for x in S]
                ci1=lagrange_interp(pts1,q)
                row1_lowdeg = all(ci1[j]==0 for j in range(k,len(ci1)))
                joint = row0_lowdeg and row1_lowdeg
                lead=ci[k] if len(ci)>k else 0
                gamma=(-lead)%q
                if not joint:
                    bad_gammas.add(gamma)
            avg_lb = -(-total_sub//(q**t))  # ceil C(n,a)/q^t  (= reverse bound, here C(n,a)/q)
            results.append(dict(n=n,k=k,a=a,delta=round(1-a/n,4),
                total_subsets=total_sub,
                avg_list_lb=avg_lb,
                distinct_lifted_polys=len(distinct_polys),
                distinct_leading_coeffs=distinct_bad_gamma,
                mca_firing_subsets=mca_subsets,
                distinct_bad_gamma=len(bad_gammas)))
    print("%-3s %-3s %-3s %-7s %-9s %-8s %-12s %-12s %-12s %-12s"%(
        "n","k","a","delta","totSub","avgLB","distPolys","distLeadCf","mcaSubs","distBadGam"))
    for r in results:
        print("%-3d %-3d %-3d %-7s %-9d %-8d %-12d %-12d %-12d %-12d"%(
            r['n'],r['k'],r['a'],r['delta'],r['total_subsets'],r['avg_list_lb'],
            r['distinct_lifted_polys'],r['distinct_leading_coeffs'],
            r['mca_firing_subsets'],r['distinct_bad_gamma']))

if __name__=="__main__":
    main()
