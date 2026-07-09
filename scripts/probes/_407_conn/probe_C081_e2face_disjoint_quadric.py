"""
C081 probe: the bad locus {e2=0, e1!=0} is DISJOINT from negation/coset structure,
and the attack_plan claim that the e2-face orbit count K is O(1) (quadric point count)
above delta*.

Three pieces, exact integer / mod-q arithmetic, PROPER dyadic subgroups mu_n.

(A) Disjointness (the genuine PROVEN content of C081): for char != 2,
    negation-closed S  ==>  e1(S)=0.  Hence e1(S)!=0 ==> S not negation-closed,
    and the bad locus {e2=0, e1!=0} never touches the antipodal/coset world.
    We verify exactly: (i) every (-1)-stable S (incl. coset unions of mu_d, d even)
    has e1=0; (ii) the bad locus {e2=0, e1!=0} is NONEMPTY at proper dyadic mu_n
    (so the redirection is non-vacuous); (iii) NO element of the bad locus is
    negation-closed (disjointness, exact).

(B) The attack_plan claim: the e2=0 bad-scalar locus, parametrized by the
    "complement quadric" + dilation orbits, has K = #orbits = O(1) above delta*.
    We compute K = #{ e2(S) : S subseteq mu_n, |S|=k+2, e1(S)!=0, e2(S)=0 ... }
    Actually the bad SCALAR alpha = -1/e1(S) on the e2=0 face; the bad-scalar
    set is dilation-orbit-closed, K = #(bad scalars)/n.  We measure how K scales
    with n at fixed rate (rho=1/4, 1/2) and across the agreement a=k+t window,
    to test O(1) vs growth.

    Here the "e2=0 face" means: for the ladder at agreement a=k+2, the bad locus
    is {S subseteq mu_n : |S|=k+2, e1(S)!=0, e2(S)=0} and the bad scalar is
    alpha = -e1(S)/e2... -- we follow the comment-57 def: bad scalar exists when
    e2(S)=0, e1(S)!=0, alpha = -1/e1(S).  The bad-scalar set B = {-1/e1(S)}.

(C) The "quadric point count": #{S : e2(S)=0} over mu_n -- does it grow like
    a quadric variety point count Theta(n^{|S|-1}) (so K ~ n^{...}/n grows), or
    is it O(1)?  This is the load-bearing magnitude the attack_plan needs O(1).
"""
import itertools, sys

def sieve_primes_upto(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]:
            s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(2,N+1) if s[i]]

PRIMES = sieve_primes_upto(5_000_000)

def find_prime(n, beta, used=()):
    """find a prime q == 1 mod n, q ~ n^beta, q-1 NOT a power of 2 (so a real
    proper subgroup, multiple-primes flavor), q > n (proper subgroup)."""
    target = int(round(n**beta))
    # search near target for q = 1 mod n
    best=None
    for q in PRIMES:
        if q < n*4: continue
        if (q-1) % n != 0: continue
        # require (q-1)/n has an odd factor > 1 sometimes; just avoid q-1 power of 2
        m=q-1
        while m%2==0: m//=2
        if m==1:  # q-1 is power of 2 -> too special
            continue
        if q in used: continue
        if best is None or abs(q-target) < abs(best-target):
            best=q
        if q>target and best is not None and best>=target:
            break
    return best

def primitive_root(q):
    # find generator of F_q^*
    from sympy import primitive_root as pr
    return pr(q)

def mu_n(q, n, g_full):
    # g_full primitive root mod q; generator of mu_n is g_full^{(q-1)/n}
    gen = pow(g_full, (q-1)//n, q)
    elts = []
    x=1
    for _ in range(n):
        elts.append(x); x=(x*gen)%q
    return elts, gen

def e_symm(subset, q, j):
    # elementary symmetric polynomial e_j of subset mod q (subset = list of residues)
    # dp
    e = [0]*(j+1); e[0]=1
    for x in subset:
        for i in range(min(j,len(e)-1),0,-1):
            e[i]=(e[i]+e[i-1]*x)%q
    return e[j]

def is_neg_closed(subset_set, q):
    return all((q-x)%q in subset_set for x in subset_set)

def main():
    print("="*78)
    print("C081: e2=0 bad locus DISJOINT from negation/coset; attack_plan K=O(1) test")
    print("="*78)
    try:
        from sympy import primitive_root
    except Exception as e:
        print("need sympy:",e); sys.exit(1)

    # ---- (A) disjointness + non-vacuity, exact, small dyadic n ----
    print("\n--- (A) Disjointness of bad locus {e2=0,e1!=0} from negation-closed ---")
    print(f"{'n':>4} {'q':>9} {'a':>3} | {'#e2=0':>7} {'#bad(e1!=0)':>11} "
          f"{'#bad&negclosed':>14} {'#negclosed_in_e2=0':>18}")
    for n, beta in [(8,4),(16,4),(8,4.5)]:
        q = find_prime(n,beta)
        if q is None:
            print(f"  n={n}: no prime found"); continue
        g = primitive_root(q)
        elts, gen = mu_n(q,n,g)
        elts_set=set(elts)
        k = n//4  # rho=1/4
        for a in [k+2]:  # agreement = k+2, the e2-ladder face
            n_e2zero=0; n_bad=0; n_bad_negclosed=0; n_negclosed_e2zero=0
            for S in itertools.combinations(elts, a):
                if e_symm(S,q,2)!=0: continue
                n_e2zero+=1
                Sset=set(S)
                nc = is_neg_closed(Sset,q)
                if nc: n_negclosed_e2zero+=1
                e1=e_symm(S,q,1)
                if e1!=0:
                    n_bad+=1
                    if nc: n_bad_negclosed+=1
            print(f"{n:>4} {q:>9} {a:>3} | {n_e2zero:>7} {n_bad:>11} "
                  f"{n_bad_negclosed:>14} {n_negclosed_e2zero:>18}")

    # ---- (B/C) the K = #bad-scalar / n  scaling, and the e2=0 quadric point count ----
    print("\n--- (B/C) bad-scalar orbit count K and e2=0 'quadric' point count ---")
    print("  bad scalar alpha = -1/e1(S) on the e2=0,e1!=0 face; B={alpha}; K=|B|/?")
    print("  Also #{S:e2(S)=0} = the complement-quadric point count over mu_n.")
    print(f"{'n':>4} {'q':>9} {'a':>3} {'rho':>5} | {'#e2=0':>8} {'#bad':>7} "
          f"{'#distinct alpha':>15} {'K=#alpha/n':>10} {'#alpha%n':>8}")
    for n, beta, rho in [(8,4,0.25),(16,4,0.25),(8,4,0.5),(16,4,0.5),(32,4,0.5)]:
        q = find_prime(n,beta)
        if q is None:
            print(f"  n={n}: no prime"); continue
        g = primitive_root(q)
        elts, gen = mu_n(q,n,g)
        k=int(round(rho*n))
        a=k+2
        if a>n:
            continue
        ncomb = 1
        # combinations count guard
        from math import comb
        if comb(n,a) > 60_000_000:
            print(f"{n:>4} {q:>9} {a:>3} {rho:>5} |  (C({n},{a})={comb(n,a)} too big, skip)")
            continue
        n_e2zero=0; n_bad=0; alphas=set()
        for S in itertools.combinations(elts,a):
            if e_symm(S,q,2)!=0: continue
            n_e2zero+=1
            e1=e_symm(S,q,1)
            if e1!=0:
                n_bad+=1
                alpha=(-pow(e1,q-2,q))%q  # -1/e1 mod q
                alphas.add(alpha)
        na=len(alphas)
        Kfrac = na/n
        print(f"{n:>4} {q:>9} {a:>3} {rho:>5} | {n_e2zero:>8} {n_bad:>7} "
              f"{na:>15} {Kfrac:>10.3f} {na%n:>8}")

    # ---- (D) does #{S:e2(S)=0} (the 'quadric') grow like a variety point count? ----
    print("\n--- (D) e2=0 'quadric' point count growth in n (at fixed small a) ---")
    print("  attack_plan needs O(1); a genuine quadric over mu_n^a has ~ n^{a-1} points")
    print(f"{'n':>5} {'q':>9} {'a':>3} | {'#e2=0':>10} {'#e2=0/n^(a-1)':>14}")
    for a in [3,4]:
        for n, beta in [(8,4),(16,4),(32,4),(64,4)]:
            from math import comb
            if comb(n,a) > 60_000_000:
                print(f"{n:>5} {'-':>9} {a:>3} |  (C({n},{a})={comb(n,a)} too big)")
                continue
            q = find_prime(n,beta)
            if q is None: continue
            g = primitive_root(q)
            elts,gen = mu_n(q,n,g)
            cnt=0
            for S in itertools.combinations(elts,a):
                if e_symm(S,q,2)==0: cnt+=1
            denom = n**(a-1)
            print(f"{n:>5} {q:>9} {a:>3} | {cnt:>10} {cnt/denom:>14.4f}")

if __name__=="__main__":
    main()
