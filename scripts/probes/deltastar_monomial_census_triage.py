"""Far-monomial line-incidence triage for exact delta-star pins (#464).
For an explicit RS code C = RS[F, L, deg<k], computes the max over FAR monomial
pairs (X^a, X^b), a,b >= k, of the line-incidence #{gamma : (X^a + gamma X^b) agrees
with C on >= ceil((1-delta) n) points}.  This is an UPPER bound on eps_mca(C, delta);
where it stays below eps* = 1/2 the radius is good, giving a lower bracket for delta*.
Compare to the Johnson radius 1 - sqrt(rho) to see whether delta* lands ABOVE Johnson.
Predicts (2026-06-27): L2 RS[F13,ord6,deg2] and L4 RS[F11,ord5,deg1] above Johnson;
L1 RS[F17,ord8,deg2] (rate 1/4) borderline; L3 RS[F13,ord4,deg2] at capacity edge.
"""
import math, itertools
def census(F, Lset, k, label):
    L=sorted(Lset); n=len(L); rho=k/n
    C=[tuple((sum(c[j]*pow(xi,j,F) for j in range(k)))%F for xi in L)
       for c in itertools.product(range(F),repeat=k)]
    ma=lambda w: max(sum(w[i]==c[i] for i in range(n)) for c in C)
    mono=lambda a: tuple(pow(xi,a,F) for xi in L)
    J=1-math.sqrt(rho)
    print(f'--- {label}: n={n} rho={k}/{n} Johnson={J:.3f} cap={1-rho:.3f} ---')
    for t in range(n,0,-1):
        d=1-t/n; worst=0
        for a in range(k,n):
            for b in range(k,n):
                if a==b: continue
                u0,u1=mono(a),mono(b)
                worst=max(worst, sum(ma(tuple((u0[i]+g*u1[i])%F for i in range(n)))>=t for g in range(F)))
        rel='ABOVE' if d>J else ('AT' if abs(d-J)<1e-9 else 'below')
        print(f'  d={d:.3f}({rel}) line-inc={worst} eps={worst/F:.3f} {"BAD" if worst/F>0.5 else "good"}')
if __name__=='__main__':
    census(17,{1,2,4,8,16,15,13,9},2,'L1 F17 rate1/4')
    census(13,{4,3,12,9,10,1},2,'L2 F13 rate1/3')
    census(13,{5,12,8,1},2,'L3 F13 rate1/2')
    census(11,{3,9,5,4,1},1,'L4 F11 rate1/5')
