#!/usr/bin/env python3
"""Build and evaluate the four actual words on all 16,384 sites of the 8191^10 grid."""

from collections import Counter
from itertools import combinations

from probe_linear_contact_quotient import require
from probe_norm_one_elliptic_list import (INVERSE, P, SQUARES, add, curve_value, mul_ext,
                                          mul_poly, physical_coefficients, power_ext,
                                          short_quotient, subgroup_evaluations)


N = 2*(P+1)
D = 1023
CURVE = (3245,6342)
SHIFT = 6109
SLOPES = ((0,0),(1,0),(7443,1965),(7443,6226))
ROOTS = ((0,0),(7491,0),(6189,8059),(6189,132))
TARGETS = ((7491,0),(6189,8059),(6189,132),(6302,6245),(6302,1946),(2150,0))


def multiply_point(n,point,a):
    result = None
    while n:
        if n%2:
            result = add(result,point,a)
        point = add(point,point,a)
        n //= 2
    return result


def summands():
    a,b = CURVE
    square_roots = {v*v%P:v for v in range(P)}
    abscissas = [x for x in range(P) if curve_value(x,CURVE) in square_roots]
    require(1+sum(1 if curve_value(x,CURVE)==0 else 2 for x in abscissas)==8184,'source count')
    subgroup = {multiply_point(D,(x,square_roots[curve_value(x,CURVE)]),a) for x in abscissas}
    require(None in subgroup and len(subgroup)==8,'order-eight subgroup')
    subgroup.remove(None)
    quotient = ((a-5*sum(3*x*x+a for x,y in subgroup))%P,
                (b-7*sum(5*x**3+3*a*x+2*b for x,y in subgroup))%P)
    require(quotient==(4877,7687) and curve_value(SHIFT,quotient)==0,'quotient data')
    roots = {x for x,y in subgroup}
    kernel = {short_quotient(x,roots,CURVE) for x in abscissas}-{None}
    require(len(kernel)==511,'size of the abscissa set')
    return [(c,2*(3*c*c+quotient[0])%P,4*curve_value(c,quotient)%P) for c in sorted(kernel)]


def polynomial_sum(terms):
    """Add tau/(T-c)+omega/(T-c)^2 over the base field using a product tree."""
    if len(terms)==1:
        c,tau,omega = terms[0]
        return [(omega-c*tau)%P,tau],[c*c%P,-2*c%P,1]
    mid = len(terms)//2
    left,dl = polynomial_sum(terms[:mid])
    right,dr = polynomial_sum(terms[mid:])
    top = [(x+y)%P for x,y in zip(mul_poly(left,dr),mul_poly(right,dl))]
    return top,mul_poly(dl,dr)


def minus(left,right):
    return ((left[0]-right[0])%P,(left[1]-right[1])%P)


def inverse(z):
    x,y = z
    divisor = INVERSE[(x*x+y*y)%P]
    require(divisor!=0,'nonzero quadratic field denominator')
    return (x*divisor%P,-y*divisor%P)


def evaluate_projective(coeff,x):
    result = (0,0)
    for c in reversed(coeff):
        a,b = mul_ext(result,x)
        result = ((a+c)%P,b)
    return result


def verify():
    require(P**10//2**128==3 and (P**10-1)%N==0 and (N//16,D)==(1024,1023),'field and rate')
    top,den = polynomial_sum(summands())
    num = [0]+den.copy()
    for i,c in enumerate(top):
        num[i] = (num[i]+c)%P
    require(len(num)==D+1 and len(den)==D and num[-1]==1,'degrees of the pencil')
    # Scaling identifies the second half of the physical grid with Norm(x-SHIFT)=1741.
    scale = next(x for x in range(1,P) if x*x%P==(-1741)%P)
    square_roots = {y*y%P:y for y in range(P)}
    generator = next((x,square_roots[(-1-x*x)%P]) for x in range(P) if (-1-x*x)%P in SQUARES)
    require(power_ext(generator,N//2)==(P-1,0) and power_ext(generator,N)==(1,0),
            'exact physical generator order')
    def fft_values(polynomial):
        coeff = physical_coefficients(polynomial,D,SHIFT,scale)
        return subgroup_evaluations(coeff+[(0,0)]*(N-len(coeff)),generator)
    nvalues,dvalues = fft_values(num),fft_values(den)
    pairs = tuple(combinations(range(4),2))
    intercepts = [mul_ext(s,z) for s,z in zip(SLOPES,ROOTS)]
    targets = [mul_ext(minus(intercepts[i],intercepts[j]),inverse(minus(SLOPES[i],SLOPES[j])))
               for i,j in pairs]
    require(tuple(targets)==TARGETS and len(set(targets))==6,'six pairwise line intersections')
    ties,hits = Counter(),[0]*4
    private = 0
    u = (1,0)
    for j,(nv,dv) in enumerate(zip(nvalues,dvalues)):
        require((nv,dv)!=((0,0),(0,0)),'no base point on the grid')
        if j:
            den_cayley = minus((1,0),u)
            t = mul_ext((0,scale),mul_ext(((1+u[0])%P,u[1]),inverse(den_cayley)))
            x = ((SHIFT+t[0])%P,t[1])
            factor = power_ext(den_cayley,D)
            require(nv==mul_ext(factor,evaluate_projective(num,x)) and
                    dv==mul_ext(factor,evaluate_projective(den,x)),
                    'independent Horner check in the Cayley coordinate')
        else:
            require(nv==power_ext((0,2*scale%P),D) and dv==(0,0),'homogeneous infinity chart')
        quartet = [mul_ext(s,minus(nv,mul_ext(z,dv))) for s,z in zip(SLOPES,ROOTS)]
        equal = [(i,k) for i,k in pairs if quartet[i]==quartet[k]]
        if equal:
            require(len(equal)==1,'disjoint double sites')
            i,k = equal[0]
            ties[i,k] += 1
            received = quartet[i]
        else:
            received = quartet[private%4]
            private += 1
        for i,value in enumerate(quartet):
            hits[i] += int(value==received)
        u = mul_ext(u,generator)
    require(u==(1,0) and [ties[e] for e in pairs]==[D]*6,'all six complete fibers')
    require(hits==[5631,5631,5630,5630] and private==N-6*D,'four actual agreement counts')
    errors = N-min(hits)
    require(errors==10754 and 4*(N-errors+1)>N+6*D,'sharp list boundary')
    require(N//16+3*(3-1)<=N and N//16+4<=N,'MCA first failure three')
    print(f'{N:,} physical evaluations, six disjoint {D:,}-site equalities, word hits {hits}.')
    print(f'Field size {P**10}, budget three, first MCA failure 3 and first list failure {errors:,}.')


if __name__=='__main__':
    verify()
