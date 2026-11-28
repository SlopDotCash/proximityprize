#!/usr/bin/env python3
"""Build the four actual words witnessing the exact list threshold on the 8192-point norm-one grid."""
from itertools import combinations
from math import isqrt

from probe_linear_contact_quotient import require


P = 8191
N = P+1
DEGREE = 511
INVERSE = [0]+[pow(x,-1,P) for x in range(1,P)]
SQUARES = {x*x % P for x in range(P)}
TARGETS = (903,2163,3378,5911,4002,3435)
LINES = ((0,0),(1,-903),(1942,-1942*2163),(5400,-5400*3378))
CURVE = (2794,2628)
GENERATOR = (5911,2328)


def curve_value(x, curve):
    a,b = curve
    return (x**3+a*x+b)%P


def add(left, right, a):
    if left is None:
        return right
    if right is None:
        return left
    x,y = left
    u,v = right
    if x==u and (y+v)%P==0:
        return None
    if x==u:
        slope = (3*x*x+a)*INVERSE[2*y%P] % P
    else:
        slope = (v-y)*INVERSE[(u-x)%P] % P
    z = (slope*slope-x-u)%P
    return z,(slope*(x-z)-y)%P


def short_quotient(x, roots, curve):
    total = x
    for root in roots:
        if root==x:
            return None
        y2 = curve_value(root,curve)
        slope = (1 if y2==0 else 2)*(3*root*root+curve[0])
        inverse = INVERSE[(x-root)%P]
        total += (slope+4*y2*inverse)*inverse
    return total%P


def kernel_abscissas():
    require(GENERATOR[1]**2%P==curve_value(GENERATOR[0],CURVE),'starting point')
    point = None
    subgroup = []
    for _ in range(16):
        point = add(point,GENERATOR,CURVE[0])
        if point is not None:
            subgroup.append(point)
    require(point is None and len(set(subgroup))==15,'cyclic order sixteen')
    roots = {x for x,y in subgroup}
    curve = ((CURVE[0]-5*sum(3*x*x+CURVE[0] for x,y in subgroup))%P,
             (CURVE[1]-7*sum(5*x**3+3*CURVE[0]*x+2*CURVE[1] for x,y in subgroup))%P)
    require(curve==(3076,286),'second curve')
    rational_x = [x for x in range(P) if curve_value(x,CURVE) in SQUARES]
    num_points = 1+sum(1 if curve_value(x,CURVE)==0 else 2 for x in rational_x)
    require(num_points==8176,'first curve point count')
    kernel = {short_quotient(x,roots,CURVE) for x in rational_x}
    kernel.remove(None)
    require(len(kernel)==255 and all(curve_value(x,curve) in SQUARES-{0} for x in kernel),
            'abscissas for the degree-511 polynomial')
    return sorted(kernel),curve


def mul_poly(left,right):
    result = [0]*(len(left)+len(right)-1)
    for i,u in enumerate(left):
        for j,v in enumerate(right):
            result[i+j] += u*v
    return [c%P for c in result]


def polynomial_pair():
    roots,curve = kernel_abscissas()
    product = [1]
    for c in roots:
        product = mul_poly(product,[-c,1])
    denominator = mul_poly(product,product)
    numerator = [0]+denominator.copy()
    for c in roots:
        quotient = [0]*(len(product)-1)
        quotient[-1] = product[-1]
        for i in range(len(quotient)-2,-1,-1):
            quotient[i] = (product[i+1]+c*quotient[i+1])%P
        require((product[0]+c*quotient[0])%P==0,'synthetic division')
        square = mul_poly(quotient,quotient)
        v = 2*(3*c*c+curve[0])%P
        w = (4*curve_value(c,curve)-c*v)%P
        for i,b in enumerate(square):
            numerator[i] += w*b
            numerator[i+1] += v*b
    numerator = [c%P for c in numerator]
    require(len(numerator)==512 and numerator[-1]==1 and len(denominator)==511,'degrees')
    return numerator,denominator


def evaluate(coefficients,x):
    if x is None:
        return coefficients[-1] if len(coefficients)==DEGREE+1 else 0
    result = 0
    for c in reversed(coefficients):
        result = (result*x+c)%P
    return result


def mul_ext(left,right):
    x,y = left
    u,v = right
    return ((x*u-y*v)%P,(x*v+y*u)%P)


def power_ext(x,n):
    result = (1,0)
    while n:
        if n%2:
            result = mul_ext(result,x)
        x = mul_ext(x,x)
        n //= 2
    return result


def physical_coefficients(coefficients,degree=DEGREE,shift=0,scale=1):
    """Homogenize to the given degree and substitute shift+scale*i*(1+U)/(1-U)."""
    padded = coefficients+[0]*(degree+1-len(coefficients))
    result = [(padded[-1],0)]
    denominator = [1]
    for coefficient in reversed(padded[:-1]):
        denominator = [(a-b)%P for a,b in zip(denominator+[0],[0]+denominator)]
        result = [((coefficient*d+shift*(x-u)-scale*(y+v))%P,
                   (shift*(y-v)+scale*(x+u))%P)
                  for (x,y),(u,v),d in zip(result+[(0,0)],[(0,0)]+result,denominator)]
    return result


def subgroup_evaluations(coefficients,generator):
    """Evaluate the ordinary coefficient vector on successive powers of the generator."""
    if len(coefficients)==1:
        return coefficients
    square = mul_ext(generator,generator)
    even = subgroup_evaluations(coefficients[::2],square)
    odd = subgroup_evaluations(coefficients[1::2],square)
    left,right = [],[]
    power = (1,0)
    for (x,y),value in zip(even,odd):
        u,v = mul_ext(power,value)
        left.append(((x+u)%P,(y+v)%P))
        right.append(((x-u)%P,(y-v)%P))
        power = mul_ext(power,generator)
    return left+right


def verify_expanded_words(numerator,denominator,projective_values):
    generator = next(u for u in projective_values if power_ext(u,N//2)==(P-1,0))
    require(power_ext(generator,N)==(1,0),'physical generator order')
    def evaluate_grid(poly):
        coeff = physical_coefficients(poly)
        return subgroup_evaluations(coeff+[(0,0)]*(N-len(coeff)),generator)
    numerator_values = evaluate_grid(numerator)
    denominator_values = evaluate_grid(denominator)
    u = (1,0)
    for (x,y),(z,w) in zip(numerator_values,denominator_values):
        quartet = [((a*x+b*z)%P,(a*y+b*w)%P) for a,b in LINES]
        require(quartet==projective_values[u],'physical polynomial coefficients and all four words')
        u = mul_ext(u,generator)
    require(u==(1,0),'closed physical subgroup enumeration')


def check():
    require(all(P%d for d in range(2,isqrt(P)+1)) and P%4==3,'prime field and quadratic extension')
    require(P**10//2**128==3 and P**10<2**256 and (P**10-1)%N==0,'field and secure budget')
    numerator,denominator = polynomial_pair()
    targets = [(v-b)*INVERSE[(a-u)%P]%P for (a,b),(u,v) in combinations(LINES,2)]
    require(tuple(targets)==TARGETS,'all six line intersections')
    words = [[] for _ in LINES]
    center = []
    grid = {}
    tie_counts = dict.fromkeys(TARGETS,0)
    private = 0
    for t in [None]+list(range(P)):
        x,y = evaluate(numerator,t),evaluate(denominator,t)
        require((x,y)!=(0,0),'defined map on the whole grid')
        if t is None:
            u = (1,0)
            scale = power_ext((0,2),DEGREE)
        else:
            divisor = INVERSE[(t*t+1)%P]
            u = (((t*t-1)*divisor)%P,(-2*t*divisor)%P)
            scale = power_ext(((1-u[0])%P,(-u[1])%P),DEGREE)
        require((u[0]*u[0]+u[1]*u[1])%P==1 and scale!=(0,0),'norm-one transform')
        vals = [mul_ext(scale,((a*x+b*y)%P,0)) for a,b in LINES]
        grid[u] = vals
        for w,v in zip(words,vals):
            w.append(v)
        proj = x*INVERSE[y]%P if y else None
        pairs = [(i,j) for i,j in combinations(range(4),2) if vals[i]==vals[j]]
        if proj in tie_counts:
            require(len(pairs)==1,'one simple pair at each marked site')
            tie_counts[proj]+=1
            center.append(vals[pairs[0][0]])
        else:
            require(not pairs,'no other collisions')
            center.append(vals[private%4])
            private+=1
    require(len(grid)==8192 and all(x==511 for x in tie_counts.values()),'six full disjoint fibers')
    verify_expanded_words(numerator,denominator,grid)
    hits = [sum(x==y for x,y in zip(w,center)) for w in words]
    require(len(set(map(tuple,words)))==4 and sorted(hits)==[2814,2814,2815,2815],'four words')
    require(4*2815>N+6*DEGREE and N-min(hits)==5378,'matching safety and failure')
    require(512+3*(3-1)<=N and 512+3+1<=N,'MCA staircase and spike boundary at three')
    print('On the same code the MCA first failure is 3 errors.')
    print(f'Field order {P**10}, list budget 3. All {len(grid):,} norm-one sites checked.')
    print(f'Six fibers each have 511 sites. Actual word agreements: {hits}.')
    print('At dimension 512 the last safe error count is 5,377 and first failure is 5,378.')


if __name__=='__main__':
    check()
