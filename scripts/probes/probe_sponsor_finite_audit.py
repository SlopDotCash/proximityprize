"""Independent compressed sponsor arithmetic and finite moment budgets.

Production construction arithmetic is certified without enumerating its domain.
Moment orders above three are research inequalities, not Lean theorems.
All certificate checks remain active under Python optimization.
Author: Mikhail Izhutkin (@mashingaan).
"""
from fractions import Fraction
from math import factorial
import json

N = 1073741824
K = 536870912
Q = 340282366920938463463374607431768211456
P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478


def require(condition, detail):
    """Keep certificate checks active under -O, -OO, and PYTHONOPTIMIZE."""
    if not condition:
        raise AssertionError(detail)


def mod_exp(base, exponent, modulus):
    value = 1
    for bit in bin(exponent)[2:]:
        value = value * value % modulus
        if bit == '1':
            value = value * base % modulus
    return value


def construction_arithmetic():
    c = K - 2
    a, leftover = divmod(N - c, 3)
    core = c + a
    support = core + 1
    count = 3 * (N - core)
    residues = [mod_exp(v, N, P) for v in range(1, 6)]
    require(len(set(residues)) == 5,
            'coefficient power residues must be distinct')
    require(mod_exp(G, N, P) == 1,
            'production generator must lie in the order-N subgroup')
    require(mod_exp(G, N // 2, P) != 1,
            'production generator must have exact order N')
    require(K <= core and c + 1 < K,
            'K <= core and c + 1 < K')
    require(count == N + 5 and count * Q > P,
            'count == N + 5 and count * Q > P')
    radius = Fraction(N - support, N)
    require(radius == Fraction(178956971, 536870912),
            'radius == Fraction(178956971, 536870912)')
    return dict(n=N, dimension=K, prime=P, generator=G,
                common=c, group=a, leftover=leftover, core=core,
                exact_support=support, maximum_head_degree=c + 1,
                radius=str(radius), distinct_scalars=count,
                strict_error_slack=count * Q - P,
                coefficient_power_residues=residues,
                evidence='arithmetic certificate only, Lean upper theorem is audited separately')


def finite_interpolation():
    n, k, p, g = 128, 64, 1409, 1022
    require(mod_exp(g, n, p) == 1,
            'mod_exp(g, n, p) == 1')
    require(mod_exp(g, n // 2, p) != 1,
            'mod_exp(g, n // 2, p) != 1')
    c = k - 2
    a = (n - c) // 3
    xs = [mod_exp(g, i, p) for i in range(n)]
    require(len(set(xs)) == n,
            'len(set(xs)) == n')
    roots = xs[:c]
    zs = []
    for x in xs:
        z = 1
        for root in roots:
            z = z * (x - root) % p
        zs.append(z)
    hs = [3 if i < c or i >= c + 3*a else (i-c)//a for i in range(n)]
    row0 = [h*h*z*x % p for h,z,x in zip(hs,zs,xs)]
    row1 = [h*z % p for h,z in zip(hs,zs)]

    def lagrange(indices, values, x):
        answer = 0
        for i in indices:
            numerator, denominator = 1, 1
            for j in indices:
                if i != j:
                    numerator = numerator * (x-xs[j]) % p
                    denominator = denominator * (xs[i]-xs[j]) % p
            answer = (answer + values[i]*numerator*pow(denominator,-1,p)) % p
        return answer

    seen = set()
    for head in range(3):
        core = list(range(c)) + list(range(c + head*a, c + (head+1)*a))
        basis = core[:k]
        require(len(core) >= k,
                'len(core) >= k')
        head1 = [lagrange(basis,row1,x) for x in xs]
        head0 = [lagrange(basis,row0,x) for x in xs]
        for i in range(n):
            if i in core:
                continue
            denominator = (row1[i]-head1[i]) % p
            require(denominator != 0,
                    'denominator != 0')
            gamma = -(row0[i]-head0[i])*pow(denominator,-1,p) % p
            support = {j for j in range(n)
                       if (row0[j]+gamma*row1[j]-head0[j]-gamma*head1[j]) % p == 0}
            require(support == set(core + [i]),
                    'support == set(core + [i])')
            require(gamma not in seen,
                    'gamma not in seen')
            seen.add(gamma)
    require(len(seen) == 3*(n-c-a),
            'len(seen) == 3*(n-c-a)')
    return dict(n=n,dimension=k,prime=p,generator=g,
                exact_support=c+a+1,distinct_scalars=len(seen),
                evidence='independent direct interpolation on a finite instance only')


def falling(m, r):
    answer = 1
    for j in range(r):
        answer *= m-j
    return answer


def multiplicity_partitions(r, lower=1):
    if r == 0:
        yield ()
    for first in range(lower,r+1):
        for tail in multiplicity_partitions(r-first,first):
            yield (first,) + tail


def repetition_inventory(m, r):
    rows = []
    for partition in multiplicity_partitions(r):
        denominator = 1
        for multiplicity in partition:
            denominator *= factorial(multiplicity)
        for multiplicity in set(partition):
            denominator *= factorial(partition.count(multiplicity))
        numerator = falling(m,len(partition))*factorial(r)
        require(numerator % denominator == 0,
                'numerator % denominator == 0')
        rows.append(dict(partition=partition,ordered_tuples=numerator//denominator))
    require(sum(row['ordered_tuples'] for row in rows) == m**r,
            "sum(row['ordered_tuples'] for row in rows) == m**r")
    require(sum(row['ordered_tuples'] for row in rows if len(row['partition']) < r) == m**r-falling(m,r),
            'repeated tuples must match the falling-factorial complement')
    return rows


def best_block(m, r):
    def cost(s):
        return Fraction(r*m**r,s) + s**(r-2)*m*m
    lo, hi = 2, m
    while lo < hi:
        mid = (lo+hi)//2
        if cost(mid+1) >= cost(mid):
            hi = mid
        else:
            lo = mid+1
    s = min(range(max(2,lo-2),min(m,lo+2)+1),key=cost)
    require(cost(s) <= cost(s+1),
            'cost(s) <= cost(s+1)')
    if s > 2:
        require(cost(s) <= cost(s-1),
                'cost(s) <= cost(s-1)')
    return s


def moment_slack(t, r, s):
    m, d = N+1, K
    # Ordered distinct collinear tuples use the block-decomposition budget.
    collinear_s = s*m*(t+1)**(r-1) + r*m**r + s**(r-1)*m*m
    return (s*N**(r-1)*(d+1)*falling(m,r) + s*(m*(N-t))**r
            - s*N**r*m**r - N**(r-1)*(d+1)*collinear_s)


def moment_frontier(r):
    s = best_block(N+1,r)
    lo, hi = 0, K
    while lo < hi:
        mid = (lo+hi+1)//2
        if moment_slack(mid,r,s) > 0:
            lo = mid
        else:
            hi = mid-1
    require(moment_slack(lo,r,s) > 0,
            'moment_slack(lo,r,s) > 0')
    require(moment_slack(lo+1,r,s) <= 0,
            'moment_slack(lo+1,r,s) <= 0')
    return dict(order=r,block=s,max_error=lo,lattice_floor=str(Fraction(lo+1,N)),
                strict_slack=moment_slack(lo,r,s),
                next_slack=moment_slack(lo+1,r,s),
                repeated_tuples=(N+1)**r-falling(N+1,r),
                multiplicity_partitions=repetition_inventory(N+1,r),
                evidence='exact optimization of stated budget, no optimality claim for all moments')


def weighted_slack(t, s, cap=None):
    m, d = N+1, K
    b = t+1 if cap is None else cap
    penalty = (s*m*b**2*(d+1-b)
               + (d+1)*(3*m**3+s*s*m*m+3*s*m*m))
    return (s*N*N*(d+1)*m**3+s*(m*(N-t))**3
            -s*N**3*m**3-N*N*penalty)


def weighted_frontier(exterior=False):
    s = best_block(N+1,3)
    def slack(t):
        b = min(t+1,max(3*t-K,0)+1) if exterior else t+1
        return weighted_slack(t,s,b)
    lo, hi = 0, K//2
    while lo < hi:
        mid = (lo+hi+1)//2
        if slack(mid) > 0:
            lo = mid
        else:
            hi = mid-1
    require(slack(lo) > 0,
            'slack(lo) > 0')
    require(slack(lo+1) <= 0,
            'slack(lo+1) <= 0')
    require(3*(lo+1) <= 2*(K+1),
            '3*(lo+1) <= 2*(K+1)')
    return dict(block=s,max_error=lo,lattice_floor=str(Fraction(lo+1,N)),
                improvement_steps=lo-210683555,
                strict_slack=slack(lo),next_slack=slack(lo+1),
                line_cap=min(lo+1,max(3*lo-K,0)+1) if exterior else lo+1,
                evidence='arithmetic certificate only, canonical Lean floor is audited separately')


def constant_line_frontier():
    m, distance = N+1, K+1
    def slack(t):
        return (N*N*distance*m**3+(m*(N-t))**3
                -N**3*m**3-N*N*(4*t*m*m+distance*m))
    lo, hi = 0, K//2
    while lo < hi:
        mid = (lo+hi+1)//2
        if slack(mid) > 0:
            lo = mid
        else:
            hi = mid-1
    require(slack(lo) > 0 and slack(lo+1) <= 0,
            'slack(lo) > 0 and slack(lo+1) <= 0')
    require(7*lo < 3*distance,
            '7*lo < 3*distance')
    return dict(max_error=lo,line_cap=3,
                lattice_floor=str(Fraction(lo+1,N)),
                improvement_steps_over_exterior=lo+1-218759456,
                strict_slack=slack(lo),next_slack=slack(lo+1),
                evidence='arithmetic certificate only, constant-line Lean transfer checked separately')


def refined_degeneracy_candidate():
    """Arithmetic only, pair-union and refined mass transfer are not Lean checked."""
    m, distance = N+1, K+1
    def slack(t):
        correction = 4*t*m*m+(distance-2*t)*m
        return (N*N*distance*m**3+(m*(N-t))**3
                -N**3*m**3-N*N*correction)
    lo, hi = 0, K//2
    while lo < hi:
        mid = (lo+hi+1)//2
        if slack(mid) > 0:
            lo = mid
        else:
            hi = mid-1
    require(slack(lo) > 0 and slack(lo+1) <= 0,
            'slack(lo) > 0 and slack(lo+1) <= 0')
    require(2*lo < distance and 7*lo < 3*distance,
            '2*lo < distance and 7*lo < 3*distance')
    return dict(max_error=lo, candidate_floor=str(Fraction(lo+1,N)),
                strict_slack=slack(lo), next_slack=slack(lo+1),
                required_lemmas=['pair error union at least distance minus t',
                                 'cube deficit at most 4*t*m^2+(distance-2*t)*m'],
                evidence='conditional arithmetic candidate, no new canonical floor claimed')


if __name__ == '__main__':
    moments = [moment_frontier(r) for r in range(3,7)]
    require(moments[0]['max_error'] == 210683555,
            "moments[0]['max_error'] == 210683555")
    require(all(moments[i+1]['max_error'] < moments[i]['max_error']
               for i in range(len(moments)-1)),
            'higher-order moment budgets must strictly weaken this floor')
    print(json.dumps(dict(construction=construction_arithmetic(),
                          finite=finite_interpolation(),moment_budgets=moments,
                          weighted_triples=weighted_frontier(),
                          exterior_line_triples=weighted_frontier(True),
                          constant_line_triples=constant_line_frontier(),
                          refined_degeneracy_candidate=refined_degeneracy_candidate()),indent=2))
