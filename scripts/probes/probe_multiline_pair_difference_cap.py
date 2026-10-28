"""Exact arithmetic for the global pair-difference cap on three-head pencils.

Structural hypotheses and the summation proof remain handwritten.
"""
import json


def main():
    checked = 0
    for L in range(1,65):
        for a in range(L+1):
            for k in range(a+1):
                e = 3*a-k
                B = 3*L*(L-1)-3*(L-a)*(L-a-1)-k*(L-a)
                d = a-k
                gap = (5*L-2)*e-e*e-2*B
                assert gap == d*(3*L-2*a-d)+2*k
                assert gap >= 0
                checked += 1
    n = 2**30
    D = n//2+1
    m = n+1

    def cap(t):
        denominator = 2*D*n-5*t*n+3*t*t
        if denominator <= 0:
            return m//3
        return min(m//3,2*n*(D-t)//denominator)

    def slack(t):
        correction = 3*t*m*m+(D-3*t)*m+6*t*cap(t)
        return n*n*D*m**3+(m*(n-t))**3-n**3*m**3-n*n*correction

    lo,hi = 0,n//4
    while lo < hi:
        mid = (lo+hi+1)//2
        if slack(mid) > 0:
            lo = mid
        else:
            hi = mid-1
    assert slack(lo) > 0 and slack(lo+1) <= 0
    t = 221512374
    bound = cap(t)
    assert bound == 6
    overbudget_lines = (n+3)//3
    assert overbudget_lines > bound
    assert 7*t < 3*D and 2*t <= n
    assert 2*(2*5*8-5*2*8+3*2*2) <= 2*8*(5-2)
    assert 3*(2*5*9-5*2*9+3*2*2) <= 2*9*(5-2)
    print(json.dumps({
        'coordinate_cases_checked': checked,
        'coordinate_identity': '(5L-2)e-e^2-2B=(a-k)(3L-3a+k)+2k',
        'global_inequality': 'L*(2Dn-5tn+3t^2)<=2n*(D-t)',
        'length': n, 'distance': D, 'error_budget': t,
        'maximum_three_head_pencils': bound,
        'maximum_ordered_distinct_collinear_triples': 6*bound,
        'previous_scalar_ledger_lines': overbudget_lines,
        'previous_scalar_ledger_excluded_by_pair_differences': True,
        'conditional_cube_max_error': lo,
        'conditional_cube_floor_numerator': lo+1,
        'floor_denominator': n,
        'improvement_over_current_floor': lo+1-221512374,
        'strict_slack': slack(lo), 'next_slack': slack(lo+1),
        'hypotheses': ['nonzero pairwise affine codeword differences',
                       'three distinct scalar heads per pencil',
                       'each selected error weight at most t',
                       '2t<=n', 'distance at least D',
                       'cap three and disjoint triple blocks for cube transfer'],
        'scope': 'exact arithmetic and coordinate identity checks, universal argument handwritten',
        'kernel_checked_global_cap': False,
        'new_production_floor': False,
    },indent=2))


if __name__ == '__main__':
    main()
