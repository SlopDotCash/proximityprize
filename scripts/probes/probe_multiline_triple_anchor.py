"""Exact two-region cube certificate for a triple-line anchor.

The structural proof is handwritten and the output is not a new threshold.
"""
from fractions import Fraction
import json


def main():
    n = 2**30
    D = n//2+1
    t = 221512374
    qmax = 3*t//2
    A = D-t
    B = n-D
    assert 0 < A <= qmax < n
    assert 7*t < 3*D
    # The region error cap is below its unconstrained uniform value.
    assert n*(qmax+t-D) <= t*qmax
    # The lower cube bound decreases over every allowed anchor size.
    assert qmax*(n-t) <= n*A
    gain = Fraction(A**3,qmax**2)+Fraction(B**3,(n-qmax)**2)-B
    assert gain > 0

    def feasible(s):
        return gain*s*s <= 3*t*s+(D-t)

    lo,hi = 0,n
    while lo < hi:
        mid = (lo+hi+1)//2
        if feasible(mid):
            lo = mid
        else:
            hi = mid-1
    assert feasible(lo) and not feasible(lo+1)
    assert lo < n-2
    m = n+1

    def cube_slack(radius):
        correction = 3*radius*m*m+(D-3*radius)*m
        return n*n*D*m**3+(m*(n-radius))**3-n**3*m**3-n*n*correction

    left,right = 0,n//4
    while left < right:
        mid = (left+right+1)//2
        if cube_slack(mid) > 0:
            left = mid
        else:
            right = mid-1
    assert cube_slack(left) > 0 and cube_slack(left+1) <= 0
    print(json.dumps({
        'scope': 'exact weighted cube arithmetic, universal proof handwritten',
        'length': n, 'distance': D, 'error_budget': t,
        'maximum_anchor_support': qmax,
        'maximum_external_witnesses_if_anchor_exists': lo,
        'maximum_total_witnesses_with_triple_anchor': lo+3,
        'cube_gain': str(gain),
        'first_excluded_external_count': lo+1,
        'no_triple_lines_in_overbudget_family': True,
        'conditional_line_free_cube_floor_numerator': left+1,
        'floor_denominator': n,
        'improvement_over_current_floor': left+1-221512374,
        'hypotheses': [
            'nonzero code differences between anchor and external heads',
            'error weight at most t', 'minimum distance at least D',
            'anchor support at most 3t/2',
            'outside-family cube deficit at most 3t*s^2+(D-t)*s'],
        'necessary_external_budget': 'gain*s^2 <= 3*t*s+(D-t)',
        'kernel_checked': False, 'new_production_floor': False,
    },indent=2))


if __name__ == '__main__':
    main()
