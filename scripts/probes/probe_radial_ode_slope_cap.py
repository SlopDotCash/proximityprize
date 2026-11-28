#!/usr/bin/env python3
"""Check the ordinary radial slope cap using independent truncated implicit equations."""
from math import comb, factorial

from probe_quarter_coset_lists import require


def inverse_coefficients(k, cap, p):
    # Sum the coefficients of Z^k using multiplication in F_p[t]/(t^(cap+1)).
    Z = [0]*(cap+1)
    Z[1] = 1
    powers = [[0]*(cap+1) for _ in range(k+1)]
    powers[0][0] = 1
    for j in range(1,cap+1):
        for a in range(2,min(k,j)+1):
            powers[a][j] = sum(Z[i]*powers[a-1][j-i] for i in range(1,j))%p
        if j>1:
            Z[j] = -powers[k][j]%p
        powers[1][j] = Z[j]
    return Z


def controls():
    p = 101
    for d in range(1,30):
        for k in range(2,d+2):
            ell = (d+k-2)//(k-1)
            j = 1+(k-1)*ell
            coefficient = (-1)**ell*comb(j+ell-1,ell)*pow(j,-1,p)%p
            require(d<j and j+ell<=2*d+1 and coefficient, 'nonzero forbidden coefficient')
            require(inverse_coefficients(k,j,p)[j]==coefficient, 'direct inverse-series recurrence')
    # Solve an actual differential equation at each initial slope directly:
    # A=Y+3X²+4XY+5Y², B=X+2Y^k+3X²+7XY. The extra terms survive in
    # the finite slopes but drop out of the top coefficient under rescaling.
    for k in range(2,7):
        d = 8
        ell = (d+k-2)//(k-1)
        j = 1+(k-1)*ell
        slope_degree = j+ell
        values = []
        for slope in range(p):
            f = [0]*(j+1)
            f[1] = slope
            for h in range(2,j+1):
                f2 = [sum(f[i]*f[l-i] for i in range(1,l))%p for l in range(h+1)]
                fk = f2
                for _ in range(k-2):
                    fk = [sum(f[i]*fk[l-i] for i in range(1,l))%p for l in range(h+1)]
                def high_b(l):
                    return 2*fk[l]+3*(l==2)+7*f[l-1]
                residual = sum(high_b(l)*(h-l+1)*f[h-l+1] for l in range(2,h+1))
                residual -= 3*(h==2)+4*f[h-1]+5*f2[h]
                f[h] = -residual*pow(h-1,-1,p)%p
            values.append(f[j])
        for _ in range(slope_degree):
            values = [(b-a)%p for a,b in zip(values,values[1:])]
        c = 2*pow(k-1,-1,p)%p
        expected = factorial(slope_degree)*(-c)**ell*comb(j+ell-1,ell)*pow(j,-1,p)%p
        require(expected and set(values)=={expected}, 'degree and top coefficient at all slopes')
    print('435 inverse-series cases and 505 perturbed ODE slope trajectories passed over F_101.')


if __name__ == '__main__':
    controls()
