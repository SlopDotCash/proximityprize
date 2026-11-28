#!/usr/bin/env python3
"""Test the cancellation at singular slope parameters by nonexceptional Taylor evaluations."""
from probe_quarter_coset_lists import poly_mul, require


def coefficients(s, cap, p):
    # q=z²(z−1)+X(z+1), P=z−1+Xz. The root 0 of q is transverse.
    # At the simple root 1 of q the numerator also vanishes.
    z = [s]+[0]*cap
    for j in range(1,cap+1):
        z2 = poly_mul(z,z,p)
        z3 = poly_mul(z2,z,p)
        q = [(z3[a]-z2[a]+(z[a-1]+int(a==1) if a else 0))%p for a in range(j)]
        rhs = z[j-1]-int(j==1)+(z[j-2] if j>=2 else 0)
        known = sum(q[a]*(j-a)*z[j-a] for a in range(1,j))
        z[j] = (rhs-known)*pow(j*q[0],-1,p)%p
    return z


def controls():
    p, cap = 101, 9
    samples = {s: coefficients(s,cap,p) for s in range(2,p)}
    for j in range(1,cap+1):
        values = [coeff[j]*pow(s,3*j-1,p)*pow(s-1,j-1,p)%p for s,coeff in samples.items()]
        # Shift the interpolation grid backwards twice to recover the
        # numerator at zero. A genuine transverse root gives a nonzero value.
        leading = []
        row = values
        for _ in range(6*j):
            leading.append(row[0])
            row = [(b-a)%p for a,b in zip(row,row[1:])]
        require(not any(row), 'numerator has degree at most 6j−1')
        at_zero = sum((-1)**k*(k+1)*c for k,c in enumerate(leading))%p
        require(at_zero, 'exact order 3j−1 at the transverse root')
    print('891 Taylor coefficient samples verify transverse and cancelled directions through order nine.')


if __name__ == '__main__':
    controls()
