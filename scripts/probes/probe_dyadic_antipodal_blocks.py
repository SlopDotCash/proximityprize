#!/usr/bin/env python3
"""Certify the four-site constraint on order 256 and weighted order-64 comparisons."""
import argparse
import json
from math import comb
from pathlib import Path

from flint import fmpz_mat

from probe_mu128_unit_ellipsoid import (
    FACTOR_TABLE, PRIMES, certify_prime, check_shift, exponent_rows, kernel_basis,
)
from probe_mu64_unit_lattice import lattice_coordinates, orthogonal_lengths, require


def verified_source(cert):
    p, g, z, unit_logs = (cert[k] for k in ('prime','generator','root','logs'))
    certify_prime(p)
    require(all(pow(g,(p-1)//factor,p) != 1 for factor in FACTOR_TABLE[p]), "seed order")
    require(z == pow(g,(p-1)//128,p) and pow(z,64,p) == p-1, "source root order")
    require(len(unit_logs) == 32 and all(pow(g,a,p) == (1-pow(z,j,p)) % p
            for j,a in zip(range(1,64,2),unit_logs)), "source unit logarithms")

    return p, g, z, unit_logs


def order64_logs(p, g, z, unit_logs):
    # For z_64 = z^2, (1-z^(2r))=(1-z^r)(1-z^(r+64)).
    logs = [(unit_logs[r//2]+unit_logs[(64-r)//2]+(p-1)//2+(64+r)*((p-1)//128)) % (p-1)
            for r in range(1,32,2)]
    require(all(pow(g,a,p) == (1-pow(z,2*r,p)) % p for r,a in zip(range(1,32,2),logs)),
            "order-64 logarithms")
    return logs


def check_field(cert, reverse):
    p, g, z, unit_logs = verified_source(cert)
    # Up to a 128th root of unity, phi_j=(1-z^j)/(1-z^(j+64)).
    factors = exponent_rows(128)
    chord_logs = [sum(a*(row[j]-row[j+64]) for a,row in zip(unit_logs,factors))
                  for j in range(1,32)]
    for j,log in enumerate(chord_logs,1):
        value = (1-pow(z,j,p))*pow(1+pow(z,j,p),-1,p) % p
        require(pow(g,128*log,p) == pow(value,128,p), "antipodal chord logarithm")
    basis = kernel_basis(chord_logs,(p-1)//128)
    if reverse:
        basis = fmpz_mat(list(reversed(basis.tolist())))
    gram = basis*basis.transpose()
    mu,lengths = orthogonal_lengths([[int(x) for x in row] for row in gram.tolist()])
    sphere = zero = 0
    for c in lattice_coordinates(mu,lengths,31*8**2):
        sphere += 1
        if any(c):
            t = (fmpz_mat([c])*basis).tolist()[0]
            require(max(abs(int(x)) for x in t) > 8, "nonzero bounded chord relation")
        else:
            zero += 1
    require((sphere,zero) == (5,1), "antipodal census")
    lower_logs = order64_logs(p, g, z, unit_logs)
    rows = exponent_rows(64)
    counts = [check_shift(rows,h,lower_logs,(p-1)//64,62*32**2,reverse,weight_bound=32)
              for h in range(1,33)]
    require(sum(counts) == (36,32)[PRIMES.index(p)], "order-64 ellipsoid census")
    print(f"p{PRIMES.index(p)+1}: antipodal sphere {sphere}, cube 1; weighted order 64 "
          f"ellipsoids {sum(counts)}, supported 32")


def negative_counts():
    for n,s,d,p in ((1024,2,45,PRIMES[1]), (2**30,2**21,45,PRIMES[1]),
                    (2**30,2,6,PRIMES[0]), (2**30,2,7,PRIMES[1])):
        blocks = n//(4*s)-2
        require(comb(blocks,d)*2**d > p-1, "too few different signed patterns")
        print(f"n={n}, centers={4*s}, degree at most {2*s*d}, free pairs={blocks}")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-basis',action='store_true')
    args = parser.parse_args()
    data = json.loads(Path(__file__).with_name('mu128_unit_logs.json').read_text())
    require(tuple(row['prime'] for row in data) == PRIMES, "named field coverage")
    for cert in data:
        check_field(cert,args.reverse_basis)
    negative_counts()
