#!/usr/bin/env python3
"""Certify the sharp weight for degree-zero order-64 locator comparisons."""
import argparse
import json
from math import prod
from pathlib import Path

from probe_dyadic_antipodal_blocks import order64_logs, verified_source
from probe_mu128_unit_ellipsoid import PRIMES, check_shift, exponent_rows
from probe_mu64_unit_lattice import require

HERE = Path(__file__).resolve().parent
ORDER = 64


def comparison_matrix(rows, h):
    sites = [j for j in range(ORDER) if j not in (0,h)]
    return [[row[j]-row[(j-h) % ORDER] for j in sites] for row in rows]


def check_witness(data, z, p, rows):
    h, weights = data['witness_shift'],data['witness_weights']
    require(len(weights) == ORDER and 0 < h <= 32 and weights[0] == weights[h] == 0,
            "bad witness layout")
    require(sum(weights) == 0 and max(map(abs,weights)) == data['bound']+1,
            "bad witness degree or size")
    def value(x):
        return prod(pow((pow(z,x,p)-pow(z,j,p)) % p,w,p)
                    for j,w in enumerate(weights) if w) % p
    require(value(0) == value(h), "named-field values differ")
    e = [sum(weights[j]*(row[j]-row[(j-h) % ORDER]) for j in range(ORDER)) for row in rows]
    require(any(e), "comparison also agrees modulo the primitive-unit exponents")
    return value(0)


def verify(cert, data, reverse):
    p,g,root,unit_logs = verified_source(cert)
    z = root*root % p
    logs = order64_logs(p,g,root,unit_logs)
    units = [(1-pow(z,r,p)) % p for r in range(1,32,2)]
    # beta_r = -z^(-r) u_r²; equal-degree comparisons satisfy product beta_r^e_r=1.
    beta_logs = [(2*a+(p-1)//2-r*((p-1)//64)) % (p-1) for a,r in zip(logs,range(1,32,2))]
    require(all(pow(g,a,p) == u*(1-pow(z,-r,p)) % p
                for a,u,r in zip(beta_logs,units,range(1,32,2))), "balanced phase logarithms")
    rows = exponent_rows(ORDER)
    bound = data['bound']
    separators = {(h,tuple(e)):y for h,e,y in data['separators']}
    used = set()
    total = 0
    for h in range(1,33):
        matrix = comparison_matrix(rows,h)
        def excluded(e):
            if h == 32:
                e = e+[-sum(e)]
            # The remaining torsion phase in the original unsquared comparison has order at most 64.
            if prod(pow(u,64*a,p) for u,a in zip(units,e)) % p != 1:
                return True
            if next(a for a in e if a) < 0:
                e = [-a for a in e]
            key = (h,tuple(e))
            y = separators.get(key)
            require(y is not None and len(y) == 17, "missing integer separating row")
            image_dot = sum(a*b for a,b in zip(y,e))
            source_l1 = sum(abs(y[-1]+sum(a*row[j] for a,row in zip(y,matrix)))
                            for j in range(62))
            require(image_dot > bound*source_l1, "invalid separating row")
            used.add(key)
            return True
        total += check_shift(rows,h,beta_logs,p-1,62*bound**2,reverse,
                             weight_bound=bound,reject_candidate=excluded)
    index = PRIMES.index(p)
    require(bound == (67,62)[index] and total == (3508,534)[index] and
            len(used) == (47,7)[index] and used == set(separators),
            "incomplete census or untested certificate")
    value = check_witness(data,z,p,rows)
    print(f"p{index+1} bound {bound}; ellipsoid points {total}; separating rows {len(used)}; "
          f"max-weight {bound+1} witness equal value {value}",flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-basis',action='store_true')
    args = parser.parse_args()
    fields = json.loads((HERE/'mu128_unit_logs.json').read_text())
    data = json.loads((HERE/'mu64_balanced_weight_certificates.json').read_text())
    require(tuple(c['prime'] for c in fields) == PRIMES and len(data) == 2,"named fields missing")
    for cert,table in zip(fields,data):
        verify(cert,table,args.reverse_basis)
