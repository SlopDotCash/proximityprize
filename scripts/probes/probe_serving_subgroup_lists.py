"""Verify signed list populations with three or seven serving quotient fibers."""

from collections import Counter, defaultdict
from itertools import combinations
from math import gcd

from probe_oriented_fiber_lists import oriented_counter, require, signature_pool
from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul
from probe_reciprocal_fiber_lists import signature_of


def assigned(exponents, order, reserved, offset, stride):
    """A rotation by an element of the reserved subgroup preserves every gcd weight."""
    weight = sum(gcd(j, order) for j in exponents)
    return (weight // stride + offset) % (reserved-1)


def small():
    order, h, p, size = 16, 8, 257, 5
    xs = [pow(9, j, p) for j in range(order*h)]
    ys = [pow(9, h*j, p) for j in range(order)]
    for reserved in (4, 8):
        step = order // reserved
        omitted = frozenset(range(0, order, step))
        ordinary = set(range(order))-omitted
        histogram = defaultdict(lambda: [0]*(2*order))
        by_root = defaultdict(list)
        for subset in combinations(sorted(ordinary), size):
            signature = signature_of(set(subset), order)
            score = sum(gcd(j, order) for j in subset)
            require(sum(signature) == score, "gcd identity for original mask")
            histogram[signature][sum(subset) % (2*order)] += 1
            a = assigned(subset, order, reserved, 0, 5)
            rotated = {(j-a*step) % order for j in subset}
            require(sum(signature_of(rotated, order)) == score, "rotation-invariant weight")
            loc = fiber_polynomial([ys[j] for j in subset], p)
            key = (signature_of(rotated, order), sum(rotated) % (2*order))
            by_root[sum(subset) % order].append((a, key, loc))
        count = oriented_counter(order, size, omitted)
        for sig, bins in histogram.items():
            require(count(sig) == bins, "restricted histogram disagrees with enumeration")
        gain = h//2
        best = []
        for members in by_root.values():
            seats = [Counter(label for anchor, label, _ in members if anchor == a).most_common(2)
                     for a in range(reserved-1)]
            winners = [(a,label,loc) for a,label,loc in members if any(label == v for v,_ in seats[a])]
            if len(winners) > len(best):
                best, best_seats = winners, seats
        c = best[0][2][0]
        common = fiber_polynomial([x for x in xs if pow(x,h,p) == ys[(reserved-1)*step]][:h-1],p)
        served = {}
        for a,seats in enumerate(best_seats):
            y = ys[a*step]
            sites = [x for x in xs if pow(x,h,p) == y]
            for idx,(label,_) in enumerate(seats):
                values = {evaluate(loc,y,p) for anchor,key,loc in best if (anchor,key) == (a,label)}
                require(len(values) == 1, "signed locator value")
                for x in sites[idx*gain:(idx+1)*gain]:
                    served[x] = next(iter(values))
        center = []
        for x in xs:
            y = pow(x,h,p)
            center.append(evaluate(common,x,p)*(pow(y,size,p)+c-served.get(x,0))*pow(y,-1,p)%p)
        words = set()
        for _,_,loc in best:
            require(loc[0] == c, "common product")
            head = [0]*((size-2)*h+1)
            head[::h] = [(-v)%p for v in loc[1:-1]]
            message = poly_mul(common,head,p)
            require(len(message) <= (size-1)*h, "degree bound")
            word = tuple(evaluate(message,x,p) for x in xs)
            require(sum(a == b for a,b in zip(word,center)) >= size*h+(h-1)+gain, "actual agreements")
            words.add(word)
        require(len(words) == len(best), "distinct evaluation words")
        print(f"F257: {len(words)} distinct words with {reserved-1} serving fibers checked on 128 sites.")


def production(order, size, levels, deviations, pool_size, reserved, root_exponent, receipts):
    h = 2**30 // order
    step = order // reserved
    omitted = frozenset(range(0, order, step))
    count = oriented_counter(order, size, omitted)
    groups = defaultdict(lambda: [[] for _ in range(reserved-1)])
    pool = signature_pool(order//4, levels, deviations, size, pool_size)
    for _,signature in pool:
        bins = count(signature)
        for a, group in enumerate(groups[sum(signature)]):
            r = (root_exponent-size*a*step) % order
            group.extend((bins[r],bins[r+order]))
    for field,offset,stride,slots,expected_words,expected_errors in receipts:
        rows = [[] for _ in range(reserved-1)]
        for total,groups_at_total in groups.items():
            a = (total//stride+offset) % (reserved-1)
            rows[a].extend(groups_at_total[a])
        population = sum(sum(sorted(row,reverse=True)[:slots]) for row in rows)
        gain = h//slots
        errors = 2**30-(size+1)*h+1-gain
        require(population == expected_words and population > field*2**30, "production population")
        require(errors == expected_errors, "error threshold")
        print(f"prime={field} rate=1/{order//(size-1)} serving_fibers={reserved-1} slots={slots} "
              f"population={population} gain={gain} errors={errors}")


if __name__ == "__main__":
    small()
    production(64, 17, range(1,6), 3, 12000, 4, 1,
               [(1,0,3,887,1073797722,771733023),(2,0,1,2524,2147776086,771745290)])
    production(128, 17, range(1,4), 2, 500, 8, 16,
               [(1,4,3,8,1193754620,921698305),(2,4,3,17,2161068386,922253434)])
