#!/usr/bin/env python3
"""Construct Paley domains with uniform shift bounds or many positively biased shifts."""
from functools import lru_cache
from itertools import combinations
from math import comb


def require(test, reason):
    if not test:
        raise ArithmeticError(reason)


def symbols(p):
    return [0 if t == 0 else (1 if pow(t, (p - 1) // 2, p) == 1 else -1)
            for t in range(p)]


def count_completions(p, m, size, total, zeros, threshold, two_sided):
    """Number of size-m completions of this partially exposed row crossing the threshold."""
    half = (p - 1) // 2
    selected_positive = (size - zeros + total) // 2
    selected_negative = size - zeros - selected_positive
    positives, negatives = half - selected_positive, half - selected_negative
    need = m - size
    count = 0
    for take_zero in range(min(1 - zeros, need) + 1):
        for plus in range(max(0, need - take_zero - negatives), min(need - take_zero, positives) + 1):
            minus = need - take_zero - plus
            value = total + plus - minus
            if (abs(value) if two_sided else value) >= threshold:
                count += comb(positives, plus) * comb(negatives, minus)
    return count


def choose_domain(p, m, threshold, minimize):
    """Conditional expectation with integer scores. All candidates have the same denominator."""
    chi = symbols(p)
    unchosen = set(range(p))
    totals = [0] * p
    zeros = [0] * p
    domain = []
    completions = lru_cache(maxsize=None)(
        lambda used, w, z: count_completions(p, m, used, w, z, threshold, minimize))
    previous = p * completions(0, 0, 0)
    for used in range(1, m + 1):
        scores = []
        for u in sorted(unchosen):
            score = sum(completions(used, totals[b] + chi[(b + u) % p],
                                    zeros[b] + int(b == (-u) % p)) for b in range(p))
            scores.append((score, u))
        require(sum(v for v, _ in scores) == (m - used + 1) * previous, "completion double count")
        best, u = min(scores) if minimize else max(scores)
        domain.append(u)
        unchosen.remove(u)
        for b in range(p):
            totals[b] += chi[(b + u) % p]
        zeros[(-u) % p] = 1
        previous = best
    computed = [sum(chi[(u + b) % p] for u in domain) for b in range(p)]
    require(totals == computed, "shift sum")
    if minimize:
        require(previous == sum(abs(w) >= threshold for w in totals), "large absolute shifts")
    else:
        require(previous == sum(w >= threshold for w in totals), "large signed shifts")
    return domain, totals


def exhaustive_check(p, m):
    chi = symbols(p)
    for threshold in range(m + 2):
        counts = [0, 0]
        for domain in combinations(range(p), m):
            for b in range(p):
                w = sum(chi[(b + u) % p] for u in domain)
                counts[0] += w >= threshold
                counts[1] += abs(w) >= threshold
        for two_sided in (False, True):
            exact = p * count_completions(p, m, 0, 0, 0, threshold, two_sided)
            require(exact == counts[two_sided], (p, m, threshold, two_sided))


def check_quartic_moment(p):
    """Compare distinct-branch curve counts with the fourth row moment, including poles."""
    chi = symbols(p)
    quartics = {}
    for sites in combinations(range(p), 4):
        # Count affine points of y^2 = product(x+u), independently of chi.
        residues = [1] * p
        for u in sites:
            residues = [(v * (x + u)) % p for x, v in enumerate(residues)]
        squares = [0] * p
        for y in range(p):
            squares[y*y % p] += 1
        quartics[sites] = sum(squares[v] for v in residues) - p
    checked = 0
    for m in range(1, p + 1):
        for domain in combinations(range(p), m):
            w = [sum(chi[(b + a) % p] for a in domain) for b in range(p)]
            distinct = sum(quartics[q] for q in combinations(domain, 4))
            pole_correction = sum(w[-a % p]**2 for a in domain)
            expected = (24*distinct + p*(3*m*m - 2*m) - 6*m**3 +
                        14*m*m - 9*m - 6*pole_correction)
            require(sum(x**4 for x in w) == expected, (p, domain, "quartic identity"))
            checked += 1
    return checked


def main():
    for p in (3, 5, 7, 11):
        for m in range(1, min(p, 5) + 1):
            exhaustive_check(p, m)
    quartic_checks = sum(check_quartic_moment(p) for p in (3, 5, 7, 11))
    print(f"Exact fourth moment from affine curve counts on {quartic_checks} nonempty domains")
    p, m = 257, 16
    denominator = comb(p, m)
    safe = next(t for t in range(m + 2)
                if p * count_completions(p, m, 0, 0, 0, t, True) < denominator)
    witness = max(t for t in range(m + 1)
                  if p * count_completions(p, m, 0, 0, 0, t, False) >= m * denominator)
    a_good, residuals = choose_domain(p, m, safe, minimize=True)
    require(max(map(abs, residuals)) < safe, "uniform certificate")
    a_bad, residuals_bad = choose_domain(p, m, witness, minimize=False)
    shifts = sorted(range(p), key=lambda b: residuals_bad[b], reverse=True)[:m]
    score = sum(residuals_bad[b] for b in shifts)
    require(min(residuals_bad[b] for b in shifts) >= witness, "biased rectangle")
    print(f"p={p}, m={m}, threshold guaranteeing a uniformly bounded domain: {safe}")
    print(f"A={a_good}, maximum over every shift={max(map(abs, residuals))}")
    print(f"threshold guaranteeing {m} positive shifts: {witness}")
    print(f"A={a_bad}, B={shifts}, signed sum={score} of {m*m}")


if __name__ == "__main__":
    main()
