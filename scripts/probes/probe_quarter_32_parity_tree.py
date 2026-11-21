#!/usr/bin/env python3
"""Exclude all saturated complex μ32 layouts using parity, valuation and face ratios."""

from array import array
from collections import defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
import subprocess
import tempfile

# The columns are A, A', B, B', C, C' and the singleton holes.
SIGN = tuple(tuple(row[(j-2*k) % 6] for j in range(6)) + (0,)
             for k in range(3) for row in ((0, 0, 1, -1, -1, 1), (0, 0, 1, -1, 1, -1)))


def signature_groups(counts):
    heavy = [j for j in range(6) if counts[j] >= 3]
    groups = defaultdict(list)
    for c in range(7):
        groups[tuple(SIGN[h][c] for h in heavy)].append(c)
    return tuple(tuple(g) for g in groups.values())


def max_changed(counts, groups):
    changed = 0
    for group in groups:
        total = sum(counts[i] for i in group)
        if total % 2:
            return -1
        changed += min(total, 2*(total-max(counts[i] for i in group)))
    return changed


def parity_profiles():
    for sizes in combinations_with_replacement(range(8), 3):
        if sum(sizes) != 14:
            continue
        caps = tuple(v for size in sizes for v in (size, size)) + (4,)
        for colors in product(*(range(v+1) for v in caps[:6])):
            holes = 16-sum(colors)
            if not 0 <= holes <= 4:
                continue
            even = colors + (holes,)
            odd = tuple(a-b for a, b in zip(caps, even))
            if even > odd:
                continue
            groups = (signature_groups(odd), signature_groups(even))
            bounds = [max_changed(v, g) for v, g in zip((even, odd), groups)]
            if min(bounds) >= 0 and sum(bounds) >= 7:
                yield sizes, even, odd, groups


@lru_cache(None)
def splits(counts):
    half = sum(counts)//2
    result = []
    for left in product(*(range(v+1) for v in counts)):
        if sum(left) == half:
            right = tuple(a-b for a, b in zip(counts, left))
            if left <= right:
                result.append((left, right))
    return result


@lru_cache(None)
def signed_counts(counts):
    return tuple(sum(a*b for a, b in zip(row, counts)) for row in SIGN)


def spread(word):
    """Put the consecutive hex digits of a packed half-block in the even slots."""
    word = (word | word << 16) & 0x0000ffff0000ffff
    word = (word | word << 8) & 0x00ff00ff00ff00ff
    return (word | word << 4) & 0x0f0f0f0f0f0f0f0f


def subtree(groups, materialize):
    @lru_cache(None)
    def states(counts):
        n = sum(counts)
        if n == 2:
            a, b = [i for i, size in enumerate(counts) for _ in range(size)]
            if not any(a in g and b in g for g in groups):
                return {}
            values = tuple(16*(SIGN[c][b] if c == a else SIGN[c][a]) if counts[c] else 0
                           for c in range(6))
            words = [a + 16*b] + ([b + 16*a] if a != b else [])
            return {(values, 2*int(a != b)): array('Q', words) if materialize else None}
        out = {}
        for left, right in splits(counts):
            left_states, right_states = states(left), states(right)
            if not left_states or not right_states:
                continue
            shared = [i for i in range(6) if left[i] and right[i]]
            weight = 32//n
            inc_left, inc_right = signed_counts(right), signed_counts(left)
            for (lv, ld), lwords in left_states.items():
                adjusted = tuple(lv[i]+weight*inc_left[i] for i in range(6))
                expanded_left = None
                for (rv, rd), rwords in right_states.items():
                    if any(adjusted[i] != rv[i]+weight*inc_right[i] for i in shared):
                        continue
                    value = tuple(adjusted[i] if left[i] else rv[i]+weight*inc_right[i] if right[i] else 0
                                  for i in range(6))
                    key = (value, ld+rd)
                    if not materialize:
                        out[key] = None
                        continue
                    if expanded_left is None:
                        expanded_left = [spread(v) for v in lwords]
                    expanded_right = [spread(w) for w in rwords]
                    dest = out.setdefault(key, array('Q'))
                    for x in expanded_left:
                        dest.extend(x | y << 4 for y in expanded_right)
                        if left != right:
                            dest.extend(y | x << 4 for y in expanded_right)
        return out
    return states


@lru_cache(None)
def state_types(groups):
    return subtree(groups, False)


def qualifying_pairs(even, odd, groups):
    left = state_types(groups[0])(even)
    right = state_types(groups[1])(odd)
    for (lv, ld) in left:
        for (rv, rd) in right:
            if ld+rd < 7:
                continue
            le = tuple(a+b for a, b in zip(lv, signed_counts(odd)))
            ro = tuple(a+b for a, b in zip(rv, signed_counts(even)))
            if any(even[i] and odd[i] and le[i] != ro[i] for i in range(6)):
                continue
            yield ((lv, ld), (rv, rd))


def write_case(prefix, halves, groups, pairs):
    indices = []
    with prefix.with_suffix('.txt').open('w') as meta:
        for side, counts, group, idx in zip(('L', 'R'), halves, groups, (0, 1)):
            keys = list(dict.fromkeys(pair[idx] for pair in pairs))
            meta.write(f'{len(keys)}\n')
            expand = subtree(group, True)
            states = expand(counts)
            with Path(str(prefix)+f'-{side}.bin').open('wb') as output:
                for key in keys:
                    assert states[key].itemsize == 8
                    meta.write(f'{len(states[key])}\n')
                    states[key].tofile(output)
            indices.append({key: j for j, key in enumerate(keys)})
            expand.cache_clear()
        for a, b in pairs:
            meta.write(f'{indices[0][a]} {indices[1][b]}\n')


def main():
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        executable = root/'face-ratios'
        source = Path(__file__).with_name('probe_quarter_32_parity_faces.cpp')
        subprocess.run(['c++', '-O3', '-std=c++17', str(source), '-o', str(executable)], check=True)
        cases = []
        profiles = 0
        for _sizes, even, odd, groups in parity_profiles():
            profiles += 1
            pairs = list(qualifying_pairs(even, odd, groups))
            if pairs:
                prefix = root/str(profiles)
                write_case(prefix, (even, odd), groups, pairs)
                cases.append(prefix)
        assert profiles == 195 and len(cases) == 35
        print(f'{profiles} parity populations, {len(cases)} with compatible valuation profiles.', flush=True)
        subprocess.run([executable, *cases], check=True)


if __name__ == '__main__':
    main()
