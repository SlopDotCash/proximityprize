"""Unit coverage for docs/kb/mixed-tower-probes/mixed_tower_debruijn_check.py.

Tests the pure decomposition helpers: prime-packet block generation (mu_2
pairs and mu_3 triples with correct bit masks), and the backtracking
decomposer (memoized, decides whether a mask splits into disjoint packets).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "docs" / "kb" / "mixed-tower-probes"))

# The probe file hardcodes sys.path.insert(0, "/tmp") at import; tolerate it
# since we only need the pure helpers.
from mixed_tower_debruijn_check import make_decomposer, prime_blocks_per_elem  # noqa: E402


def test_prime_blocks_per_elem_n8() -> None:
    per, blocks = prime_blocks_per_elem(8)
    # mu_2 pairs: {0,4},{1,5},{2,6},{3,7} → 4 blocks of 2 bits.
    pairs = [b for b in blocks if b.bit_count() == 2]
    assert len(pairs) == 4
    # mu_3 triples: for i in range(8//3=2): {i, i+2, i+2*8//3=i+5} (Python
    # precedence: 2*n//3 = (2*8)//3 = 5) → {0,2,5}, {1,3,6}.
    triples = [b for b in blocks if b.bit_count() == 3]
    assert len(triples) == 2
    assert 0b100101 in triples  # {0,2,5}
    assert 0b1001010 in triples  # {1,3,6}
    # Every element 0..7 appears in at least one block (union covers all).
    union = 0
    for b in blocks:
        union |= b
    assert union == (1 << 8) - 1


def test_prime_blocks_per_elem_n6() -> None:
    per, blocks = prime_blocks_per_elem(6)
    pairs = [b for b in blocks if b.bit_count() == 2]
    triples = [b for b in blocks if b.bit_count() == 3]
    assert len(pairs) == 3  # {0,3},{1,4},{2,5}
    assert len(triples) == 2  # {0,2,4},{1,3,5}


def test_decomposer_single_pair() -> None:
    dec = make_decomposer(6)
    pair = (1 << 0) | (1 << 3)  # {0,3}
    assert dec(pair) is True
    assert dec(0) is True  # empty mask


def test_decomposer_full_set_n6() -> None:
    dec = make_decomposer(6)
    full = (1 << 6) - 1
    # {0..5} = pair {0,3} + pair {1,4} + pair {2,5} → decomposable.
    assert dec(full) is True


def test_decomposer_single_bit_not_decomposable() -> None:
    dec = make_decomposer(6)
    assert dec(1 << 2) is False  # {2} alone cannot form any packet


def test_decomposer_memoizes() -> None:
    dec = make_decomposer(8)
    # Run twice; second call hits the cache (no error, same result).
    mask = (1 << 0) | (1 << 4)
    assert dec(mask) is True
    assert dec(mask) is True
