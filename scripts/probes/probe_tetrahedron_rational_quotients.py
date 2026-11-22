"""Check candidate tetrahedron vertex fibers over the designated second prime.

Run from the repository root with python3 scripts/probes/probe_tetrahedron_rational_quotients.py.
The existing C++ fingerprint sieve screens all dihedral orbits. Every surviving
ratio is then evaluated on the entire quotient in the actual prime field.
"""

from collections import Counter
from functools import lru_cache
from math import prod
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import PRIME


def run_case(directory, binary, size, anchor, degree, expected_orbits, expected_profiles):
    probes = Path(__file__).resolve().parent
    table = directory / f"table-{size}"
    if not table.exists():
        subprocess.run([sys.executable, probes / "probe_mu32_modp_fingerprint_table.py",
                        str(PRIME), str(size), table], check=True)
    result = subprocess.run([binary, table, str(anchor), str(degree), "3"],
                            capture_output=True, text=True, check=True)
    lines = result.stdout.splitlines()
    expected_hits = sum(expected_profiles.values())
    require(lines[-1] == f"DONE N={size} |T|={anchor} size={degree} "
            f"T-orbits={expected_orbits} hits={expected_hits}", "complete sieve")
    # This is the same primitive root used to construct the fingerprint table.
    generator = next(t for t in range(2, PRIME) if pow(t, (PRIME-1)//2, PRIME) != 1)
    z = pow(generator, (PRIME-1)//size, PRIME)
    nodes = tuple(pow(z, i, PRIME) for i in range(size))

    @lru_cache(None)
    def locator(mask):
        roots = [v for i, v in enumerate(nodes) if mask >> i & 1]
        return tuple(prod(t-v for v in roots) % PRIME for t in nodes)

    profiles = Counter()
    for line in lines[:-1]:
        require(line.startswith("HIT "), "unexpected sieve output")
        target, first, second = (int(t[2:], 16) for t in line.split()[1:])
        require((target & first) == (target & second) == (first & second) == 0,
                "disjoint candidate masks")
        require(target.bit_count() == anchor and first.bit_count() == second.bit_count() == degree,
                "mask degrees")
        values = [a*pow(c, -1, PRIME) % PRIME if c else -1
                  for a, c in zip(locator(first), locator(second))]
        require(len({values[i] for i in range(size) if target >> i & 1}) == 1,
                "constant ratio on the target")
        profile = tuple(sorted(Counter(values).values(), reverse=True)[:4])
        profiles[profile] += 1
    require(profiles == expected_profiles, "exact prime-field fiber populations")
    print(f"nodes={size} target={anchor} degree={degree} orbits={expected_orbits} "
          f"hits={expected_hits} four largest={dict(sorted(profiles.items()))}")


def main():
    probes = Path(__file__).resolve().parent
    with TemporaryDirectory() as temp:
        directory = Path(temp)
        binary = directory / "ratio-search"
        subprocess.run(["c++", "-std=c++17", "-O3", "-pthread",
                        probes / "probe_mu32_modp_ratio_search.cpp", "-o", binary], check=True)
        run_case(directory, binary, 16, 3, 3, 21, {(3, 3, 3, 1): 4, (3, 3, 3, 2): 3})
        run_case(directory, binary, 32, 5, 5, 3199, {})
        run_case(directory, binary, 32, 5, 6, 3199, {(6, 6, 6, 2): 10, (6, 6, 6, 4): 9})


if __name__ == "__main__":
    main()
