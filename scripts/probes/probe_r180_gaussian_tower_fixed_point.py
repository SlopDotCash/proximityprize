#!/usr/bin/env python3
"""#466 R180: the dyadic tower split matches the real-Gaussian fixed point.

R178 measured two tower-split statistics near 0.636:

  cancel = |a+b|^2 / (|a|+|b|)^2
  polar  = ||a|^2-|b|^2| / (|a|^2+|b|^2)

For independent real Gaussians these expectations are both 2/pi.  This probe
prints the closed-form target and a deterministic quadrature check.
"""

from __future__ import annotations

import math


def quadrature(samples: int = 4000) -> tuple[float, float]:
    # Midpoint quadrature after polar coordinates.  For (A,B) isotropic
    # Gaussian, the angle is uniform and the radius cancels in both ratios.
    cancel = 0.0
    polar = 0.0
    for i in range(samples):
        theta = 2 * math.pi * (i + 0.5) / samples
        a = math.cos(theta)
        b = math.sin(theta)
        cancel += (a + b) ** 2 / (abs(a) + abs(b)) ** 2
        polar += abs(a * a - b * b) / (a * a + b * b)
    return cancel / samples, polar / samples


def main() -> None:
    cancel, polar = quadrature()
    print(f"2/pi        = {2 / math.pi:.12f}")
    print(f"cancel_quad = {cancel:.12f}")
    print(f"polar_quad  = {polar:.12f}")
    print("R178 dyadic measured: cancel≈0.634..0.636, polar≈0.634..0.636")


if __name__ == "__main__":
    main()
