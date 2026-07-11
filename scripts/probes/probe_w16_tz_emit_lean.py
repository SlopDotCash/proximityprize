#!/usr/bin/env python3
"""
probe_w16_tz_emit_lean.py — emit the intermediate dyadic TZ rung files (thread
res:tz-prize-scale, #466).

Companion to probe_w16_tz_prize_scale.py (which sieves + verifies + reports).  This
script re-runs the same deterministic sieve for k = 16..29 and writes the three grouped
Frontier lane files

  _W16TZDyadicRungs16to20.lean   (n = 2^16 .. 2^20)
  _W16TZDyadicRungs21to25.lean   (n = 2^21 .. 2^25)
  _W16TZDyadicRungs26to29.lean   (n = 2^26 .. 2^29)

each discharging `TZPrimeSupply (2^k) 2 20` with twenty two-factor Lucas-certified
primes per rung (see the prize-scale file `_W16TZPrizeScaleP30.lean` for the pattern;
the n = 2^30 rung lives there).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_w16_tz_prize_scale import sieve_rung  # noqa: E402

REPO = "/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib"
DIR = f"{REPO}/ArkLib/Data/CodingTheory/ProximityGap/Frontier"

HEADER = """/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# W16 — intermediate dyadic `TZPrimeSupply` rungs `n = 2^{LO} .. 2^{HI}` (#466)

Fills the explicit-certificate Thorner–Zaman ladder between the pre-existing top rung
`n = 2^15` (`ThornerZamanInstance.lean`) and the prize-scale rung `n = 2^30`
(`_W16TZPrizeScaleP30.lean`): for each `k = {LO}..{HI}` this file proves

  `tzPrimeSupply_<2^k>_two : TZPrimeSupply (2^k) (2 : ℝ) 20`,

i.e. the window `[2^(2k), 2^(2k+1)]` contains at least twenty primes `≡ 1 (mod 2^k)`.
Every witness prime has the kernel-cheap two-factor Lucas shape `p − 1 = 2^a · c`
(`a = max(k, 2k−20)`, `c` an odd prime of ≤ 21 bits, witness `g = 3`), sieved and
independently re-verified by `scripts/probes/probe_w16_tz_prize_scale.py` and emitted
by `scripts/probes/probe_w16_tz_emit_lean.py`.  `binaryPow` is the locally verified
square-and-multiply exponentiation (provenance: `Frontier/_PrizeShapePrimeP30.lean`).

The asymptotic [TZ24] statement remains the named open hypothesis; these are concrete,
axiom-clean discharges at the dyadic moduli, feeding small-supply consumers
(`tzSupplyOne_gives_*`, width-four-refuter-style pigeonholes) at every scale up to the
prize modulus.
-/

namespace ArkLib.ProximityGap.Frontier.W16TZDyadicRungs

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ArkLib.ProximityGap.KKH26

/-! ## Kernel-cheap exponentiation (provenance: `Frontier/_PrizeShapePrimeP30.lean`,
verbatim copy of the locally verified square-and-multiply implementation) -/

/-- Structurally recursive fuel wrapper for kernel-cheap square-and-multiply
exponentiation. -/
private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

/-- Kernel-cheap square-and-multiply exponentiation. -/
private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M : Type*} [Monoid M] (a : M) (n fuel : ℕ)
    (hnfuel : n < fuel) : binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

/-- **Two-factor Lucas certificate.**  If `p − 1 = 2^e · c` with `c` an odd prime, a
witness `g` with `g^(p−1) = 1`, `g^((p−1)/2) ≠ 1`, `g^((p−1)/c) ≠ 1` certifies `p`
prime. -/
private theorem lucasTwoFactor {p : ℕ} (c e : ℕ) (g : ZMod p)
    (hc : Nat.Prime c) (hfact : p - 1 = 2 ^ e * c)
    (hmain : g ^ (p - 1) = 1)
    (h2 : g ^ ((p - 1) / 2) ≠ 1)
    (hcw : g ^ ((p - 1) / c) ≠ 1) : Nat.Prime p := by
  refine lucas_primality p g hmain ?_
  intro q hq hdvd
  rw [hfact] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2' | hc'
  · obtain rfl : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2')
    exact h2
  · obtain rfl : q = c := (Nat.prime_dvd_prime_iff_eq hq hc).mp hc'
    exact hcw
"""

FOOTER_OPEN = """
end ArkLib.ProximityGap.Frontier.W16TZDyadicRungs

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/
"""


def wrap_setlit(primes, indent, width=62):
    """Render {p1, ..., p20} wrapped at <= width cols with `indent` continuation
    spaces (leaves room for the `} : Finset ℕ) ...` suffix on the final line)."""
    parts = [str(p) for p in primes]
    lines = []
    cur = "{"
    for i, s in enumerate(parts):
        piece = s + (", " if i < len(parts) - 1 else "")
        if len(cur) + len(piece) > width:
            lines.append(cur)
            cur = " " * indent + piece
        else:
            cur += piece
    cur += "}"
    lines.append(cur)
    return "\n".join(lines)


def rung_block(k, rows):
    n = 1 << k
    lo = n * n
    primes = [p for (p, _, _, _) in rows]
    out = []
    out.append(f"/-! ### Rung `n = 2^{k} = {n}`: window `[{lo}, {2 * lo}]` -/\n")
    for (p, c, a, g) in rows:
        out.append(
            f"private theorem prime_{p} : Nat.Prime {p} :=\n"
            f"  lucasTwoFactor {c} {a} {g} (by norm_num) (by norm_num)\n"
            f"    (by rw [← binaryPow_eq_pow]; decide)\n"
            f"    (by rw [← binaryPow_eq_pow]; decide)\n"
            f"    (by rw [← binaryPow_eq_pow]; decide)\n"
        )
    memb = []
    for i, p in enumerate(primes):
        memb.append(
            f"  have h{i + 1} : ({p} : ℕ) ∈ tzWindow {n} (2 : ℝ) := by\n"
            f"    rw [mem_tzWindow]\n"
            f"    exact ⟨prime_{p}, by decide, by rw [hpow]; norm_num,\n"
            f"      by rw [hpow]; norm_num⟩"
        )
    memb_block = "\n".join(memb)
    setlit_sub = wrap_setlit(primes, 8)
    setlit_calc = wrap_setlit(primes, 10)
    out.append(
        f"""/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^{k} = {n}`, `β = 2`.**
The window `[{n}², 2·{n}²] = [{lo}, {2 * lo}]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod {n})`. -/
theorem tzPrimeSupply_{n}_two : TZPrimeSupply {n} (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : (({n} : ℕ) : ℝ) ^ (2 : ℝ) = {lo} := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
{memb_block}
  have hsub :
      ({setlit_sub} : Finset ℕ) ⊆
        tzWindow {n} (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({setlit_calc} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow {n} (2 : ℝ)).card := Finset.card_le_card hsub
"""
    )
    return "\n".join(out)


def emit_file(ks, fname):
    blocks = [HEADER.replace("{LO}", str(ks[0])).replace("{HI}", str(ks[-1]))]
    ns = []
    for k in ks:
        rows = sieve_rung(k)
        blocks.append(rung_block(k, rows))
        ns.append(1 << k)
    blocks.append(FOOTER_OPEN)
    for n in ns:
        blocks.append(
            "#print axioms "
            f"ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_{n}_two"
        )
    path = f"{DIR}/{fname}"
    with open(path, "w") as f:
        f.write("\n".join(blocks) + "\n")
    nlines = sum(1 for _ in open(path))
    maxcol = max(len(line.rstrip("\n")) for line in open(path))
    print(f"wrote {path}: {nlines} lines, max col {maxcol}")


def main():
    emit_file(list(range(16, 21)), "_W16TZDyadicRungs16to20.lean")
    emit_file(list(range(21, 26)), "_W16TZDyadicRungs21to25.lean")
    emit_file(list(range(26, 30)), "_W16TZDyadicRungs26to29.lean")


if __name__ == "__main__":
    main()
