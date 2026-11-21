import ArkLib.Research.ProximityGap.Frontier.DyadicOddPencilExclusion
import ArkLib.Research.ProximityGap.Frontier.DyadicFourCycleCount

/-!
# The 4-cycle with reflection equations on `ZMod (2 ^ (e + 1))`

Composition of the parity lemma for sets with the 4-cycle contradiction. Four sets
`Q₀,…,Q₃` of the same odd size `q ≥ 5` and four overlap sites `s₀,…,s₃` in
`ZMod (2 ^ (e + 1))`, with `2 * q + 2` of these points in each parity class, cannot satisfy
the reflection equations at all four vertices.

The class counts are stated as hypotheses; they hold when the eight pieces partition the
group. The reflection equations are the characteristic-zero input and are not formalised.
See Section 4 of `docs/research/proximity-gap/dyadic-radius-successor-list-three.md`.
-/

open Finset

namespace ProximityGap.DyadicFourCycle

open ProximityGap.DyadicOddPencil

variable (e : ℕ)

/-- **No 4-cycle.** -/
theorem four_cycle_refl (he : 1 ≤ e) {Q0 Q1 Q2 Q3 : Finset (ZMod (2 ^ (e + 1)))}
    {s0 s1 s2 s3 : ZMod (2 ^ (e + 1))} {q : ℕ} (hq : 5 ≤ q) (hodd : q % 2 = 1)
    (k0 : Q0.card = q) (k1 : Q1.card = q) (k2 : Q2.card = q) (k3 : Q3.card = q)
    (d01 : Disjoint Q0 Q1) (d12 : Disjoint Q1 Q2) (d23 : Disjoint Q2 Q3) (d30 : Disjoint Q3 Q0)
    (s01 : s0 ≠ s1) (s12 : s1 ≠ s2) (s23 : s2 ≠ s3) (s30 : s3 ≠ s0)
    (n00 : s0 ∉ Q0) (n01 : s0 ∉ Q1) (n11 : s1 ∉ Q1) (n12 : s1 ∉ Q2)
    (n22 : s2 ∉ Q2) (n23 : s2 ∉ Q3) (n33 : s3 ∉ Q3) (n30 : s3 ∉ Q0)
    (classf : nb (cl e) Q0 false + nb (cl e) Q1 false + nb (cl e) Q2 false + nb (cl e) Q3 false
      + cls (cl e) s0 false + cls (cl e) s1 false + cls (cl e) s2 false + cls (cl e) s3 false
      = 2 * q + 2)
    (classt : nb (cl e) Q0 true + nb (cl e) Q1 true + nb (cl e) Q2 true + nb (cl e) Q3 true
      + cls (cl e) s0 true + cls (cl e) s1 true + cls (cl e) s2 true + cls (cl e) s3 true
      = 2 * q + 2)
    (h0 : Disjoint (insert s2 Q3) (insert s1 Q1))
    (r0 : Refl e Q0 (insert s2 Q3) (insert s1 Q1))
    (h1 : Disjoint (insert s3 Q0) (insert s2 Q2))
    (r1 : Refl e Q1 (insert s3 Q0) (insert s2 Q2))
    (h2 : Disjoint (insert s0 Q1) (insert s3 Q3))
    (r2 : Refl e Q2 (insert s0 Q1) (insert s3 Q3))
    (h3 : Disjoint (insert s1 Q2) (insert s0 Q0))
    (r3 : Refl e Q3 (insert s1 Q2) (insert s0 Q0)) : False := by
  obtain ⟨fa0, fb0⟩ := forces_of_refl e he h0 r0
  obtain ⟨fa1, fb1⟩ := forces_of_refl e he h1 r1
  obtain ⟨fa2, fb2⟩ := forces_of_refl e he h2 r2
  obtain ⟨fa3, fb3⟩ := forces_of_refl e he h3 r3
  exact four_cycle_false (anti_anti e) (anti_ne e) (cl_anti e he) hq hodd k0 k1 k2 k3
    d01 d12 d23 d30 s01 s12 s23 s30 n00 n01 n11 n12 n22 n23 n33 n30 classf classt
    (fun h ↦ ⟨fa0 true h, fb0 true h⟩)
    (fun h ↦ ⟨fa0 false h, fb0 false h⟩)
    (fun h ↦ ⟨fa1 true h, fb1 true h⟩)
    (fun h ↦ ⟨fa1 false h, fb1 false h⟩)
    (fun h ↦ ⟨fa2 true h, fb2 true h⟩)
    (fun h ↦ ⟨fa2 false h, fb2 false h⟩)
    (fun h ↦ ⟨fa3 true h, fb3 true h⟩)
    (fun h ↦ ⟨fa3 false h, fb3 false h⟩)

end ProximityGap.DyadicFourCycle

#print axioms ProximityGap.DyadicFourCycle.four_cycle_refl
