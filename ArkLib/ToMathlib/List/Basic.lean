/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/

/-!
# Additional `List` lemmas

Small `List` utility lemmas extending Mathlib's API.

* `List.take_one_eq_head`: taking the first element of a non-empty list yields the singleton
  list containing its head, `l.take 1 = [l.head h]`.
-/

@[simp, grind =]
theorem List.take_one_eq_head.{u} {α : Type u} {l : List α} (h : l ≠ []) :
    l.take 1 = [l.head h] := by grind [cases List]
