/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# Guruswami–Sudan Interpolation for Line-Decoding Double Coverage

The `(1, k-1)`-weighted Guruswami–Sudan interpolant existence used for the line-decoding
`MCAForallDoubleCover` argument is already **fully proved** as `exists_interpolant` in
`ArkLib.ToMathlib.BasefoldSingleRoundSoundness` (built on `SiegelInterpolation.GS.exists_gs_interpolant`).

This module previously re-derived a weaker `exists_interpolant` here but left the
list-index/`Fin S.card` bijection step as a `sorry`. That incomplete duplicate was removed in
favour of the proved `ToMathlib/Prop55` version (DRY); consume that lemma directly.
-/
