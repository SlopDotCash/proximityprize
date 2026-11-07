/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Binary Basefold decoder compatibility

Check the complete original positional API, including the historical prime-characteristic and
nonzero-round metadata, against the canonical decoder. Both APIs require an in-radius proof;
neither has an out-of-radius fallback. See `scripts/integration/binius-decoder-consolidation.json`.
-/

namespace Binius.BinaryBasefold.Compatibility
set_option backward.isDefEq.respectTransparency false

/-- The original full positional interface remains valid and computes the canonical decoder. -/
theorem UDRCodeword_original_signature
    {r : ℕ} [nr : NeZero r] {L : Type} [lf : Field L] [lfin : Fintype L]
    [ldec : DecidableEq L] (F : Type) [ff : Field F] [ffin : Fintype F]
    [hp : Fact (Nat.Prime (ringChar F))] [hq : Fact (Fintype.card F = 2)]
    [alg : Algebra F L] (β : Fin r → L) [hli : Fact (LinearIndependent F β)]
    {ℓ 𝓡 : ℕ} [nℓ : NeZero ℓ] [n𝓡 : NeZero 𝓡] {hrate : ℓ + 𝓡 < r}
    (i : Fin r) (hi : i ≤ ℓ)
    (f : OracleFunction F β (h_ℓ_add_R_rate := hrate) i)
    (hclose : UDRClose F β (h_ℓ_add_R_rate := hrate) i hi f) :
    @UDRCodeword r nr L lf lfin ldec F ff ffin hp hq alg β hli ℓ 𝓡 nℓ n𝓡 hrate
      i hi f hclose = uniqueDecodingCodeword F β i hi f (by exact hclose) := rfl

#print axioms UDRCodeword_original_signature
#print axioms Binius.BinaryBasefold.Compatibility.UDRCodeword_eq_canonical
#print axioms Binius.BinaryBasefold.UDRCodeword_eq_of_close
#print axioms Binius.BinaryBasefold.UDRCodeword_constFunc_eq_self
#print axioms Binius.BinaryBasefold.UDRCodeword_mem_BBF_Code
#print axioms Binius.BinaryBasefold.dist_to_UDRCodeword_le_uniqueDecodingRadius

end Binius.BinaryBasefold.Compatibility
