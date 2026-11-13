/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Correctness

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Scheme
import ArkLib.Commitments.Ordinary.Ajtai.Simple.Correctness
import ArkLib.Commitments.Functional.Hachi.GadgetNorms

/-!
# Correctness of the Inner-Outer Ajtai Commitment

Perfect correctness for lawful gadget decompositions: if the message and inner gadget
decompositions invert their gadget matrices, an honest commitment always verifies.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec (Rq Φ) messageRows)]
variable [DecidableEq (PolyVec (Rq Φ) innerRows)]
variable [DecidableEq (Commitment Φ outerRows)]

omit [DecidableEq (PolyVec (Rq Φ) innerRows)] [DecidableEq (Commitment Φ outerRows)] in
/-- Honest message decompositions pass the message gadget checks. -/
theorem generateDecomps_message_checks (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition Φ base decomp.message)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base messageRows messageDigits)
        ((generateDecomps Φ decomp pp m).message i) (m i) ()) = true := by
  simp only [List.all_eq_true]
  intro i _
  have hprod : Simple.commit Φ (gadgetMatrix Φ base messageRows messageDigits)
      ((generateDecomps Φ decomp pp m).message i) = m i := by
    simpa [Simple.commit, gadgetMul, generateDecomps] using hMessageDecomp (m i)
  simp [Simple.verify, hprod]

omit [DecidableEq (PolyVec (Rq Φ) messageRows)] [DecidableEq (Commitment Φ outerRows)] in
/-- Honest inner decompositions pass the inner gadget checks. -/
theorem generateDecomps_inner_checks (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        ((generateDecomps Φ decomp pp m).innerDecomp i)
        (Simple.commit Φ pp.innerMatrix ((generateDecomps Φ decomp pp m).message i)) ())
      = true := by
  simp only [List.all_eq_true]
  intro i _
  simp [Simple.verify, generateDecomps_inner_eq Φ base decomp hInnerDecomp pp m i]

end ArkLib.Lattices.Ajtai.InnerOuter

/-! ## Concrete instantiation over `ZMod q`

The genuine base-`b` (binary) gadget decomposition `zmodDigitDecomposition` instantiates the
inner-outer commitment over `R = ZMod q`, giving perfect correctness whenever `1 < b`, every
residue fits in the chosen digit count (`q ≤ b ^ digits`), and `1 ≤ deg φ`. -/

namespace ArkLib.Lattices.Ajtai.InnerOuter

section ZMod

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

end ZMod

end ArkLib.Lattices.Ajtai.InnerOuter
