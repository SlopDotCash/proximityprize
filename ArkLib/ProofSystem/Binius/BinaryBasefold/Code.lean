/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
# Binary Basefold code compatibility layer

The core Binary Basefold code definitions now live in `Prelude`/`Basic`.  This file remains as the
stable import point for downstream soundness files and houses derived codeword helpers that are not
part of the basic protocol surface.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

noncomputable section SoundnessTools

end SoundnessTools

end Binius.BinaryBasefold
