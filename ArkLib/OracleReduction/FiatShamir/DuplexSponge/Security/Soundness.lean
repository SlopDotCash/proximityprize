/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma

/-!
# Soundness and Knowledge Soundness of Duplex-Sponge Fiat-Shamir (placeholder)

**Status: placeholder module with no declarations.** This file currently consists of the import
of `Security/KeyLemma.lean` and this docstring only. It does **not** state or prove soundness or
knowledge soundness of the Duplex-Sponge Fiat-Shamir (DSFS) transformation, and nothing in this
module should be cited as a DSFS security theorem.

Intended content (not yet formalized here): following Section 6 of Chiesa-Orrù [CO25], reduce
the soundness and knowledge soundness of DSFS to the corresponding security properties of the
basic (unsalted/salted) Fiat-Shamir transformation. In the paper these reductions rely on the
key lemma (Lemma 5.1 of [CO25]), which bounds the statistical distance between the DSFS and
basic-FS query-answer traces, modulo the prover and trace transformations.

The imported key-lemma module does not discharge Lemma 5.1:
`DuplexSpongeFS.duplexSpongeToFSGameStatDist` takes the named residual `KeyLemmaResidual` as an
explicit hypothesis (see also `KeyLemmaAssembly.lean`, which reduces the eager variant to
hybrid-step residuals). Any DSFS soundness theorem added here on top of that interface would
therefore be conditional on the key-lemma residual until it is proved.
-/
