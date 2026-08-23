/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma

/-!
# Soundness and Knowledge Soundness of Duplex-Sponge Fiat-Shamir

This module establishes the main security theorems for the Duplex-Sponge Fiat-Shamir (DSFS)
transformation, namely soundness and knowledge soundness. We prove that the soundness and knowledge
soundness of DSFS reduce directly to the corresponding security properties of the basic,
unsalted/salted Fiat-Shamir transformation (as described in Section 6 of Chiesa-Orrù [CO25]).

These reductions crucially rely on the key lemma (Lemma 5.1 of [CO25]), which guarantees the
statistical indistinguishability of the interactive query-answer traces under the DSFS and basic FS
models, modulo the prover and trace transformations.
-/
