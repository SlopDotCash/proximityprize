/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.EntropyVolumeUpperBall

/-!
# Compatibility import for the Hamming-ball entropy upper bound

The canonical proof of `CodingTheory.hammingBallVolume_le_qEntropy` now lives in
`ArkLib.Data.CodingTheory.EntropyVolumeUpperBall`. This file preserves the older import path without
redeclaring the same global theorem name, so aggregate imports can include both modules.
-/

-- Axiom audit for the re-exported theorem.
#print axioms CodingTheory.hammingBallVolume_le_qEntropy
