/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
public import Tengoku

/-!
Kernel-checked shard 1 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

@[expose] public section

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 0 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.7624ca921c7c from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock0 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 0 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 1 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.57f238904c5b from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock1 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 1 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 2 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.17a57cf67d04 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock2 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 2 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 3 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.4175bf259bb5 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock3 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 3 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

end Sp4
end Connes
