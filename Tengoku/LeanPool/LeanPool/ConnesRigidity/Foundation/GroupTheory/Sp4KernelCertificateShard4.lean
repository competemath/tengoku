/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
public import Tengoku

/-!
Kernel-checked shard 5 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

@[expose] public section

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 16 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.be5f85996519 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock16 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 16 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 17 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.6c7f3bce1503 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock17 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 17 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 18 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.df911b2b6a2c from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock18 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 18 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 19 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.8263a5da0aa7 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock19 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 19 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

end Sp4
end Connes
