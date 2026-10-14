/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
public import Tengoku

/-!
Kernel-checked shard 3 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

@[expose] public section

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 8 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.7668536e5133 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock8 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 8 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 9 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.7c5c33fa9872 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock9 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 9 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 10 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.f4dfde8d4cc4 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock10 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 10 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 11 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.b68733cdb679 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock11 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 11 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

end Sp4
end Connes
