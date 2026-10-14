/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
public import Tengoku

/-!
Kernel-checked shard 8 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

@[expose] public section

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 28 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.97e703da6a6c from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock28 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 28 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 29 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.7a4255364a20 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock29 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 29 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 30 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.a398f57a9495 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock30 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 30 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 31 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.b8f67f61eb7d from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock31 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 31 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

end Sp4
end Connes
