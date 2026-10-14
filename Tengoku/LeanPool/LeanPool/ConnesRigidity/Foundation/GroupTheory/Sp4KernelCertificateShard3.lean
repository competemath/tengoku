/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
public import Tengoku

/-!
Kernel-checked shard 4 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

@[expose] public section

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 12 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.b3c721f3583d from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock12 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 12 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 13 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.cc73baaeddc3 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock13 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 13 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 14 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.026cc63613ff from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock14 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 14 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 15 (with indices 0 through 31).
@isnad1 id=eq.0h3v.s6.f583c0b79143 from=translated src=- shape=28ff5f83 vocab=7d2e4c86
-/
theorem kernelDetectorBlock15 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 15 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

end Sp4
end Connes
