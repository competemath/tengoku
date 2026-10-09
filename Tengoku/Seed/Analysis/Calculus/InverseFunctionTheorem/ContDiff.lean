/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
public import Tengoku.Seed.Analysis.Calculus.ContDiff.RCLike
public import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, `C^r` case

In this file we specialize the inverse function theorem to `C^r`-smooth functions.
-/

@[expose] public section

noncomputable section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
variable [CompleteSpace E] (f : E → F) {f' : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns an `OpenPartialHomeomorph` with `to_fun = f` and `a ∈ source`. -/
def toOpenPartialHomeomorph (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : n ≠ 0) : OpenPartialHomeomorph E F :=
  (hf.hasStrictFDerivAt' hf' hn).toOpenPartialHomeomorph f

variable {f}

/--
@isnad1 id=eq.3h7v.s8.586dc80dcbcd from=seed src=0 shape=b46f3b02 vocab=0b362e08
-/
@[simp]
theorem toOpenPartialHomeomorph_coe (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    (hf.toOpenPartialHomeomorph f hf' hn : E → F) = f :=
  rfl

/--
@isnad1 id=mem.3h7v.s8.cd20752c8ee7 from=seed src=0 shape=0241c655 vocab=c05f05d9
-/
theorem mem_toOpenPartialHomeomorph_source (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    a ∈ (hf.toOpenPartialHomeomorph f hf' hn).source :=
  (hf.hasStrictFDerivAt' hf' hn).mem_toOpenPartialHomeomorph_source

/--
@isnad1 id=mem.3h7v.s8.a4580c16c3a5 from=seed src=0 shape=00114e17 vocab=270fde77
-/
theorem image_mem_toOpenPartialHomeomorph_target (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    f a ∈ (hf.toOpenPartialHomeomorph f hf' hn).target :=
  (hf.hasStrictFDerivAt' hf' hn).image_mem_toOpenPartialHomeomorph_target

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : n ≠ 0) : F → E :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a

/--
@isnad1 id=eq.3h7v.s8.b336e037f0cd from=seed src=0 shape=057bea50 vocab=6a6b1c58
-/
theorem localInverse_apply_image (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `ContDiff.toOpenPartialHomeomorph`) is
also `ContDiff`.
@isnad1 id=contdiff.3h7v.s8.31ffed7dd857 from=seed src=0 shape=09944c83 vocab=6a6b1c58
-/
theorem to_localInverse (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert! hf'
  · convert! hf

end ContDiffAt
