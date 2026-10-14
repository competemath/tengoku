/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Tengoku

/-!
# Representative-level `W^{1,p}`

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port stores concrete value and gradient
representatives and uses the `CKN` weak-gradient API.

## Main definitions

* `MemLpOn` and `GradMemLpOn`: scalar and coordinatewise `L^p` membership.
* `W1pFunction`: a concrete representative with a chosen weak gradient.
* `MemW1p`: representative-level membership in `W^{1,p}`.

## Main results

* `W1pFunction.restrict`: restriction to an open subset.
-/

@[expose] public section

open scoped ENNReal

namespace CKN

/-- Scalar `L^p` membership on a restricted domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)

/-- Coordinatewise gradient `L^p` membership on a restricted domain. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)

/-- A concrete representative and a chosen coordinate weak gradient. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  /-- Chosen scalar representative of the W¹ᵖ function. -/
  toFun : Vec d → ℝ
  /-- Chosen weak gradient of the W¹ᵖ representative. -/
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} :
    CoeFun (W1pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Representative-level membership of a concrete function in `W^{1,p}`. -/
def MemW1p {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  ∃ v : W1pFunction U p, v.toFun = u

/-- Restriction preserves scalar `L^p` membership.
@isnad1 id=memlpon.2h5v.s5.274efcb36610 from=translated src=- shape=93e5c27e vocab=ce9f2499
-/
theorem memLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemLpOn U p u) :
    MemLpOn V p u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set
    MeasureTheory.volume hVU)

/-- Restriction preserves coordinatewise gradient `L^p` membership.
@isnad1 id=gradmeml.2h5v.s5.1f4aac7a0c31 from=translated src=- shape=295311a9 vocab=105aec8a
-/
theorem gradMemLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemLpOn U p Du) :
    GradMemLpOn V p Du := by
  intro i
  exact memLpOn_mono hVU (hDu i)

namespace W1pFunction

/--
@isnad1 id=eq.2h5v.s5.63c7059ba78b from=translated src=- shape=4e0c0cca vocab=289ce2df
-/
@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u v : W1pFunction U p}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

/-- The chosen coordinate weak derivative stored in a W1p representative.
@isnad1 id=hasweakp.0h5v.s5.2f1d31cb5770 from=translated src=- shape=25e67ff9 vocab=b96e6fbf
-/
theorem hasWeakPartialDerivOn {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i

/-- The `i`th chosen gradient component belongs to `L^p(U)`.
@isnad1 id=memlpon.0h5v.s4.a8ab91cdfb3a from=translated src=- shape=37b445d2 vocab=ab92f751
-/
theorem grad_memLp {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (i : Fin d) :
    MemLpOn U p (fun x => u.grad x i) :=
  u.gradMemLp i

/-- The underlying representative belongs to representative-level `W^{1,p}`.
@isnad1 id=memw1p.0h4v.s4.c16bcb0f1045 from=translated src=- shape=454df48a vocab=12bc4436
-/
theorem memW1p {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞} (u : W1pFunction U p) :
    MemW1p U p u.toFun :=
  ⟨u, rfl⟩

/-- Restrict a representative-level Sobolev function to an open subset. -/
def restrict {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    W1pFunction V p where
  toFun := u.toFun
  grad := u.grad
  memLp := memLpOn_mono hVU u.memLp
  gradMemLp := gradMemLpOn_mono hVU u.gradMemLp
  hasWeakGradient := u.hasWeakGradient.restrict hVOpen hVU

end W1pFunction

end CKN
