/-
Copyright (c) 2024 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Archimedean.Hom  -- shake: keep (Subsingleton (ℝ →+*o ℝ)), cf. lean#13417
public import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Algebra.Order.CompleteField

/-!
# Uniqueness of ring homomorphisms to the real numbers

This file contains results about ring homomorphisms to `ℝ`.

## Main results

* `Real.nonemptyOrderRingHom`: For any archimedean ordered field `α`, there exists
  a monotone ring homomorphism `α →+*o ℝ`.
* `Real.RingHom.unique`: There exists no nontrivial ring homomorphism `ℝ →+* ℝ`.
-/

public section

-- Note that we already know `Subsingleton (α →+*o ℝ)` here.
-- We intentionally do not define instance `Unique (α →+*o ℝ)` to avoid instance diamonds.
/--
@isnad1 id=nonempty.0h1v.s6.7d176117a81a from=seed src=0 shape=445132f8 vocab=b98c102d
-/
instance Real.nonemptyOrderRingHom (α : Type*)
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] : Nonempty (α →+*o ℝ) :=
  ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingHom α ℝ⟩

/--
@isnad1 id=monotone.1h3v.s7.1c9434e69691 from=seed src=0 shape=1e329e29 vocab=a2ac630f
-/
theorem ringHom_monotone {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [Ring S] [LinearOrder S] [IsOrderedAddMonoid S] [PosMulMono S]
    (hR : ∀ r : R, 0 ≤ r → IsSquare r) (f : R →+* S) : Monotone f :=
  (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

/-- There exists no nontrivial ring homomorphism `ℝ →+* ℝ`. -/
instance Real.RingHom.unique : Unique (ℝ →+* ℝ) where
  default := RingHom.id ℝ
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (ℝ →+*o ℝ) _
      ⟨f, ringHom_monotone (fun _ ↦ Real.isSquare_iff.mpr) f⟩ default)

/--
@isnad1 id=eq.0h3v.s5.0463f6d9cff4 from=seed src=0 shape=13a72bfa vocab=a87faf02
-/
@[simp]
theorem Real.ringHom_apply {F : Type*} [FunLike F ℝ ℝ] [RingHomClass F ℝ ℝ] (f : F) (r : ℝ) :
    f r = r :=
  DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r
