/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.RatFuncDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiation on `Frac(K[X])`

The affine-transport layer uses Mathlib's generic `FractionRing K[X]`, while
the explicit quotient-rule derivative is most naturally constructed on
`RatFunc K`.  These fields are canonically equivalent.  This file transports
the derivative across their `K`-algebra equivalence and proves that it still
extends formal polynomial differentiation.
-/

noncomputable section

open Polynomial

namespace JacobianTwo.FractionRingDerivative

open JacobianTwo.RatFuncDerivative

variable {K : Type*} [Field K]

/-- The canonical `K`-algebra equivalence between rational functions and the
generic fraction ring.-/
def ratFuncFractionRingEquiv :
    RatFunc K ≃ₐ[K] FractionRing K[X] :=
  RatFunc.toFractionRingAlgEquiv K K

/-- The quotient-rule derivative transported to `FractionRing K[X]`.-/
def fractionRingDerivative :
    Derivation K (FractionRing K[X]) (FractionRing K[X]) :=
  rationalDerivativeDerivation.liftOfRightInverse
    ratFuncFractionRingEquiv.apply_symm_apply
    (fun x hx => by
      have hx0 : x = 0 := ratFuncFractionRingEquiv.injective (by simpa using hx)
      subst x
      simp)

@[simp]
theorem fractionRingDerivative_apply (x : FractionRing K[X]) :
    fractionRingDerivative x = ratFuncFractionRingEquiv
      (rationalDerivative (ratFuncFractionRingEquiv.symm x)) := by
  change fractionRingDerivative
      (ratFuncFractionRingEquiv (ratFuncFractionRingEquiv.symm x)) = _
  unfold fractionRingDerivative
  rw [Derivation.liftOfRightInverse_apply]
  rfl

@[simp]
theorem ratFuncFractionRingEquiv_algebraMap (p : K[X]) :
    ratFuncFractionRingEquiv (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (FractionRing K[X]) p := by
  change (RatFunc.toFractionRingAlgEquiv K K[X])
      (algebraMap K[X] (RatFunc K) p) =
    algebraMap K[X] (FractionRing K[X]) p
  exact (RatFunc.toFractionRingAlgEquiv K K[X]).commutes p

/-- The transported derivation agrees with the ordinary derivative on the
embedded polynomial ring.-/
@[simp]
theorem fractionRingDerivative_algebraMap (p : K[X]) :
    fractionRingDerivative (algebraMap K[X] (FractionRing K[X]) p) =
      algebraMap K[X] (FractionRing K[X]) (derivative p) := by
  rw [← ratFuncFractionRingEquiv_algebraMap p,
    fractionRingDerivative_apply, ratFuncFractionRingEquiv.symm_apply_apply,
    rationalDerivative_algebraMap, ratFuncFractionRingEquiv_algebraMap]

/-- In characteristic zero, the constants of the transported derivation are
exactly the embedded elements of `K`.-/
theorem fractionRingDerivative_eq_zero_iff [CharZero K]
    (x : FractionRing K[X]) :
    fractionRingDerivative x = 0 ↔
      ∃ c : K, x = algebraMap K (FractionRing K[X]) c := by
  constructor
  · intro hx
    have hpreimage :
        rationalDerivative (ratFuncFractionRingEquiv.symm x) = 0 := by
      apply ratFuncFractionRingEquiv.injective
      rw [map_zero]
      simpa only [fractionRingDerivative_apply] using hx
    obtain ⟨c, hc⟩ :=
      (rationalDerivative_eq_zero_iff (ratFuncFractionRingEquiv.symm x)).1
        hpreimage
    refine ⟨c, ?_⟩
    calc
      x = ratFuncFractionRingEquiv (ratFuncFractionRingEquiv.symm x) :=
        (ratFuncFractionRingEquiv.apply_symm_apply x).symm
      _ = ratFuncFractionRingEquiv (RatFunc.C c) := by rw [hc]
      _ = algebraMap K (FractionRing K[X]) c := by
        rw [← RatFunc.algebraMap_eq_C]
        exact ratFuncFractionRingEquiv.commutes c
  · rintro ⟨c, rfl⟩
    exact fractionRingDerivative.map_algebraMap c

end JacobianTwo.FractionRingDerivative
