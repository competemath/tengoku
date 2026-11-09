/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.NumberTheory.LocalField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Basic structure of nonarchimedean local fields

Compactness facts and the normalized integer-valued valuation attached to a
nonarchimedean local field.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The normalized integer valuation attached to a nonarchimedean local field.

It is obtained by transporting the value group to `WithZero (Multiplicative Int)` and then taking
the exponent of the nonzero value of a field unit.-/
noncomputable def v (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ → Int :=
  fun x =>
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        (by simp))

/-- The normalized integer valuation is obtained by transporting the field valuation to
multiplicative integers and taking its additive exponent.
@isnad1 id=eq.0h2v.s9.1ddf4a2b6818 from=translated src=- shape=ce51ed52 vocab=5da952ac
-/
@[simp]
theorem v_apply (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    v K x =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
          (by simp)) :=
  rfl

/-- Every integer occurs as the normalized valuation of a nonzero field element.
@isnad1 id=surjecti.0h1v.s5.ecc2381bc787 from=translated src=- shape=c3c038e0 vocab=8edc8e67
-/
theorem v_surjective (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (v K) := by
  intro n
  let γ : ValuativeRel.ValueGroupWithZero K :=
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm
      ((Multiplicative.ofAdd n : Multiplicative Int) : WithZero (Multiplicative Int))
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
  have hγ_ne : γ ≠ 0 := by
    dsimp [γ]
    simp
  have ha0 : a ≠ 0 := by
    intro h
    apply hγ_ne
    simpa [h] using ha.symm
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  simp [v, γ, ha]

/-- The normalized valuation turns multiplication of field units into addition of integers.
@isnad1 id=eq.0h3v.s9.5eee4c2718e5 from=translated src=- shape=0ead4374 vocab=8fb314a5
-/
theorem v_mul (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x * y)) =
      v K (Additive.ofMul x) + v K (Additive.ofMul y) := by
  simp [v, Valuation.map_mul, WithZero.unzero_mul, toAdd_mul]

/-- The normalized valuation of the multiplicative identity is zero.
@isnad1 id=eq.0h1v.s7.0285eb494b18 from=translated src=- shape=1356f0e1 vocab=0c48d424
-/
@[simp]
theorem v_one (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    v K (Additive.ofMul (1 : Kˣ)) = 0 := by
  dsimp [v]
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (((1 : Kˣ) : K))))
        (by simp) = (1 : Multiplicative Int) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp
  rw [hunzero]
  exact toAdd_one

/-- The normalized valuation of an inverse is the negative of the original valuation.
@isnad1 id=eq.0h2v.s8.9feabd59639e from=translated src=- shape=b3cf44bc vocab=24182e06
-/
theorem v_inv (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x) := by
  have hmul := v_mul K x x⁻¹
  rw [mul_inv_cancel, v_one] at hmul
  omega

/-- The normalized valuation of a quotient is the difference of the two valuations.
@isnad1 id=eq.0h3v.s9.c4710caad548 from=translated src=- shape=0ead4374 vocab=0277a5eb
-/
theorem v_div (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x / y)) =
      v K (Additive.ofMul x) - v K (Additive.ofMul y) := by
  rw [div_eq_mul_inv, v_mul, v_inv, sub_eq_add_neg]

/-- Raising a field unit to a natural power multiplies its normalized valuation by that power.
@isnad1 id=eq.0h3v.s8.1f7a42a44908 from=translated src=- shape=58512f47 vocab=b7785761
-/
theorem v_pow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat) :
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x) := by
  induction n with
  | zero =>
      rw [pow_zero, v_one]
      simp
  | succ n ih =>
      rw [pow_succ, v_mul, ih]
      rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by simp]
      ring

/-- Raising a field unit to an integral power multiplies its normalized valuation by that integer.
Raising a field unit to an integral power multiplies its normalized valuation by that integer.
@isnad1 id=eq.0h3v.s8.3df1c812c932 from=translated src=- shape=4e922046 vocab=2235b726
-/
theorem v_zpow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int) :
    v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x) := by
  cases n with
  | ofNat n =>
      simpa using v_pow K x n
  | negSucc n =>
      rw [zpow_negSucc, v_inv, v_pow]
      change -(((n + 1 : Nat) : Int) * v K (Additive.ofMul x)) =
        (-(((n + 1 : Nat) : Int))) * v K (Additive.ofMul x)
      ring

/-- A nonarchimedean local field contains a unit representative of normalized valuation one.
@isnad1 id=ex.0h1v.s7.ead8420f440a from=translated src=- shape=63a641b7 vocab=0c48d424
-/
theorem v_uniformiser (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ ϖ : Kˣ, v K (Additive.ofMul ϖ) = 1 := by
  obtain ⟨x, hx⟩ := v_surjective K 1
  exact ⟨Additive.toMul x, hx⟩

/-- The canonical inclusion of valuation-integer units into field units.-/
def integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K).toMonoidHom

/-- The inclusion of valuation-ring units into field units preserves the underlying field element.
The inclusion of valuation-ring units into field units preserves the underlying field element.
@isnad1 id=eq.0h2v.s11.9935dedeb210 from=translated src=- shape=8d595e32 vocab=9f09afb2
-/
@[simp]
theorem integerUnitsToFieldUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((integerUnitsToFieldUnits K x : Kˣ) : K) = (((x : 𝒪[K]ˣ) : 𝒪[K]) : K) :=
  rfl

/-- The canonical inclusion of valuation-integer units into field units is
injective.
@isnad1 id=injectiv.0h1v.s11.a97dcad22c1c from=translated src=- shape=f903f34c vocab=016c065b
-/
theorem integerUnitsToFieldUnits_injective
    (K : Type u) [Field K] [ValuativeRel K] :
    Function.Injective (integerUnitsToFieldUnits K) := by
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  simpa [integerUnitsToFieldUnits] using congrArg Units.val hxy

/-- A valuation-integer unit has normalized valuation zero as a field unit.
@isnad1 id=eq.0h2v.s11.7240e4e9cca3 from=translated src=- shape=dc16dbdf vocab=3819bb8b
-/
@[simp]
theorem v_integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ) :
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0 := by
  have hxv :
      ValuativeRel.valuation K ((integerUnitsToFieldUnits K x : Kˣ) : K) = 1 := by
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) x)
  rw [v_apply]
  apply (WithZero.toAdd_unzero_eq_iff _ 0).2
  change
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
        (ValuativeRel.valuation K
          ((integerUnitsToFieldUnits K x : Kˣ) : K)) =
      ((Multiplicative.ofAdd (0 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int))
  rw [hxv, map_one]
  rfl

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
