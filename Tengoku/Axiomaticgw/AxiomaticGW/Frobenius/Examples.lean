/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Coalgebra
public import Tengoku.Seed.RingTheory.Finiteness.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Frobenius algebra examples

This file is the home for concrete examples and API regression tests.

The first example is deliberately elementary, but its perfectness proof shows
the shape of the definitions.  `LinearMap.IsPerfPair` asks for bijectivity in
both arguments.  Lean's `constructor` tactic splits a conjunction-like goal
into its fields, while `intro` introduces variables and hypotheses.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace CommFrobeniusAlgebra

/-- The base ring is a Frobenius algebra over itself, with counit the identity
linear map. Its pairing is ordinary multiplication: `η(x, y) = x * y`.-/
def baseRing (R : Type*) [CommRing R] : CommFrobeniusAlgebra R R where
  counit := LinearMap.id
  isPerfPair := by
    -- Perfectness asks for bijectivity in the left and right arguments.
    constructor
    -- Left argument: x is sent to the functional y ↦ x * y.
    · constructor
      -- Injectivity: equal functionals are equal at 1, hence x = y.
      · intro x y h
        have h1 := DFunLike.congr_fun h 1
        simpa only [tracePairing_apply, mul_one, LinearMap.id_coe, id_eq]
          using h1
      -- Surjectivity: every linear functional f : R → R is multiplication by
      -- f(1), because linearity gives f(y) = y * f(1).
      · intro f
        refine ⟨f 1, ?_⟩
        apply LinearMap.ext
        intro y
        simpa only [tracePairing_apply, mul_comm, LinearMap.id_coe, id_eq,
          smul_eq_mul, mul_one] using (f.map_smul y 1).symm
    -- Right argument: the same proof works, using commutativity of R.
    · constructor
      · intro x y h
        have h1 := DFunLike.congr_fun h 1
        simpa only [LinearMap.flip_apply, tracePairing_apply, one_mul,
          LinearMap.id_coe, id_eq] using h1
      · intro f
        refine ⟨f 1, ?_⟩
        apply LinearMap.ext
        intro y
        simpa only [LinearMap.flip_apply, tracePairing_apply,
          LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
          using (f.map_smul y 1).symm

/-- In the base-ring example, the counit really is the identity function.
@isnad1 id=eq.0h2v.s7.edff2924d7e9 from=translated src=- shape=8a239b67 vocab=ed1dbad1
-/
@[simp]
theorem baseRing_counit_apply (R : Type*) [CommRing R] (x : R) :
    (baseRing R).counit x = x := rfl

/-- The derived Frobenius pairing on the base ring is multiplication.
@isnad1 id=eq.0h3v.s9.ea2eca5c0239 from=translated src=- shape=0903b29b vocab=90aeddde
-/
@[simp]
theorem baseRing_pairing_apply (R : Type*) [CommRing R] (x y : R) :
    (baseRing R).pairing.form x y = x * y := rfl

/-- The inverse metric for the pairing `η(x, y) = x * y` is `1 ⊗ 1`.

The proof applies the injective map `tensorEndEquiv` to both sides, reducing a
tensor equality to an equality of endomorphisms.  `ext x` then reduces that to
pointwise equality on an arbitrary element.
@isnad1 id=eq.0h1v.s7.2c60154b5206 from=translated src=- shape=4c2b1cc3 vocab=3b3a9ec1
-/
@[simp]
theorem baseRing_casimir (R : Type*) [CommRing R] :
    (baseRing R).casimir = 1 ⊗ₜ[R] 1 := by
  apply (baseRing R).pairing.tensorEndEquiv.injective
  apply LinearMap.ext
  intro x
  simp only [tensorEndEquiv_casimir, LinearMap.id_coe, id_eq,
    SymmetricPerfectPairing.tensorEndEquiv_tmul, pairing_apply, one_mul,
    baseRing_counit_apply, smul_eq_mul, mul_one]

/-- Multiplying the two legs of `1 ⊗ 1` gives the handle element `1`.
@isnad1 id=eq.0h1v.s5.6a7bba635b03 from=translated src=- shape=2fced6e6 vocab=b6b62549
-/
@[simp]
theorem baseRing_handleElement (R : Type*) [CommRing R] :
    (baseRing R).handleElement = 1 := by
  simp only [handleElement, baseRing_casimir, LinearMap.mul'_apply, mul_one]

/-! ## A rank-two example -/

/-- The functional `(x, y) ↦ x + y` on the product algebra `R × R`.-/
def productCounit (R : Type*) [CommRing R] : R × R →ₗ[R] R where
  toFun x := x.1 + x.2
  map_add' x y := by
    dsimp
    ac_rfl
  map_smul' r x := by
    simp only [Prod.smul_fst, smul_eq_mul, Prod.smul_snd, RingHom.id_apply,
      mul_add]

/-- Evaluation of the product counit.
@isnad1 id=eq.0h2v.s7.7a6af7ded19e from=translated src=- shape=54ccb1d9 vocab=59c0a250
-/
@[simp]
theorem productCounit_apply (R : Type*) [CommRing R] (x : R × R) :
    productCounit R x = x.1 + x.2 := rfl

/-- The product algebra `R × R`, with Frobenius functional `(x, y) ↦ x + y`.

Its trace pairing is the diagonal pairing
`η((a, b), (c, d)) = a * c + b * d`. The perfectness proof reconstructs an arbitrary
linear functional from its values on `(1,0)` and `(0,1)`.-/
def productAlgebra (R : Type*) [CommRing R] :
    CommFrobeniusAlgebra R (R × R) where
  counit := productCounit R
  isPerfPair := by
    constructor
    · constructor
      · intro x y h
        apply Prod.ext
        · have h₁ := DFunLike.congr_fun h (1, 0)
          simpa only [tracePairing_apply, productCounit_apply, Prod.fst_mul,
            mul_one, Prod.snd_mul, mul_zero, add_zero] using h₁
        · have h₂ := DFunLike.congr_fun h (0, 1)
          simpa only [tracePairing_apply, productCounit_apply, Prod.fst_mul,
            mul_zero, Prod.snd_mul, mul_one, zero_add] using h₂
      · intro f
        refine ⟨(f (1, 0), f (0, 1)), ?_⟩
        apply LinearMap.ext
        intro y
        have hy : y = y.1 • (1, 0) + y.2 • (0, 1) := by
          ext <;> simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
            Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
        have hfy := congrArg f hy
        change f (1, 0) * y.1 + f (0, 1) * y.2 = f y
        simpa only [map_add, map_smul, smul_eq_mul, mul_comm] using hfy.symm
    · constructor
      · intro x y h
        apply Prod.ext
        · have h₁ := DFunLike.congr_fun h (1, 0)
          simpa only [LinearMap.flip_apply, tracePairing_apply,
            productCounit_apply, Prod.fst_mul, one_mul, Prod.snd_mul,
            zero_mul, add_zero] using h₁
        · have h₂ := DFunLike.congr_fun h (0, 1)
          simpa only [LinearMap.flip_apply, tracePairing_apply,
            productCounit_apply, Prod.fst_mul, zero_mul, Prod.snd_mul,
            one_mul, zero_add] using h₂
      · intro f
        refine ⟨(f (1, 0), f (0, 1)), ?_⟩
        apply LinearMap.ext
        intro y
        have hy : y = y.1 • (1, 0) + y.2 • (0, 1) := by
          ext <;> simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
            Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
        have hfy := congrArg f hy
        change y.1 * f (1, 0) + y.2 * f (0, 1) = f y
        simpa only [map_add, map_smul, smul_eq_mul] using hfy.symm

/-- The product pairing is diagonal.
@isnad1 id=eq.0h3v.s9.a2333422ef64 from=translated src=- shape=67514b80 vocab=564536bf
-/
theorem productAlgebra_pairing_apply (R : Type*) [CommRing R]
    (x y : R × R) :
    (productAlgebra R).pairing.form x y = x.1 * y.1 + x.2 * y.2 := rfl

/-- The inverse metric of the diagonal product pairing is the sum of the two
coordinate idempotents.
@isnad1 id=eq.0h1v.s10.a7f6e13b0444 from=translated src=- shape=4a873b00 vocab=8f4148ab
-/
@[simp]
theorem productAlgebra_casimir (R : Type*) [CommRing R] :
    (productAlgebra R).casimir =
      (1, 0) ⊗ₜ[R] (1, 0) + (0, 1) ⊗ₜ[R] (0, 1) := by
  apply (productAlgebra R).pairing.tensorEndEquiv.injective
  apply LinearMap.ext
  intro x
  apply Prod.ext <;>
    simp only [productAlgebra, productCounit, tensorEndEquiv_casimir,
      LinearMap.id_coe, id_eq, map_add, LinearMap.add_apply,
      SymmetricPerfectPairing.tensorEndEquiv_tmul, pairing_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, one_mul, Prod.snd_mul,
      zero_mul, add_zero, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
      zero_add, Prod.mk_add_mk, Prod.mk.eta]

/-- Comultiplication acts diagonally on the two coordinate idempotents.
@isnad1 id=eq.0h2v.s11.f00d94b3a031 from=translated src=- shape=f7aa9d89 vocab=cdc7bd2f
-/
@[simp]
theorem productAlgebra_comul (R : Type*) [CommRing R] (x : R × R) :
    (productAlgebra R).comul x =
      (x.1, 0) ⊗ₜ[R] (1, 0) + (0, x.2) ⊗ₜ[R] (0, 1) := by
  rw [comul_apply, productAlgebra_casimir, mul_add]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  have hx₁ : x * ((1, 0) : R × R) = (x.1, 0) := by
    ext <;> simp only [Prod.fst_mul, Prod.snd_mul, mul_one, mul_zero]
  have hx₂ : x * ((0, 1) : R × R) = (0, x.2) := by
    ext <;> simp only [Prod.fst_mul, Prod.snd_mul, mul_zero, mul_one]
  rw [hx₁, hx₂, one_mul, one_mul]

/-- The handle element of the product Frobenius algebra is its unit.
@isnad1 id=eq.0h1v.s6.69e50e2630ce from=translated src=- shape=4ced6b77 vocab=37334c37
-/
@[simp]
theorem productAlgebra_handleElement (R : Type*) [CommRing R] :
    (productAlgebra R).handleElement = 1 := by
  simp only [handleElement, productAlgebra_casimir, map_add,
    LinearMap.mul'_apply, Prod.mk_mul_mk, mul_one, mul_zero, Prod.mk_add_mk,
    add_zero, zero_add, Prod.mk_eq_one, and_self]

end CommFrobeniusAlgebra

end AxiomaticGW
