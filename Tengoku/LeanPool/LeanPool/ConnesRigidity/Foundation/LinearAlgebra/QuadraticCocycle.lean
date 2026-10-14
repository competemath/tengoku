/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `deancureton/ten-proofs`,
`ConnesRigidity/ArithmeticCocycle.lean` at
66af8383b1dbc53e21ceefc917a503b9bd88df51, lines 16-243.
Modifications: isolated the finite and integral cocycle calculations, narrowed
imports, and changed the namespace. See the upstream PORT_MAP.md.
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.LinearAlgebra.ArithmeticSymplectic
public import Tengoku

/-!
The quadratic cocycle component of the Connes rigidity formalization.
-/

@[expose] public section

namespace Connes
namespace OpenAIPort

open Matrix

/--
The `ModTwoSymplecticGroup` construction used in the Connes rigidity formalization.
-/
abbrev ModTwoSymplecticGroup :=
  Matrix.symplecticGroup (Fin 2) (ZMod 2)

instance modTwoSymplecticGroupDecidableMem : DecidablePred
    (fun A : Matrix SymplecticIndex SymplecticIndex (ZMod 2) =>
      A ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  fun A => decidable_of_iff
    (A * Matrix.J (Fin 2) (ZMod 2) * Matrix.transpose A =
      Matrix.J (Fin 2) (ZMod 2))
    (SymplecticGroup.mem_iff).symm

instance : Fintype ModTwoSymplecticGroup :=
  Subtype.fintype _

/- Reduction of integral symplectic matrices. Paper: §2.
-/
/--
The `reducedSymplecticHom` construction used in the Connes rigidity formalization.
-/
def reducedSymplecticHom :
    IntegralSymplecticGroup →* ModTwoSymplecticGroup where
  toFun g :=
    ⟨(g.1 : Matrix SymplecticIndex SymplecticIndex ℤ).map
        (Int.castRingHom (ZMod 2)),
      SymplecticGroup.map_mem g.2 (Int.castRingHom (ZMod 2))⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one (Int.castRingHom (ZMod 2)) (map_zero _) (map_one _)
  map_mul' g h := by
    apply Subtype.ext
    ext i j
    simp [Matrix.mul_apply]

/-- Evaluation of matrix reduction. Paper: §2.
@isnad1 id=eq.0h1v.s13.24d17ae2ee3e from=translated src=- shape=1031daba vocab=0d751059
-/
@[simp] theorem reducedSymplecticHom_coe (g : IntegralSymplecticGroup) :
    (reducedSymplecticHom g : Matrix SymplecticIndex SymplecticIndex (ZMod 2)) =
      reducedMatrixHom g := rfl

instance : DistribMulAction ModTwoSymplecticGroup ModTwoSpace :=
  DistribMulAction.compHom ModTwoSpace
    (Matrix.symplecticGroup (Fin 2) (ZMod 2)).subtype

/- A coordinate vector for the finite symplectic space. Paper: §2.
-/
/--
The `modTwoBasis` construction used in the Connes rigidity formalization.
-/
def modTwoBasis (i : SymplecticIndex) : ModTwoSpace :=
  Pi.single i 1

/-- The source-shaped quadratic cocycle. Paper: §2.
-/
def finiteQuadraticCocycle (g : ModTwoSymplecticGroup) : ModTwoSpace
  | Sum.inl i =>
      standardQuadraticForm (g⁻¹ • modTwoBasis (Sum.inr i)) +
        standardQuadraticForm (modTwoBasis (Sum.inr i))
  | Sum.inr i =>
      standardQuadraticForm (g⁻¹ • modTwoBasis (Sum.inl i)) +
        standardQuadraticForm (modTwoBasis (Sum.inl i))

/-- Dot-product form of the alternating pairing. Paper: §2.
@isnad1 id=eq.0h2v.s7.a3800c52aa83 from=translated src=- shape=604b0f95 vocab=8a83e557
-/
theorem modTwoSymplecticForm_eq_dotProduct (x y : ModTwoSpace) :
    modTwoSymplecticForm x y =
      dotProduct x ((Matrix.J (Fin 2) (ZMod 2)).mulVec y) := by
  simp [modTwoSymplecticForm, Matrix.J, Matrix.mulVec, dotProduct]
  abel

/- Symplectic invariance of the alternating pairing. Paper: §2. -/
/--
@isnad1 id=eq.0h3v.s12.9f6ce0b73916 from=translated src=- shape=7b79625e vocab=154c7608
-/
theorem modTwoSymplecticForm_smul
    (g : ModTwoSymplecticGroup) (x y : ModTwoSpace) :
    modTwoSymplecticForm (g • x) (g • y) = modTwoSymplecticForm x y := by
  rw [modTwoSymplecticForm_eq_dotProduct, modTwoSymplecticForm_eq_dotProduct]
  change dotProduct (g.1.mulVec x)
      ((Matrix.J (Fin 2) (ZMod 2)).mulVec (g.1.mulVec y)) =
    dotProduct x ((Matrix.J (Fin 2) (ZMod 2)).mulVec y)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [SymplecticGroup.mem_iff'.mp g.2]
  rw [← Matrix.dotProduct_mulVec]

/- Additivity in the second argument. Paper: §2. -/
/--
@isnad1 id=eq.0h3v.s7.fec912f9ea1f from=translated src=- shape=1f2d97f4 vocab=64be2653
-/
theorem modTwoSymplecticForm_add_right (x y z : ModTwoSpace) :
    modTwoSymplecticForm x (y + z) =
      modTwoSymplecticForm x y + modTwoSymplecticForm x z := by
  simp [modTwoSymplecticForm, mul_add, Finset.sum_add_distrib]
  abel

/- The quadratic defect as a linear map. Paper: §2.
-/
/--
The `quadraticDefectLinear` construction used in the Connes rigidity formalization.
-/
def quadraticDefectLinear (g : ModTwoSymplecticGroup) :
    ModTwoSpace →ₗ[ZMod 2] ZMod 2 where
  toFun w := standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w
  map_add' x y := by
    change
      standardQuadraticForm ((g⁻¹).1.mulVec (x + y)) +
          standardQuadraticForm (x + y) =
        standardQuadraticForm ((g⁻¹).1.mulVec x) + standardQuadraticForm x +
          (standardQuadraticForm ((g⁻¹).1.mulVec y) + standardQuadraticForm y)
    rw [Matrix.mulVec_add, standardQuadraticForm_add, standardQuadraticForm_add]
    have hinv := modTwoSymplecticForm_smul g⁻¹ x y
    change modTwoSymplecticForm ((g⁻¹).1.mulVec x) ((g⁻¹).1.mulVec y) =
      modTwoSymplecticForm x y at hinv
    rw [hinv]
    have hcancel :
        modTwoSymplecticForm x y + modTwoSymplecticForm x y = 0 :=
      CharTwo.add_self_eq_zero _
    calc
      standardQuadraticForm ((g⁻¹).1.mulVec x) +
            standardQuadraticForm ((g⁻¹).1.mulVec y) +
            modTwoSymplecticForm x y +
          (standardQuadraticForm x + standardQuadraticForm y +
            modTwoSymplecticForm x y) =
          (standardQuadraticForm ((g⁻¹).1.mulVec x) + standardQuadraticForm x) +
            (standardQuadraticForm ((g⁻¹).1.mulVec y) + standardQuadraticForm y) +
              (modTwoSymplecticForm x y + modTwoSymplecticForm x y) := by abel
      _ = _ := by rw [hcancel]; simp
  map_smul' c x := by
    change
      standardQuadraticForm ((g⁻¹).1.mulVec (c • x)) +
          standardQuadraticForm (c • x) =
        c * (standardQuadraticForm ((g⁻¹).1.mulVec x) + standardQuadraticForm x)
    rw [Matrix.mulVec_smul]
    have hc : c ^ 2 = c := by
      revert c
      decide
    simp [standardQuadraticForm]
    ring_nf
    rw [hc]

/-- The pairing functional associated to a finite vector. Paper: §2.
-/
def symplecticFunctional (d : ModTwoSpace) :
    ModTwoSpace →ₗ[ZMod 2] ZMod 2 where
  toFun w := modTwoSymplecticForm d w
  map_add' := modTwoSymplecticForm_add_right d
  map_smul' c w := by
    simp [modTwoSymplecticForm]
    ring

/-- The quadratic defect is represented by its source cocycle. Paper: §2.
@isnad1 id=eq.0h2v.s12.4dec1c940899 from=translated src=- shape=ff7f44ec vocab=2e171e02
-/
theorem finiteQuadraticCocycle_defining_identity
    (g : ModTwoSymplecticGroup) (w : ModTwoSpace) :
    standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w =
      modTwoSymplecticForm (finiteQuadraticCocycle g) w := by
  have heq :
      quadraticDefectLinear g =
        symplecticFunctional (finiteQuadraticCocycle g) := by
    apply (Pi.basisFun (ZMod 2) SymplecticIndex).ext
    intro i
    rcases i with i | i
    · fin_cases i <;>
        simp [quadraticDefectLinear, symplecticFunctional, finiteQuadraticCocycle,
          modTwoSymplecticForm, modTwoBasis, Pi.basisFun]
    · fin_cases i <;>
        simp [quadraticDefectLinear, symplecticFunctional, finiteQuadraticCocycle,
          modTwoSymplecticForm, modTwoBasis, Pi.basisFun]
  exact LinearMap.congr_fun heq w

/- Nondegeneracy of the coordinate pairing. Paper: §2. -/
/--
@isnad1 id=eq.1h2v.s4.5b98638fb909 from=translated src=- shape=0ccae21c vocab=30b6b300
-/
theorem modTwoSymplecticForm_nondegenerate {x y : ModTwoSpace}
    (h : ∀ w, modTwoSymplecticForm x w = modTwoSymplecticForm y w) :
    x = y := by
  funext i
  rcases i with i | i
  · fin_cases i
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inr 0))
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inr 1))
  · fin_cases i
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inl 0))
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inl 1))

/- Additivity in the first argument. Paper: §2. -/
/--
@isnad1 id=eq.0h3v.s7.71b26b7f7535 from=translated src=- shape=0cd70a10 vocab=64be2653
-/
theorem modTwoSymplecticForm_add_left (x y z : ModTwoSpace) :
    modTwoSymplecticForm (x + y) z =
      modTwoSymplecticForm x z + modTwoSymplecticForm y z := by
  simp [modTwoSymplecticForm, add_mul, Finset.sum_add_distrib]
  abel

/- Moving an action across the pairing. Paper: §2. -/
/--
@isnad1 id=eq.0h3v.s12.b405cb30f336 from=translated src=- shape=72202017 vocab=73da4276
-/
theorem modTwoSymplecticForm_smul_left
    (g : ModTwoSymplecticGroup) (x y : ModTwoSpace) :
    modTwoSymplecticForm (g • x) y =
      modTwoSymplecticForm x (g⁻¹ • y) := by
  rw [← modTwoSymplecticForm_smul g x (g⁻¹ • y)]
  simp

/- The finite quadratic map satisfies the cocycle law. Paper: §2. -/
/--
@isnad1 id=iscocycl.0h0v.s11.62e1f10853ad from=translated src=- shape=15cce6a8 vocab=376ca962
-/
theorem finiteQuadraticCocycle_isCocycle :
    groupCohomology.IsCocycle₁ finiteQuadraticCocycle := by
  intro g h
  apply modTwoSymplecticForm_nondegenerate
  intro w
  rw [← finiteQuadraticCocycle_defining_identity]
  rw [modTwoSymplecticForm_add_left, modTwoSymplecticForm_smul_left]
  rw [← finiteQuadraticCocycle_defining_identity]
  rw [← finiteQuadraticCocycle_defining_identity]
  rw [_root_.mul_inv_rev]
  simp only [mul_smul]
  have hcancel :
      standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm (g⁻¹ • w) = 0 :=
    CharTwo.add_self_eq_zero _
  rw [← add_zero
    (standardQuadraticForm (h⁻¹ • g⁻¹ • w) + standardQuadraticForm w),
    ← hcancel]
  abel

/- The integral reduction of the finite cocycle. Paper: §2.
-/
/--
The `integralQuadraticCocycle` construction used in the Connes rigidity formalization.
-/
def integralQuadraticCocycle (g : IntegralSymplecticGroup) : ModTwoSpace :=
  finiteQuadraticCocycle (reducedSymplecticHom g)

/- Reduction and integral actions agree on the finite carrier. Paper: §2. -/
/--
@isnad1 id=eq.0h2v.s13.c161cded2df7 from=translated src=- shape=390a236c vocab=2df1dbc8
-/
theorem reducedSymplecticHom_smul
    (g : IntegralSymplecticGroup) (w : ModTwoSpace) :
    reducedSymplecticHom g • w = g • w := rfl

/- The integral cocycle has the quadratic defining identity. Paper: §2. -/
/--
@isnad1 id=eq.0h2v.s12.7f289d855e68 from=translated src=- shape=2344782a vocab=a288f5fe
-/
theorem integralQuadraticCocycle_defining_identity
    (g : IntegralSymplecticGroup) (w : ModTwoSpace) :
    standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w =
      modTwoSymplecticForm (integralQuadraticCocycle g) w := by
  rw [← reducedSymplecticHom_smul g⁻¹ w, map_inv]
  exact finiteQuadraticCocycle_defining_identity (reducedSymplecticHom g) w

/- The integral reduction also satisfies the cocycle law. Paper: §2. -/
/--
@isnad1 id=iscocycl.0h0v.s11.00e07e933b49 from=translated src=- shape=421c9364 vocab=224577bb
-/
theorem integralQuadraticCocycle_isCocycle :
    groupCohomology.IsCocycle₁ integralQuadraticCocycle := by
  intro g h
  change finiteQuadraticCocycle (reducedSymplecticHom (g * h)) =
    g • finiteQuadraticCocycle (reducedSymplecticHom h) +
      finiteQuadraticCocycle (reducedSymplecticHom g)
  rw [map_mul, ← reducedSymplecticHom_smul]
  exact finiteQuadraticCocycle_isCocycle
    (reducedSymplecticHom g) (reducedSymplecticHom h)

end OpenAIPort
end Connes
