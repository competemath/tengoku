/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.KernelRank
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.BilinearLattice
import Tengoku.Seed.LinearAlgebra.Matrix.DotProduct
import Tengoku.Seed.LinearAlgebra.StdBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

section KerCompare

variable {R ι : Type*} [CommRing R] [Fintype ι]

/--
@isnad1 id=eq.1h4v.s5.8d1a832d95fc from=translated src=- shape=7c0d25c4 vocab=18881c2a
-/
theorem vecMul_eq_mulVec_of_isSymm {A : Matrix ι ι R} (hA : A.IsSymm) (z : ι → R) :
    z ᵥ* A = A *ᵥ z := by
  rw [← Matrix.vecMul_transpose, hA.eq]

/--
@isnad1 id=eq.1h3v.s11.6170e1fceb02 from=translated src=- shape=3ff7be78 vocab=4ff220a3
-/
theorem ker_toBilin'_eq_ker_mulVecLin [DecidableEq ι] {A : Matrix ι ι R}
    (hA : A.IsSymm) :
    LinearMap.ker (Matrix.toBilin' A) = LinearMap.ker A.mulVecLin := by
  ext z
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hz
    refine dotProduct_eq_zero_iff.mp fun w => ?_
    have hw := congrArg (fun φ : (ι → R) →ₗ[R] R => φ w) hz
    simp only [LinearMap.zero_apply] at hw
    rwa [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      vecMul_eq_mulVec_of_isSymm hA] at hw
  · intro hz
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      vecMul_eq_mulVec_of_isSymm hA, hz]
    simp

end KerCompare

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
@isnad1 id=issymm.0h3v.s5.3612cf2285c3 from=translated src=- shape=9bbb9fae vocab=d17353c3
-/
theorem localGramMatrixRat_isSymm (x : V) : (localGramMatrixRat G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => by
    change ((localGramMatrix G x C B : ℤ) : ℚ) = ((localGramMatrix G x B C : ℤ) : ℚ)
    exact congrArg (fun n : ℤ => (n : ℚ)) (localGramMatrix_comm G x C B)

def ratGramFormOnPi (x : V) :
    LinearMap.BilinForm ℚ (SecondSubconstituent G x → ℚ) :=
  Matrix.toBilin' (localGramMatrixRat G x)

/--
@isnad1 id=eq.0h5v.s9.b7152f76586f from=translated src=- shape=f2711bdd vocab=dc8bd5e4
-/
theorem ratGramFormOnPi_apply (x : V) (v w : SecondSubconstituent G x → ℚ) :
    ratGramFormOnPi G x v w = v ⬝ᵥ (localGramMatrixRat G x *ᵥ w) :=
  Matrix.toBilin'_apply' _ _ _

/--
@isnad1 id=issymm.0h3v.s6.0703f9d0f986 from=translated src=- shape=5838eae1 vocab=dc0158d3
-/
theorem ratGramFormOnPi_isSymm (x : V) : (ratGramFormOnPi G x).IsSymm := by
  rw [ratGramFormOnPi, Matrix.isSymm_toBilin'_iff_isSymm]
  exact localGramMatrixRat_isSymm G x

/--
@isnad1 id=isrefl.0h3v.s6.55b9ef793af7 from=translated src=- shape=5838eae1 vocab=db13084a
-/
theorem ratGramFormOnPi_isRefl (x : V) : (ratGramFormOnPi G x).IsRefl :=
  (ratGramFormOnPi_isSymm G x).isRefl

/--
@isnad1 id=eq.0h3v.s8.1ffdbd67b789 from=translated src=- shape=5de816a5 vocab=22854d2b
-/
theorem ker_ratGramFormOnPi (x : V) :
    LinearMap.ker (ratGramFormOnPi G x) = rationalGramKernel G x :=
  ker_toBilin'_eq_ker_mulVecLin (localGramMatrixRat_isSymm G x)

abbrev ratGramSpace (x : V) :=
  (SecondSubconstituent G x → ℚ) ⧸ rationalGramKernel G x

def ratGramForm (x : V) : LinearMap.BilinForm ℚ (ratGramSpace G x) :=
  LinearMap.IsRefl.liftQ₂
    (ratGramFormOnPi G x)
    (rationalGramKernel G x)
    (ratGramFormOnPi_isRefl G x)
    (le_of_eq (ker_ratGramFormOnPi G x).symm)

/--
@isnad1 id=eq.0h5v.s10.fca20f312111 from=translated src=- shape=ca04c9a7 vocab=b7ae60df
-/
@[simp]
theorem ratGramForm_mk (x : V) (v w : SecondSubconstituent G x → ℚ) :
    ratGramForm G x (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) =
      v ⬝ᵥ (localGramMatrixRat G x *ᵥ w) :=
  ratGramFormOnPi_apply G x v w

/--
@isnad1 id=issymm.0h3v.s7.4f797ce5c6ab from=translated src=- shape=3c0fbbd4 vocab=6fcb61d2
-/
theorem ratGramForm_isSymm (x : V) : (ratGramForm G x).IsSymm := by
  constructor
  intro v w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact (ratGramFormOnPi_isSymm G x).eq v w

/--
@isnad1 id=isrefl.0h3v.s7.d1283c09980b from=translated src=- shape=3c0fbbd4 vocab=6d2eaa72
-/
theorem ratGramForm_isRefl (x : V) : (ratGramForm G x).IsRefl :=
  (ratGramForm_isSymm G x).isRefl

/--
@isnad1 id=eq.1h3v.s7.96a595322d89 from=translated src=- shape=7a9b1ea6 vocab=e14b21de
-/
theorem finrank_ratGramSpace (hG : IsHypothetical G) (x : V) :
    Module.finrank ℚ (ratGramSpace G x) = 12 := by
  have h :
      Module.finrank ℚ (ratGramSpace G x) +
          Module.finrank ℚ (rationalGramKernel G x) =
        Module.finrank ℚ (SecondSubconstituent G x → ℚ) :=
    (rationalGramKernel G x).finrank_quotient_add_finrank
  rw [rationalGramKernel_finrank G hG x, Module.finrank_pi ℚ,
    secondSubconstituent_card G hG x] at h
  omega

/--
@isnad1 id=eq.0h4v.s7.5712f03c6967 from=translated src=- shape=b2632063 vocab=22611972
-/
theorem localGramMatrixRat_mulVec_cast (x : V)
    (z : SecondSubconstituent G x → ℤ) :
    localGramMatrixRat G x *ᵥ (fun B => (z B : ℚ)) =
      fun B => ((localGramMatrix G x *ᵥ z) B : ℚ) := by
  funext B
  show (∑ C, ((localGramMatrix G x B C : ℤ) : ℚ) * ((z C : ℤ) : ℚ)) =
    ((∑ C, localGramMatrix G x B C * z C : ℤ) : ℚ)
  push_cast
  rfl

def toRatSpaceOnPi (x : V) :
    (SecondSubconstituent G x → ℤ) →ₗ[ℤ] ratGramSpace G x :=
  ((rationalGramKernel G x).mkQ.restrictScalars ℤ).comp
    (integerToRationalVectors G x)

/--
@isnad1 id=eq.0h4v.s9.5b21126357e9 from=translated src=- shape=c15d608d vocab=9d3a546d
-/
theorem toRatSpaceOnPi_apply (x : V) (z : SecondSubconstituent G x → ℤ) :
    toRatSpaceOnPi G x z = Submodule.Quotient.mk (fun B => (z B : ℚ)) := rfl

/--
@isnad1 id=eq.0h3v.s8.a3058e1db107 from=translated src=- shape=8213d603 vocab=864ec614
-/
theorem ker_toRatSpaceOnPi (x : V) :
    LinearMap.ker (toRatSpaceOnPi G x) = integralGramRelations G x := by
  ext z
  rw [← integralGramKernel_eq_relations]
  simp only [LinearMap.mem_ker, toRatSpaceOnPi_apply, Submodule.Quotient.mk_eq_zero,
    integralGramKernel, Matrix.mulVecLin_apply]
  constructor
  · intro hz
    have hzero : localGramMatrixRat G x *ᵥ (fun B => (z B : ℚ)) = 0 := hz
    rw [localGramMatrixRat_mulVec_cast] at hzero
    funext B
    have hB := congrFun hzero B
    simp only [Pi.zero_apply, Int.cast_eq_zero] at hB
    simpa using hB
  · intro hz
    show localGramMatrixRat G x *ᵥ (fun B => (z B : ℚ)) = 0
    rw [localGramMatrixRat_mulVec_cast]
    funext B
    have hB := congrFun hz B
    simp only [Pi.zero_apply] at hB
    simp [hB]

def toRatSpace (x : V) :
    IntegralGramLattice G x →ₗ[ℤ] ratGramSpace G x :=
  Submodule.liftQ (integralGramRelations G x) (toRatSpaceOnPi G x)
    (le_of_eq (ker_toRatSpaceOnPi G x).symm)

/--
@isnad1 id=eq.0h4v.s9.d99e96b94d43 from=translated src=- shape=43546d3e vocab=8eee46ea
-/
@[simp]
theorem toRatSpace_mk (x : V) (z : SecondSubconstituent G x → ℤ) :
    toRatSpace G x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (fun B => (z B : ℚ)) := rfl

/--
@isnad1 id=injectiv.0h3v.s9.33aa5cf6ffbe from=translated src=- shape=2c87299a vocab=e3d7ffa3
-/
theorem toRatSpace_injective (x : V) : Function.Injective (toRatSpace G x) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq (ker_toRatSpaceOnPi G x))

/--
@isnad1 id=eq.0h5v.s11.1b780d53a4f8 from=translated src=- shape=069c7635 vocab=e4c09334
-/
theorem toRatSpace_pairing (x : V) (a b : IntegralGramLattice G x) :
    ratGramForm G x (toRatSpace G x a) (toRatSpace G x b) =
      (integralGramPairing G x a b : ℚ) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have hint :
      integralGramPairing G x (Submodule.Quotient.mk z) (Submodule.Quotient.mk w) =
        z ⬝ᵥ (localGramMatrix G x *ᵥ w) :=
    Matrix.toBilin'_apply' _ _ _
  rw [toRatSpace_mk, toRatSpace_mk, ratGramForm_mk, localGramMatrixRat_mulVec_cast,
    hint]
  show (∑ C, ((z C : ℤ) : ℚ) * (((localGramMatrix G x *ᵥ w) C : ℤ) : ℚ)) =
    ((∑ C, z C * (localGramMatrix G x *ᵥ w) C : ℤ) : ℚ)
  push_cast
  rfl

/--
@isnad1 id=eq.0h4v.s9.a83a67791dce from=translated src=- shape=9e4f9715 vocab=61ce0285
-/
@[simp]
theorem toRatSpace_generator (x : V) (B : SecondSubconstituent G x) :
    toRatSpace G x (integralGramGenerator G x B) =
      Submodule.Quotient.mk (Pi.single B (1 : ℚ)) := by
  rw [integralGramGenerator, toRatSpace_mk]
  congr 1
  funext C
  by_cases h : C = B <;> simp [h]

def gramLattice (x : V) : Submodule ℤ (ratGramSpace G x) :=
  LinearMap.range (toRatSpace G x)

/--
@isnad1 id=mem.0h4v.s10.bfba8e01f170 from=translated src=- shape=2eb639b3 vocab=3a79c703
-/
theorem toRatSpace_mem_gramLattice (x : V) (a : IntegralGramLattice G x) :
    toRatSpace G x a ∈ gramLattice G x :=
  LinearMap.mem_range_self _ _

/--
@isnad1 id=eq.0h3v.s9.095afb9ebd5d from=translated src=- shape=4703c758 vocab=072c0fc4
-/
theorem gramLattice_span_top (x : V) :
    Submodule.span ℚ ((gramLattice G x : Submodule ℤ (ratGramSpace G x)) :
        Set (ratGramSpace G x)) = ⊤ := by
  classical
  set b := Pi.basisFun ℚ (SecondSubconstituent G x) with hb
  have hrange :
      Set.range ((rationalGramKernel G x).mkQ ∘ b) ⊆
        ((gramLattice G x : Submodule ℤ (ratGramSpace G x)) :
          Set (ratGramSpace G x)) := by
    rintro _ ⟨B, rfl⟩
    refine ⟨integralGramGenerator G x B, ?_⟩
    rw [toRatSpace_generator]
    simp [hb, Pi.basisFun_apply]
  have htop :
      Submodule.span ℚ (Set.range ((rationalGramKernel G x).mkQ ∘ b)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective _
  refine top_unique ?_
  rw [← htop]
  exact Submodule.span_mono hrange

/--
@isnad1 id=fg.0h3v.s7.8d3d58d7d117 from=translated src=- shape=3c0fbbd4 vocab=aecee955
-/
theorem gramLattice_fg (x : V) : (gramLattice G x).FG := by
  have : Module.Finite ℤ (IntegralGramLattice G x) :=
    Module.Finite.of_surjective (integralGramRelations G x).mkQ
      (Submodule.mkQ_surjective _)
  exact Submodule.fg_range (toRatSpace G x)

/--
@isnad1 id=islattic.0h3v.s7.53a788b175db from=translated src=- shape=6e1c534d vocab=5ab68493
-/
theorem gramLattice_isLattice (x : V) :
    Lattice.IsLattice ℚ (gramLattice G x) :=
  ⟨gramLattice_fg G x, gramLattice_span_top G x⟩

end SRG266
