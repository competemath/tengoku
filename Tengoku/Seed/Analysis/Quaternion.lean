/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Quaternion
public import Tengoku.Seed.Analysis.InnerProductSpace.Continuous
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
public import Tengoku.Seed.Topology.Algebra.Algebra

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the Euclidean norm of its components.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/

@[expose] public noncomputable section


@[inherit_doc] scoped[Quaternion] notation "ℍ" => Quaternion ℝ

open scoped RealInnerProductSpace

namespace Quaternion

instance : Inner ℝ ℍ :=
  ⟨fun a b => (a * star b).re⟩

/--
@isnad1 id=eq.0h1v.s8.5ed31a63a2f4 from=seed src=0 shape=4fba51f9 vocab=7606bc40
-/
theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.cf64ca57b646 from=seed src=0 shape=048572f9 vocab=ee24e766
-/
theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * star b).re :=
  rfl

instance : NormedAddCommGroup ℍ :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ ℍ _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun _ => normSq_nonneg
      definite := fun _ => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_def, add_mul, re_add]
      smul_left := fun x y r => by simp [inner_def] }

instance : InnerProductSpace ℝ ℍ :=
  InnerProductSpace.ofCore _

/--
@isnad1 id=eq.0h1v.s8.73b5a87f14f2 from=seed src=0 shape=0298b890 vocab=88410813
-/
theorem normSq_eq_norm_mul_self (a : ℍ) : normSq a = ‖a‖ * ‖a‖ := by
  rw [← inner_self, real_inner_self_eq_norm_mul_norm]

instance : NormOneClass ℍ :=
  ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

/--
@isnad1 id=eq.0h1v.s6.3a32f5ed48af from=seed src=0 shape=32bc8227 vocab=c4cec114
-/
@[simp, norm_cast]
theorem norm_coe (a : ℝ) : ‖(a : ℍ)‖ = ‖a‖ := by
  rw [norm_eq_sqrt_real_inner, inner_self, normSq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

/--
@isnad1 id=eq.0h1v.s7.2004096e5e8d from=seed src=0 shape=f4fa557c vocab=c85c1dd8
-/
@[simp, norm_cast]
theorem nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_coe a

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
/--
@isnad1 id=eq.0h1v.s5.f64a9069f7f3 from=seed src=0 shape=ec0a1a4f vocab=f4d5f10c
-/
theorem norm_star (a : ℍ) : ‖star a‖ = ‖a‖ := by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
/--
@isnad1 id=eq.0h1v.s6.f77762721532 from=seed src=0 shape=8cf62763 vocab=c2c60f8e
-/
theorem nnnorm_star (a : ℍ) : ‖star a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_star a

instance : NormedDivisionRing ℍ where
  dist_eq _ _ := rfl
  norm_mul _ _ := by simp_rw [norm_eq_sqrt_real_inner, inner_self]; simp

instance : NormedAlgebra ℝ ℍ where
  norm_smul_le := norm_smul_le
  toAlgebra := Quaternion.algebra

instance : CStarRing ℍ where
  norm_mul_self_le x :=
    le_of_eq <| Eq.symm <| (norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_star x)

/-- Coercion from `ℂ` to `ℍ`. -/
@[coe] def coeComplex (z : ℂ) : ℍ := ⟨z.re, z.im, 0, 0⟩

instance : Coe ℂ ℍ := ⟨coeComplex⟩

/--
@isnad1 id=eq.0h1v.s5.fc72b3e4bf5f from=seed src=0 shape=629ce682 vocab=62a2dd77
-/
@[simp, norm_cast]
theorem re_coeComplex (z : ℂ) : (z : ℍ).re = z.re :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.d8f7d6f5b4d2 from=seed src=0 shape=629ce682 vocab=0c71e779
-/
@[simp, norm_cast]
theorem imI_coeComplex (z : ℂ) : (z : ℍ).imI = z.im :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.6db847ff25b7 from=seed src=0 shape=f7033f44 vocab=80bfedc3
-/
@[simp, norm_cast]
theorem imJ_coeComplex (z : ℂ) : (z : ℍ).imJ = 0 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.7b61cb0aec22 from=seed src=0 shape=f7033f44 vocab=0f373ddc
-/
@[simp, norm_cast]
theorem imK_coeComplex (z : ℂ) : (z : ℍ).imK = 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.dd49547f0685 from=seed src=0 shape=82c640f9 vocab=95240252
-/
@[simp, norm_cast]
theorem coeComplex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by ext <;> simp

/--
@isnad1 id=eq.0h2v.s6.02bf6bb74300 from=seed src=0 shape=82c640f9 vocab=49b39b16
-/
@[simp, norm_cast]
theorem coeComplex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by ext <;> simp

/--
@isnad1 id=eq.0h0v.s5.f6e5f0a80a7d from=seed src=0 shape=249d2cad vocab=84913cd3
-/
@[simp, norm_cast]
theorem coeComplex_zero : ((0 : ℂ) : ℍ) = 0 :=
  rfl

/--
@isnad1 id=eq.0h0v.s5.d564a7b0ac00 from=seed src=0 shape=249d2cad vocab=84913cd3
-/
@[simp, norm_cast]
theorem coeComplex_one : ((1 : ℂ) : ℍ) = 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.046b50c75efe from=seed src=0 shape=8d954e0b vocab=031c1863
-/
@[simp, norm_cast]
theorem coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z := by ext <;> simp

/--
@isnad1 id=eq.0h1v.s3.1a575048b482 from=seed src=0 shape=edb93955 vocab=1e9e274d
-/
@[simp, norm_cast]
theorem coeComplex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r :=
  rfl

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def ofComplex : ℂ →ₐ[ℝ] ℍ where
  toFun := (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl

/--
@isnad1 id=eq.0h0v.s6.f6c3be7f9df0 from=seed src=0 shape=dcf1375f vocab=f7e65e36
-/
@[simp]
theorem coe_ofComplex : ⇑ofComplex = coeComplex := rfl

/-- The norm of the components as a Euclidean vector equals the norm of the quaternion.
@isnad1 id=eq.0h1v.s7.bf52342c0b04 from=seed src=0 shape=ce38bfdc vocab=742d8873
-/
lemma norm_toLp_equivTuple (x : ℍ) : ‖WithLp.toLp 2 (equivTuple ℝ x)‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_self, normSq_def', PiLp.inner_apply,
    Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl

/-- `QuaternionAlgebra.linearEquivTuple` as a `LinearIsometryEquiv`. -/
@[simps apply symm_apply]
def linearIsometryEquivTuple : ℍ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) (0 : ℝ) (-1 : ℝ)).trans
      (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm with
    toFun := fun a => !₂[a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_toLp_equivTuple }

/--
@isnad1 id=continuo.0h0v.s7.d90ca0934e70 from=seed src=0 shape=4b718b57 vocab=98d3cc3a
-/
@[continuity]
theorem continuous_coe : Continuous (coe : ℝ → ℍ) :=
  continuous_algebraMap ℝ ℍ

/--
@isnad1 id=continuo.0h0v.s9.a9e4bec3005b from=seed src=0 shape=ac045197 vocab=759b30da
-/
@[continuity]
theorem continuous_normSq : Continuous (normSq : ℍ → ℝ) := by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.fun_mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)

/--
@isnad1 id=continuo.0h0v.s6.e2463d696a90 from=seed src=0 shape=8104195c vocab=2789c39e
-/
@[continuity]
theorem continuous_re : Continuous fun q : ℍ => q.re :=
  (PiLp.continuous_apply 2 _ 0).comp linearIsometryEquivTuple.continuous

/--
@isnad1 id=continuo.0h0v.s6.1277bcfc749f from=seed src=0 shape=8104195c vocab=540496b0
-/
@[continuity]
theorem continuous_imI : Continuous fun q : ℍ => q.imI :=
  (PiLp.continuous_apply 2 _ 1).comp linearIsometryEquivTuple.continuous

/--
@isnad1 id=continuo.0h0v.s6.0485c51d93c5 from=seed src=0 shape=8104195c vocab=fdfdc227
-/
@[continuity]
theorem continuous_imJ : Continuous fun q : ℍ => q.imJ :=
  (PiLp.continuous_apply 2 _ 2).comp linearIsometryEquivTuple.continuous

/--
@isnad1 id=continuo.0h0v.s6.54602945fc59 from=seed src=0 shape=8104195c vocab=e1c4c2a4
-/
@[continuity]
theorem continuous_imK : Continuous fun q : ℍ => q.imK :=
  (PiLp.continuous_apply 2 _ 3).comp linearIsometryEquivTuple.continuous

/--
@isnad1 id=continuo.0h0v.s8.cff7ebfe2047 from=seed src=0 shape=8d3d3d6d vocab=5276e075
-/
@[continuity]
theorem continuous_im : Continuous fun q : ℍ => q.im := by
  simpa only [← sub_re_self] using! continuous_id.sub (continuous_coe.comp continuous_re)

instance : CompleteSpace ℍ :=
  haveI : IsUniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding
  (completeSpace_congr this).1 inferInstance

section infinite_sum

variable {α : Type*} {L : SummationFilter α}

/--
@isnad1 id=iff.0h4v.s8.26b255c4e939 from=seed src=0 shape=87b5b8e2 vocab=a159b3cb
-/
@[simp, norm_cast]
theorem hasSum_coe {f : α → ℝ} {r : ℝ} : HasSum (fun a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L :=
  ⟨fun h => by
    simpa only using!
    h.map (show ℍ →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _ _) continuous_re,
    fun h => by simpa only using! h.map (algebraMap ℝ ℍ) (continuous_algebraMap _ _)⟩

/--
@isnad1 id=iff.0h3v.s8.5a1a66257cde from=seed src=0 shape=4cbd3722 vocab=880767b9
-/
@[simp, norm_cast]
theorem summable_coe {f : α → ℝ} : (Summable (fun a => (f a : ℍ)) L) ↔ Summable f L := by
  simpa only using!
    Summable.map_iff_of_leftInverse (algebraMap ℝ ℍ) (show ℍ →ₗ[ℝ] ℝ from
      QuaternionAlgebra.reₗ _ _ _)
      (continuous_algebraMap _ _) continuous_re re_coe

/--
@isnad1 id=eq.0h3v.s8.0d855ee1772f from=seed src=0 shape=5bd7ed9a vocab=e8a1b673
-/
@[norm_cast]
theorem tsum_coe (f : α → ℝ) : (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a) :=
  (Function.LeftInverse.map_tsum f (continuous_algebraMap _ _) continuous_re re_coe).symm

end infinite_sum

end Quaternion
