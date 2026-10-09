/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Group.Hom
public import Tengoku.Seed.Topology.Algebra.SeparationQuotient.Hom

/-!
# Lifts of maps to separation quotients of seminormed groups

For any `SeminormedAddCommGroup M`, a `NormedAddCommGroup` instance has been defined in
`Mathlib/Analysis/Normed/Group/Uniform.lean`.

## Main definitions

We use `M` and `N` to denote seminormed groups.
All the following definitions are in the `SeparationQuotient` namespace. Hence we can access
`SeparationQuotient.normedMk` as `normedMk`.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

* `liftNormedAddGroupHom` : any bounded group hom `f : M → N` such that `∀ x, ‖x‖ = 0 → f x = 0`
  descends to a bounded group hom `SeparationQuotient M → N`.
  Here, `(f : NormedAddGroupHom M N)`, `(hf : ∀ x : M, ‖x‖ = 0 → f x = 0)`
  and `liftNormedAddGroupHom f hf : NormedAddGroupHom (SeparationQuotient M) N` such that
  `liftNormedAddGroupHom f hf (mk x) = f x`.

## Main results

* `norm_normedMk_eq_one` : the operator norm of the projection is `1` if the subspace is not `⊤`.

* `norm_liftNormedAddGroupHom_le` : `‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖`.
-/

@[expose] public section

section

open SeparationQuotient NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotient

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the inseparable setoid. -/
@[simps]
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) where
  __ := mkAddMonoidHom
  bound' := ⟨1, by simp⟩

/-- The operator norm of the projection is at most `1`.
@isnad1 id=le.0h1v.s6.8a00064c5dd7 from=seed src=0 shape=b97c1108 vocab=8813c2d4
-/
theorem norm_normedMk_le : ‖normedMk (M := M)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp

/--
@isnad1 id=eq.2h6v.s7.ba7b80751e26 from=seed src=0 shape=faef9992 vocab=d461d0ab
-/
lemma apply_eq_apply_of_inseparable {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) : ∀ x y, Inseparable x y → f x = f y :=
  fun x y h ↦ eq_of_sub_eq_zero <| by
    rw [← map_sub]
    rw [Metric.inseparable_iff, dist_eq_norm] at h
    exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
@[simps]
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) : NormedAddGroupHom (SeparationQuotient M) N where
  toFun := SeparationQuotient.liftContinuousAddMonoidHom f <| apply_eq_apply_of_inseparable f hf
  map_add' v₁ v₂ := map_add ..
  bound' := by
    refine ⟨‖f‖, fun v ↦ ?_⟩
    obtain ⟨v, rfl⟩ := surjective_mk v
    exact le_opNorm f v

/--
@isnad1 id=le.1h4v.s7.5d58341f3177 from=seed src=0 shape=0a507410 vocab=16a96394
-/
theorem norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) (x : SeparationQuotient M) :
    ‖liftNormedAddGroupHom f hf x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨x, rfl⟩ := surjective_mk x
  exact le_opNorm f x

/-- The equivalence between `NormedAddGroupHom M N` vanishing on the inseparable setoid and
`NormedAddGroupHom (SeparationQuotient M) N`. -/
@[simps]
noncomputable def liftNormedAddGroupHomEquiv {N : Type*} [SeminormedAddCommGroup N] :
    {f : NormedAddGroupHom M N // ∀ x, ‖x‖ = 0 → f x = 0} ≃
    NormedAddGroupHom (SeparationQuotient M) N where
  toFun f := liftNormedAddGroupHom f f.prop
  invFun g := ⟨g.comp normedMk, by
    intro x hx
    rw [← norm_mk, norm_eq_zero] at hx
    simp [hx]⟩
  right_inv _ := by
    ext x
    obtain ⟨x, rfl⟩ := surjective_mk x
    rfl

/-- For a norm-continuous group homomorphism `f`, its lift to the separation quotient
is bounded by the norm of `f`.
@isnad1 id=le.1h3v.s7.2eed6393f455 from=seed src=0 shape=484cf6af vocab=fb174dca
-/
theorem norm_liftNormedAddGroupHom_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) :
    ‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)

/--
@isnad1 id=le.2h4v.s7.ba96ff1b19a6 from=seed src=0 shape=16aa8b36 vocab=d40400f8
-/
theorem liftNormedAddGroupHom_norm_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖liftNormedAddGroupHom f hf‖ ≤ c :=
  (norm_liftNormedAddGroupHom_le f hf).trans fb

/--
@isnad1 id=normnoni.2h3v.s6.ad6e449f8d87 from=seed src=0 shape=1f076326 vocab=7f885762
-/
theorem liftNormedAddGroupHom_normNoninc {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) (fb : f.NormNoninc) :
    (liftNormedAddGroupHom f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ 1 := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  exact le_trans (norm_liftNormedAddGroupHom_apply_le f hf x)
    (mul_le_of_le_one_left (norm_nonneg x) fb')

/-- The operator norm of the projection is `1` if there is an element whose norm is different from
`0`.
@isnad1 id=eq.0h1v.s6.96f7e2d508ba from=seed src=0 shape=f525c568 vocab=a72d55a6
-/
theorem norm_normedMk_eq_one [NontrivialTopology M] :
    ‖normedMk (M := M)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simpa only [normedMk_apply, one_mul] using! fun _ ↦ le_rfl
  · intro N _ hle
    obtain ⟨x, _⟩ := exists_norm_ne_zero M
    exact one_le_of_le_mul_right₀ (by positivity) (hle x)

/-- The projection is `0` if and only if all the elements have norm `0`.
@isnad1 id=iff.0h1v.s7.35538d4e50f8 from=seed src=0 shape=757fb022 vocab=900ba2d6
-/
theorem normedMk_eq_zero_iff : normedMk (M := M) = 0 ↔ ∀ (x : M), ‖x‖ = 0 := by
  constructor
  · intro h x
    rw [SeparationQuotient.mk_eq_zero_iff.mp]
    have : normedMk x = 0 := by
      rw [h]
      simp only [NormedAddGroupHom.zero_apply]
    rw [← this]
    simp
  · intro h
    ext x
    simpa [← norm_eq_zero] using h x

end SeparationQuotient

end
