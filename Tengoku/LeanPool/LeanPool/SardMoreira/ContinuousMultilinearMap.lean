/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.SardMoreira.ToMathlib.ContinuousLinearMap

/-!
# LeanPool.SardMoreira.ContinuousMultilinearMap
-/

@[expose] public section

open scoped Asymptotics BigOperators

section AddMonoid

namespace ContinuousMultilinearMap

variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Semiring R] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [AddCommMonoid G] [Module R G] [TopologicalSpace G]

/--
@isnad1 id=eq.0h9v.s8.4f0ea3fdcde0 from=translated src=- shape=e7290de5 vocab=e9ae574a
-/
theorem prod_add_prod [ContinuousAdd F] [ContinuousAdd G] (f₁ f₂ : ContinuousMultilinearMap R E F)
    (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ + f₂.prod g₂ = (f₁ + f₂).prod (g₁ + g₂) :=
  rfl

/--
@isnad1 id=eq.0h9v.s8.549d0eab299a from=translated src=- shape=0f5aba03 vocab=47de667f
-/
theorem compContinuousLinearMap_sum_left {E' : ι → Type*} [∀ i, AddCommMonoid (E' i)]
    [∀ i, Module R (E' i)] [∀ i, TopologicalSpace (E' i)] [ContinuousAdd F]
    {ι' : Type*} (s : Finset ι')
    (f : ι' → ContinuousMultilinearMap R E F) (g : ∀ i, E' i →L[R] E i) :
    (∑ i ∈ s, f i).compContinuousLinearMap g = ∑ i ∈ s, (f i).compContinuousLinearMap g := by
  ext; simp

end ContinuousMultilinearMap

end AddMonoid

section AddCommGroup

namespace ContinuousMultilinearMap

variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Ring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommGroup F] [Module R F] [TopologicalSpace F]
    [AddCommGroup G] [Module R G] [TopologicalSpace G]

/--
@isnad1 id=eq.0h9v.s9.cbf06de7bb00 from=translated src=- shape=e7290de5 vocab=4f97d92e
-/
theorem prod_sub_prod [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
     (f₁ f₂ : ContinuousMultilinearMap R E F) (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ - f₂.prod g₂ = (f₁ - f₂).prod (g₁ - g₂) :=
  rfl

/--
@isnad1 id=eq.0h7v.s8.41c5b30b636e from=translated src=- shape=56635ee9 vocab=6474725a
-/
@[simp]
theorem compContinuousLinearMap_neg_left {E' : ι → Type*} [∀ i, AddCommGroup (E' i)]
    [∀ i, Module R (E' i)] [∀ i, TopologicalSpace (E' i)] [IsTopologicalAddGroup F]
    (f : ContinuousMultilinearMap R E F) (g : ∀ i, E' i →L[R] E i) :
    (-f).compContinuousLinearMap g = -f.compContinuousLinearMap g := by
  ext; simp

/--
@isnad1 id=eq.0h8v.s9.e998b90d8170 from=translated src=- shape=35ded6b1 vocab=85e3cdc6
-/
theorem compContinuousLinearMap_sub {E' : ι → Type*} [∀ i, AddCommGroup (E' i)]
    [∀ i, Module R (E' i)] [∀ i, TopologicalSpace (E' i)] [IsTopologicalAddGroup F]
    (f g : ContinuousMultilinearMap R E F) (h : ∀ i, E' i →L[R] E i) :
    (f - g).compContinuousLinearMap h =
      f.compContinuousLinearMap h - g.compContinuousLinearMap h := by
  ext; simp

end ContinuousMultilinearMap

end AddCommGroup

namespace ContinuousMultilinearMap

variable {ι α 𝕜 : Type*} {E F : ι → Type*} {G H : Type*}
  [NontriviallyNormedField 𝕜] [Fintype ι]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H]

omit [Fintype ι] in
/--
@isnad1 id=isbigo.3h11v.s9.4fe2d825a6b8 from=translated src=- shape=2dd32813 vocab=c8fa49d4
-/
theorem const_apply_sub_const_apply_isBigO [Finite ι] (f : ContinuousMultilinearMap 𝕜 E G)
    {g₁ g₂ : α → ∀ i, E i} {B : α → H} {l : Filter α}
    (hg₁ : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₁ · i‖))
    (hg₂ : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₂ · i‖))
    (hsub : ∀ i, (fun a ↦ g₁ a i - g₂ a i) =O[l] B) :
    (fun a ↦ f (g₁ a) - f (g₂ a)) =O[l] B := by
  have := Fintype.ofFinite ι
  refine .trans (.of_norm_le fun _ ↦ norm_image_sub_le _ _ _) ?_
  simp only [← Asymptotics.isBigO_one_iff ℝ, ← Asymptotics.isBigO_pi] at *
  have hsub_pi : (fun a ↦ g₁ a - g₂ a) =O[l] B := by simpa [Pi.sub_apply] using hsub
  simpa using hg₁.prod_left hg₂ |>.norm_left |>.pow (Fintype.card ι - 1)
    |>.const_mul_left (‖f‖ * Fintype.card ι) |>.mul hsub_pi.norm_norm

/--
@isnad1 id=eq.0h6v.s13.8f72033b887b from=translated src=- shape=06e1c493 vocab=8e6ad810
-/
@[simp]
theorem compContinuousLinearMapContinuousMultilinear_apply (f : ∀ i, E i →L[𝕜] F i) :
    compContinuousLinearMapContinuousMultilinear 𝕜 E F G f = compContinuousLinearMapL f :=
  rfl

/--
@isnad1 id=isbigo.5h13v.s11.032a6a79a8c1 from=translated src=- shape=643acbec vocab=874cb59b
-/
theorem compContinuousLinearMap_sub_compContinuousLinearMap_isBigO
    {f₁ f₂ : α → ContinuousMultilinearMap 𝕜 F G} {g₁ g₂ : α → ∀ i, E i →L[𝕜] F i}
    {l : Filter α} {B : α → H}
    (hf₂_bdd : l.IsBoundedUnder (· ≤ ·) (‖f₂ ·‖))
    (hf_sub : (fun a ↦ f₁ a - f₂ a) =O[l] B)
    (hg₁_bdd : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₁ · i‖))
    (hg₂_bdd : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₂ · i‖))
    (hg_sub : ∀ i, (fun a ↦ g₁ a i - g₂ a i) =O[l] B) :
    (fun a ↦ (f₁ a).compContinuousLinearMap (g₁ a) -
      (f₂ a).compContinuousLinearMap (g₂ a)) =O[l] B := by
  simp only [← compContinuousLinearMapL_apply, ← compContinuousLinearMapContinuousMultilinear_apply]
  apply ContinuousLinearMap.apply_sub_apply_isBigO
  · simp only [compContinuousLinearMapContinuousMultilinear_apply]
    refine .mono_le ?_ (.of_forall fun _ ↦ norm_compContinuousLinearMapL_le _ _)
    simp only [← Asymptotics.isBigO_one_iff ℝ] at hg₁_bdd
    simpa using Asymptotics.IsBigO.finsetProd fun i (_ : i ∈ Finset.univ) ↦ (hg₁_bdd i).norm_left
  · apply const_apply_sub_const_apply_isBigO
    · exact hg₁_bdd
    · exact hg₂_bdd
    · exact hg_sub
  · exact hf₂_bdd
  · exact hf_sub

end ContinuousMultilinearMap
