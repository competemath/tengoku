/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Topology.Sheaves.Flasque
import Tengoku.Seed.Topology.Sheaves.LocallySurjective
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.CechInjective
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.Restrict

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Leray's theorem and Cartan's criterion

We compare sheaf cohomology with Čech cohomology by dimension shifting along
`0 → F → I(F) → I(F)/F → 0` (`TopCat.Sheaf.injSES`), using that injective sheaves are Čech acyclic
(`TopCat.Presheaf.isCechAcyclic_of_injective_sheaf`) and restrict to injective sheaves on opens.

## Main results

* `TopCat.Presheaf.exists_lift_of_cech`: for `0 → F → G → Q → 0` exact and a cover `U` of `W`
  with Čech `H¹(U, F) = 0`, a section of `Q` over `W` which lifts to `G` on every `U i` lifts
  over `W`.
* `TopCat.Sheaf.isCechAcyclic_X₃`: Čech acyclicity passes to quotients `G/F` if the sequence is
  surjective on all finite intersections.
* `TopCat.Sheaf.H_eq_zero_of_isCechAcyclic` (**Leray**, vanishing form): if `U` covers `X`,
  `Hⁿ(U_σ, F) = 0` for `n ≥ 1` on all finite intersections `U_σ`, and `Č•(U, F)` is exact in
  positive degrees, then `Hⁿ(X, F) = 0` for `n ≥ 1`.
* `TopCat.Sheaf.cartan` (**Cartan's criterion**): for a family `ℬ` of opens closed under
  intersections and a class of admissible covers which is cofinal among covers of members of `ℬ`,
  Čech acyclicity of `F` on admissible `ℬ`-covers of members of `ℬ` implies `Hⁿ(B, F|_B) = 0`
  for all `B ∈ ℬ` and `n ≥ 1`. `TopCat.Sheaf.cartan_of_isCompact` is the version for a basis of
  compact opens and finite covers.

Along the way: `TopCat.Sheaf.surjective_of_H_one`, `TopCat.Sheaf.H_one_eq_zero_of_surjective`,
`TopCat.Sheaf.H_succ_succ_eq_zero`, `TopCat.Sheaf.H_succ_eq_zero_of_H_succ_succ` and their
`restrictOpen` versions relate sections and cohomology in a short exact sequence whose middle
term is injective.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Presheaf

section Cochains

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

variable {U} in
lemma cechD_cechCochainMap {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ)
    (c : CechCochain U P n) :
    cechD U Q n (cechCochainMap U φ n c) = cechCochainMap U φ (n + 1) (cechD U P n c) := by
  funext τ
  simp only [cechD_apply, cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    map_zsmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.naturality]

lemma cechCochainMap_cechAugment {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    {W : Opens X} (hW : ∀ i, U i ≤ W) (s : P.obj (op W)) :
    cechCochainMap U φ 0 (cechAugment U P hW s) = cechAugment U Q hW (φ.app _ s) := by
  funext σ
  simp only [cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, cechAugment_apply]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.naturality]

end Cochains

section Lift

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

end Lift

end TopCat.Presheaf

namespace TopCat.Sheaf

open TopCat.Presheaf

variable {X : TopCat.{u}}

section DimensionShifting

variable {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
include hS

/-- If `H¹(X, S.X₁) = 0` then `S.X₂(X) → S.X₃(X)` is surjective. -/
lemma surjective_of_H_one (h : ∀ x : H S.X₁ 1, x = 0) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  intro y
  obtain ⟨w, hw⟩ := (H.exact₃ hS 0 1 rfl ((H.equiv₀ _).symm y)).1 (h _)
  refine ⟨H.equiv₀ _ w, ?_⟩
  rw [← H.equiv₀_map, hw, AddEquiv.apply_symm_apply]

/-- If S.X₂ is injective and `S.X₂(X) → S.X₃(X)` is surjective then `H¹(X, S.X₁) = 0`. -/
lemma H_one_eq_zero_of_surjective [Injective S.X₂]
    (hsurj : Function.Surjective (S.g.hom.app (op ⊤))) (x : H S.X₁ 1) : x = 0 := by
  obtain ⟨z, rfl⟩ := (H.exact₁ hS 0 1 rfl x).1 (H.eq_zero_of_injective S.X₂ (n := 0) _)
  obtain ⟨t, ht⟩ := hsurj (H.equiv₀ _ z)
  have : z = H.map S.g 0 ((H.equiv₀ S.X₂).symm t) := by
    rw [H.map_equiv₀_symm, ht, AddEquiv.symm_apply_apply]
  rw [this, H.δ_map_g]

/-- Dimension shifting: if S.X₂ is injective, `Hⁿ⁺¹(S.X₃) = 0` implies `Hⁿ⁺²(S.X₁) = 0`. -/
lemma H_succ_succ_eq_zero [Injective S.X₂] {q : ℕ} (h : ∀ z : H S.X₃ (q + 1), z = 0)
    (x : H S.X₁ (q + 2)) : x = 0 := by
  obtain ⟨z, rfl⟩ := (H.exact₁ hS (q + 1) (q + 2) rfl x).1 (H.eq_zero_of_injective S.X₂ _)
  rw [h z, map_zero]

/-- Dimension shifting: if S.X₂ is injective, `Hⁿ⁺²(S.X₁) = 0` implies `Hⁿ⁺¹(S.X₃) = 0`. -/
lemma H_succ_eq_zero_of_H_succ_succ [Injective S.X₂] {q : ℕ} (h : ∀ x : H S.X₁ (q + 2), x = 0)
    (z : H S.X₃ (q + 1)) : z = 0 := by
  obtain ⟨w, rfl⟩ := (H.exact₃ hS (q + 1) (q + 2) rfl z).1 (h _)
  rw [H.eq_zero_of_injective S.X₂ w, map_zero]

end DimensionShifting

section Open

variable (V : Opens X)

lemma surjective_restrictOpen_map_app_top_iff {F G : AbSheaf X} (φ : F ⟶ G) :
    Function.Surjective (((restrictOpen V).map φ).hom.app (op ⊤)) ↔
      Function.Surjective (φ.hom.app (op V)) := by
  change Function.Surjective (φ.hom.app (op (V.isOpenEmbedding.isOpenMap.functor.obj ⊤))) ↔ _
  rw [functor_obj_top]

variable {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
include hS

lemma shortExact_restrictOpen : (S.map (restrictOpen V)).ShortExact :=
  hS.map_of_exact (restrictOpen V)

/-- If `H¹(V, S.X₁|_V) = 0` then `S.X₂(V) → S.X₃(V)` is surjective. -/
lemma surjective_of_H_one_restrictOpen (h : ∀ x : H ((restrictOpen V).obj S.X₁) 1, x = 0) :
    Function.Surjective (S.g.hom.app (op V)) :=
  (surjective_restrictOpen_map_app_top_iff V S.g).1
    (surjective_of_H_one (shortExact_restrictOpen V hS) h)

/-- If S.X₂ is injective and `S.X₂(V) → S.X₃(V)` is surjective then `H¹(V, S.X₁|_V) = 0`. -/
lemma H_one_restrictOpen_eq_zero_of_surjective [Injective S.X₂]
    (hsurj : Function.Surjective (S.g.hom.app (op V)))
    (x : H ((restrictOpen V).obj S.X₁) 1) : x = 0 :=
  have : Injective (S.map (restrictOpen V)).X₂ := injective_restrictAb _ S.X₂
  H_one_eq_zero_of_surjective (shortExact_restrictOpen V hS)
    ((surjective_restrictOpen_map_app_top_iff V S.g).2 hsurj) x

lemma H_succ_succ_restrictOpen_eq_zero [Injective S.X₂] {q : ℕ}
    (h : ∀ z : H ((restrictOpen V).obj S.X₃) (q + 1), z = 0)
    (x : H ((restrictOpen V).obj S.X₁) (q + 2)) : x = 0 :=
  have : Injective (S.map (restrictOpen V)).X₂ := injective_restrictAb _ S.X₂
  H_succ_succ_eq_zero (shortExact_restrictOpen V hS) h x

lemma H_succ_restrictOpen_eq_zero_of_H_succ_succ [Injective S.X₂] {q : ℕ}
    (h : ∀ x : H ((restrictOpen V).obj S.X₁) (q + 2), x = 0)
    (z : H ((restrictOpen V).obj S.X₃) (q + 1)) : z = 0 :=
  have : Injective (S.map (restrictOpen V)).X₂ := injective_restrictAb _ S.X₂
  H_succ_eq_zero_of_H_succ_succ (shortExact_restrictOpen V hS) h z

end Open

section InjectiveSES

variable (F : AbSheaf X)

/-- The short exact sequence `0 → F → I(F) → I(F)/F → 0` with `I(F)` injective. -/
noncomputable def injSES : ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injSES_shortExact : (injSES F).ShortExact :=
  have : Mono (injSES F).f := inferInstanceAs (Mono (Injective.ι F))
  have : Epi (injSES F).g := inferInstanceAs (Epi (cokernel.π (Injective.ι F)))
  { exact := ShortComplex.exact_cokernel _ }

instance : Injective (injSES F).X₂ := inferInstanceAs (Injective (Injective.under F))

end InjectiveSES

/-- In a short exact sequence of sheaves which is surjective on all finite intersections `U_σ`,
if the first two terms are Čech acyclic then so is the third. -/
lemma isCechAcyclic_X₃ {ι : Type u} {U : ι → Opens X} {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (h₁ : IsCechAcyclic U S.X₁.obj) (h₂ : IsCechAcyclic U S.X₂.obj)
    (hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
      Function.Surjective (S.g.hom.app (op (cechOpen U σ)))) :
    IsCechAcyclic U S.X₃.obj := by
  have hT := cechComplex_shortExact_of_sheaf hS hsurj
  intro n
  have e := hT.homology_exact₃ (n + 1) (n + 2) (by simp)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine e.isZero_X₂ ?_ ?_
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)).eq_of_src _ _
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))).eq_of_tgt _ _

section Leray

variable {ι : Type u} (U : ι → Opens X)

end Leray

section Cartan

lemma iInf_fin_succ {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 2) → α) :
    ⨅ a, f a = f 0 ⊓ ⨅ a : Fin (n + 1), f a.succ :=
  le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a => iInf_le _ a.succ))
    (le_iInf fun a => Fin.cases inf_le_left (fun a => inf_le_right.trans (iInf_le _ a)) a)

/-- A family of opens closed under binary intersections contains all finite intersections
`U_σ` of its members. -/
lemma cechOpen_mem {ℬ : Set (Opens X)} (hℬ : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ⊓ B' ∈ ℬ) {ι : Type u}
    {U : ι → Opens X} (hU : ∀ i, U i ∈ ℬ) {n : ℕ} (σ : Fin (n + 1) → ι) :
    cechOpen U σ ∈ ℬ := by
  induction n with
  | zero =>
    have : cechOpen U σ = U (σ 0) := le_antisymm (iInf_le _ 0)
      (le_iInf fun a => by rw [Subsingleton.elim (α := Fin 1) a 0])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [cechOpen, iInf_fin_succ]
    exact hℬ _ (hU _) _ (ih (σ ∘ Fin.succ))

variable (ℬ : Set (Opens X)) (hℬ : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ⊓ B' ∈ ℬ)
  (Adm : ∀ ι : Type u, (ι → Opens X) → Prop)
  (hcof : ∀ B ∈ ℬ, ∀ 𝒱 : Set (Opens X), (∀ x ∈ B, ∃ V ∈ 𝒱, x ∈ V) →
    ∃ (ι : Type u) (U : ι → Opens X), Adm ι U ∧ (∀ i, U i ∈ ℬ) ∧ (∀ i, ∃ V ∈ 𝒱, U i ≤ V) ∧
      ⨆ i, U i = B)

end Cartan

end TopCat.Sheaf
