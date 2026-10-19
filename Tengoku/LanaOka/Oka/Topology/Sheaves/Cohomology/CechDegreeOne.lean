/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.Leray
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.PullbackZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Čech cohomology in degree one

Let `U : ι → Opens X` be an open cover of `X` and `F` an abelian sheaf. We construct the
comparison map `H¹(U, F) → H¹(X, F)` from Čech to sheaf cohomology and show that it is
always injective, and bijective as soon as `H¹(U i, F|_{U i}) = 0` for all `i` (no condition on
the intersections).

The map is the classical one. Embed `F` into an injective sheaf, `0 → F → I → Q → 0`
(`TopCat.Sheaf.injSES`). A Čech `1`-cocycle `z` of `F` is a coboundary `d t` in `Č•(U, I)` (the
injective sheaf `I` is Čech acyclic), the image of `t` in `Č⁰(U, Q)` is a `0`-cocycle, hence a
global section `s` of `Q`, and `z ↦ δ s`. The value does not depend on the choices, nor on the
short exact sequence: for *every* short exact sequence `0 → F → G → Q → 0` and every such pair
`(t, s)` (`TopCat.Sheaf.IsCechLift`) the image of `z` is `δ s` (`TopCat.Sheaf.cechToH_eq`). This
characterisation gives additivity, naturality in `F`, and compatibility with refinement.

## Main definitions and results

* `TopCat.Presheaf.cechRefine`, `TopCat.Presheaf.cechRefineHom`: the refinement map
  `Č•(U, P) → Č•(V, P)` for a family `V` with `V k ≤ U (τ k)`.
* `TopCat.Sheaf.cechToH hU F z hz : H F 1`: the class of a Čech `1`-cocycle, characterised by
  `TopCat.Sheaf.cechToH_eq`; it vanishes exactly on coboundaries
  (`TopCat.Sheaf.cechToH_eq_zero_iff`), is natural (`TopCat.Sheaf.cechToH_map`), compatible with
  refinement (`TopCat.Sheaf.cechToH_cechRefine`) and surjective if `H¹(U i, F) = 0` for all `i`
  (`TopCat.Sheaf.cechToH_surjective`).
* `TopCat.Sheaf.cechHomologyToH hU F : (cechComplex U F.obj).homology 1 →+ H F 1`, injective
  (`TopCat.Sheaf.cechHomologyToH_injective`), natural in `F`
  (`TopCat.Sheaf.cechHomologyToH_naturality`) and compatible with refinement
  (`TopCat.Sheaf.cechHomologyToH_refine`).
* `TopCat.Sheaf.cechH1Equiv hU hH : (cechComplex U F.obj).homology 1 ≃+ H F 1` if
  `H¹(U i, F|_{U i}) = 0` for all `i`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

lemma cechCochainMap_comp {P Q R : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (ψ : Q ⟶ R)
    (n : ℕ) (c : CechCochain U P n) :
    cechCochainMap U (φ ≫ ψ) n c = cechCochainMap U ψ n (cechCochainMap U φ n c) := rfl

lemma cechCochainMap_id (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (c : CechCochain U P n) :
    cechCochainMap U (𝟙 P) n c = c := rfl

section Refinement

variable {κ : Type u} {V : κ → Opens X} {τ : κ → ι} (hτ : ∀ k, V k ≤ U (τ k))

include hτ in
lemma cechOpen_le_cechOpen_comp {n : ℕ} (σ : Fin (n + 1) → κ) :
    cechOpen V σ ≤ cechOpen U (τ ∘ σ) :=
  le_iInf fun a => (iInf_le _ a).trans (hτ _)

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The refinement map `Čⁿ(U, P) → Čⁿ(V, P)`, `c ↦ (σ ↦ c(τ ∘ σ)|_{V_σ})`, for a family `V` with
`V k ≤ U (τ k)`. -/
def cechRefine (n : ℕ) : CechCochain U P n →+ CechCochain V P n where
  toFun c σ := P.map (homOfLE (cechOpen_le_cechOpen_comp U hτ σ)).op (c (τ ∘ σ))
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp

lemma cechRefine_apply {n : ℕ} (c : CechCochain U P n) (σ : Fin (n + 1) → κ) :
    cechRefine U hτ P n c σ = P.map (homOfLE (cechOpen_le_cechOpen_comp U hτ σ)).op (c (τ ∘ σ)) :=
  rfl

/-- Refinement commutes with the augmentation. -/
lemma cechRefine_cechAugment {W : Opens X} (hW : ∀ i, U i ≤ W) (hV : ∀ k, V k ≤ W)
    (s : P.obj (op W)) : cechRefine U hτ P 0 (cechAugment U P hW s) = cechAugment V P hV s := by
  funext σ
  simp only [cechRefine_apply, cechAugment_apply, map_homOfLE_map_homOfLE]

/-- Refinement is natural in the presheaf. -/
lemma cechRefine_cechCochainMap {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ)
    (c : CechCochain U P n) :
    cechRefine U hτ Q n (cechCochainMap U φ n c) =
      cechCochainMap V φ n (cechRefine U hτ P n c) := by
  funext σ
  simp only [cechRefine_apply, cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.naturality]

end Refinement

end TopCat.Presheaf

namespace TopCat.Sheaf

open TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

section Sections

variable {S S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (hS' : S'.ShortExact)

/-- The connecting homomorphism `S.X₃(X) = H⁰(X, S.X₃) → H¹(X, S.X₁)` on global sections. -/
noncomputable def H.δSections : S.X₃.obj.obj (op ⊤) →+ H S.X₁ 1 :=
  (H.δ hS 0 1 rfl).comp (H.equiv₀ S.X₃).symm.toAddMonoidHom

lemma H.δSections_apply (s : S.X₃.obj.obj (op ⊤)) :
    H.δSections hS s = H.δ hS 0 1 rfl ((H.equiv₀ S.X₃).symm s) := rfl

/-- Global sections of `S.X₃` coming from `S.X₂` have zero connecting image. -/
lemma H.δSections_g (a : S.X₂.obj.obj (op ⊤)) : H.δSections hS (S.g.hom.app _ a) = 0 := by
  rw [H.δSections_apply, ← H.map_equiv₀_symm, H.δ_map_g]

/-- The connecting image of a global section of `S.X₃` vanishes iff it lifts to `S.X₂`. -/
lemma H.δSections_eq_zero_iff (s : S.X₃.obj.obj (op ⊤)) :
    H.δSections hS s = 0 ↔ ∃ a, S.g.hom.app _ a = s := by
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ha ▸ H.δSections_g hS a⟩
  obtain ⟨w, hw⟩ := (H.exact₃ hS 0 1 rfl ((H.equiv₀ _).symm s)).1 h
  refine ⟨H.equiv₀ _ w, ?_⟩
  rw [← H.equiv₀_map, hw, AddEquiv.apply_symm_apply]

/-- The connecting map on global sections is natural in the short exact sequence. -/
lemma H.δSections_naturality (Φ : S ⟶ S') (s : S.X₃.obj.obj (op ⊤)) :
    H.δSections hS' (Φ.τ₃.hom.app _ s) = H.map Φ.τ₁ 1 (H.δSections hS s) := by
  rw [H.δSections_apply, H.δSections_apply, ← H.map_equiv₀_symm, H.δ_naturality hS hS' Φ]

end Sections

section Lift

variable (S : ShortComplex (AbSheaf X))

/-- `(t, s)` lifts the Čech `1`-cochain `z` of `S.X₁` along `0 → S.X₁ → S.X₂ → S.X₃ → 0`:
`d t = f z` in `Č¹(U, S.X₂)` and the image of `t` in `Č⁰(U, S.X₃)` is the restriction of the
global section `s`. -/
def IsCechLift (z : CechCochain U S.X₁.obj 1) (t : CechCochain U S.X₂.obj 0)
    (s : S.X₃.obj.obj (op ⊤)) : Prop :=
  cechD U S.X₂.obj 0 t = cechCochainMap U S.f.hom 1 z ∧
    cechCochainMap U S.g.hom 0 t = cechAugment U S.X₃.obj (fun _ => le_top) s

variable {U S}

lemma cechCochainMap_g_f {n : ℕ} (x : CechCochain U S.X₁.obj n) :
    cechCochainMap U S.g.hom n (cechCochainMap U S.f.hom n x) = 0 := by
  rw [← cechCochainMap_comp]
  have : S.f.hom ≫ S.g.hom = 0 := congrArg (fun φ => φ.hom) S.zero
  rw [this]
  rfl

/-- Morphisms of short complexes transport lifts. -/
lemma IsCechLift.map {S' : ShortComplex (AbSheaf X)} (Φ : S ⟶ S')
    {z : CechCochain U S.X₁.obj 1} {t : CechCochain U S.X₂.obj 0} {s : S.X₃.obj.obj (op ⊤)}
    (h : IsCechLift U S z t s) :
    IsCechLift U S' (cechCochainMap U Φ.τ₁.hom 1 z) (cechCochainMap U Φ.τ₂.hom 0 t)
      (Φ.τ₃.hom.app _ s) := by
  refine ⟨?_, ?_⟩
  · rw [cechD_cechCochainMap, h.1, ← cechCochainMap_comp, ← cechCochainMap_comp]
    exact congrArg (fun φ : S.X₁ ⟶ S'.X₂ => cechCochainMap U φ.hom 1 z) Φ.comm₁₂.symm
  · rw [← cechCochainMap_cechAugment, ← h.2, ← cechCochainMap_comp, ← cechCochainMap_comp]
    exact congrArg (fun φ : S.X₂ ⟶ S'.X₃ => cechCochainMap U φ.hom 0 t) Φ.comm₂₃

/-- Two lifts of the same cochain have the same connecting image. -/
lemma IsCechLift.δSections_eq (hS : S.ShortExact) {z : CechCochain U S.X₁.obj 1}
    {t t' : CechCochain U S.X₂.obj 0}
    {s s' : S.X₃.obj.obj (op ⊤)} (h : IsCechLift U S z t s) (h' : IsCechLift U S z t' s')
    (hU : ⨆ i, U i = ⊤) : H.δSections hS s = H.δSections hS s' := by
  have hd : cechD U S.X₂.obj 0 (t - t') = 0 := by rw [map_sub, h.1, h'.1, sub_self]
  obtain ⟨a, ha⟩ := exists_cechAugment_eq U (fun _ => le_top) S.X₂ hU.ge _ hd
  have hs : S.g.hom.app _ a = s - s' := by
    apply cechAugment_injective U (fun _ => le_top) S.X₃ hU.ge
    rw [← cechCochainMap_cechAugment, ha, map_sub, map_sub, h.2, h'.2]
  rw [← sub_eq_zero, ← map_sub, ← hs, H.δSections_g]

end Lift

section Comparison

variable {U} (hU : ⨆ i, U i = ⊤)
include hU

end Comparison

section Homology

variable {U} (hU : ⨆ i, U i = ⊤)
include hU

omit hU in
lemma exists_homologyπ_eq {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (x : (cechComplex U P).homology 1) : ∃ c, (cechComplex U P).homologyπ 1 c = x :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance x

end Homology

end TopCat.Sheaf
