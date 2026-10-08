/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Robin Carlier, Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Nonsingular simplicial sets

In this file, we introduce a typeclass `SSet.Nonsingular` for a
simplicial set `X : SSet`: it says that for any non-degenerate simplex
`x : X _⦋n⦌`, the corresponding morphism `Δ[n] ⟶ X` is a monomorphism.
This notion is useful in the context of the study of the subdivision
functor (TODO @joelriou).

The condition `SSet.Nonsingular` is a weaker condition compared
to the notion of "polyhedral complex" which appears in the article
*Simplicial approximation* by Jardine, and which says that there
exists a monomorphism `X ⟶ nerve T` where `T` is a partially ordered type.

## References
* [Vegard Fjellbo and John Rognes,
  *Exponentials of non-singular simplicial sets*][fjellbo-rognes-2022]
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
/-- A simplicial set `X` is nonsingular if for any
nondegenerate simplex `x` (of dimension `n`), the corresponding
morphism `Δ[n] ⟶ X` is a monomorphism. -/
@[kerodon 02MG]
class Nonsingular where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

attribute [instance] Nonsingular.mono

/--
@isnad1 id=mono.1h3v.s8.3a0c9e996ecd from=seed src=0 shape=b2d1b460 vocab=515aad6d
-/
lemma Nonsingular.mono' [X.Nonsingular]
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Mono (yonedaEquiv.symm x) := mono ⟨x, hx⟩

/--
@isnad1 id=nonsingu.0h3v.s5.a48cee09e928 from=seed src=0 shape=f6911e5d vocab=2121ca80
-/
@[kerodon 02MK]
lemma Nonsingular.of_mono (f : X ⟶ Y) [Mono f] [Y.Nonsingular] :
    X.Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f

/--
@isnad1 id=nonsingu.0h3v.s4.ab0c7c88d395 from=seed src=0 shape=8567d0ba vocab=63dba3b8
-/
lemma Nonsingular.of_iso (e : X ≅ Y) [X.Nonsingular] : Y.Nonsingular :=
  .of_mono e.inv

instance (A : X.Subcomplex) [X.Nonsingular] : (A : SSet).Nonsingular :=
  .of_mono A.ι

@[kerodon 02MT]
instance (T : Type*) [PartialOrder T] : (nerve T).Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective] at hx
    simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hx (Functor.congr_obj hij l)

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Nonsingular :=
  Nonsingular.of_iso (stdSimplex.isoNerve _).symm

instance (n m : SimplexCategory) :
    (stdSimplex.{u}.obj n ⊗ stdSimplex.obj m).Nonsingular :=
  Nonsingular.of_iso (prodStdSimplex.isoNerve _ _).symm

/--
@isnad1 id=mem.1h4v.s8.4957ab8d5781 from=seed src=0 shape=a1b0bf55 vocab=82b1fd89
-/
@[kerodon 02MH]
lemma nonDegenerate_δ [X.Nonsingular]
    {n : ℕ} {x : X _⦋n + 1⦌} (hx : x ∈ X.nonDegenerate _) (i : Fin (n + 2)) :
    X.δ i x ∈ X.nonDegenerate _ := by
  have := Nonsingular.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this, nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply]
  infer_instance

/--
@isnad1 id=eq.2h5v.s9.26fa4570b9eb from=seed src=0 shape=7f4fb113 vocab=82b1fd89
-/
lemma Nonsingular.δ_injective [X.Nonsingular]
    {n : ℕ} (x : X _⦋n + 1⦌) (hx : x ∈ X.nonDegenerate _)
    (i j : Fin (n + 2)) (hij : X.δ i x = X.δ j x) : i = j := by
  apply SimplexCategory.δ_injective
  apply stdSimplex.objEquiv.symm.injective
  have := mono' x hx
  exact injective_of_mono ((yonedaEquiv.symm x).app _) hij

/--
@isnad1 id=eq.2h6v.s8.b1ae02b2d272 from=seed src=0 shape=65bcea05 vocab=86b716eb
-/
lemma Nonsingular.injective_map
    [X.Nonsingular] {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
    {m : SimplexCategory} {f g : m ⟶ ⦋n⦌}
    (h : X.map f.op x = X.map g.op x) :
    f = g := by
  have := Nonsingular.mono' x hx
  apply stdSimplex.{u}.map_injective
  rw [← cancel_mono (yonedaEquiv.symm x)]
  apply yonedaEquiv.injective
  simpa [yonedaEquiv_comp, yonedaEquiv_map]

/--
@isnad1 id=isiso.1h3v.s6.52e63aa5d661 from=seed src=0 shape=1b788ea7 vocab=ada48c49
-/
lemma Nonsingular.isIso_toOfSimplex [X.Nonsingular]
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    IsIso (Subcomplex.toOfSimplex x) := by
  rw [Subcomplex.isIso_toOfSimplex_iff]
  exact Nonsingular.mono' x hx

/-- If `x : X _⦋n⦌` is a nondegenerate simplex of a nonsingular simplicial set,
this is the isomorphism `Δ[n] ≅ Subcomplex.ofSimplex x` induced by `x`. -/
@[expose, simps! hom]
noncomputable def Nonsingular.iso
    [X.Nonsingular] {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Δ[n] ≅ Subcomplex.ofSimplex x :=
  letI := Nonsingular.isIso_toOfSimplex x hx
  asIso (Subcomplex.toOfSimplex x)

namespace N

variable [X.Nonsingular] {x y z : X.N} (h : x ≤ y)

include h in
/--
@isnad1 id=existsun.1h3v.s8.5810f08b6a91 from=seed src=0 shape=0b2f2619 vocab=4b8c3fdf
-/
lemma existsUnique_of_le :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.1.2 = x.1.2 :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h
    exact ⟨f, inferInstance, hf⟩) (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ ↦ by
    exact Nonsingular.injective_map _ y.nonDegenerate (by rw [hf₁, hf₂]))

/-- Given an inequality `x ≤ y` between nondegenerate simplices of a
nonsingular simplicial set `X`, this is the corresponding morphism
`⦋x.dim⦌ ⟶ ⦋y.dim⦌` in the simplex category. -/
noncomputable def monoOfLE : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (existsUnique_of_le h).exists.choose

instance : Mono (monoOfLE h) :=
  (existsUnique_of_le h).exists.choose_spec.1

/--
@isnad1 id=eq.1h3v.s8.a2cba4a4540e from=seed src=0 shape=da45360f vocab=952d5329
-/
@[simp]
lemma map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.simplex :=
  (existsUnique_of_le h).exists.choose_spec.2

/--
@isnad1 id=eq.1h3v.s9.eaf5be6bcacb from=seed src=0 shape=5412a62c vocab=a69d10f1
-/
@[reassoc, simp]
lemma stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex :
    stdSimplex.map (monoOfLE h) ≫ yonedaEquiv.symm y.simplex =
      yonedaEquiv.symm x.simplex := by
  rw [yonedaEquiv_symm_naturality_left, map_monoOfLE]

/--
@isnad1 id=iff.1h4v.s8.60f5ee59f753 from=seed src=0 shape=54a7dab0 vocab=f2d4eab3
-/
lemma monoOfLE_eq_iff (h : x ≤ y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g] :
    monoOfLE h = g ↔ X.map g.op y.simplex = x.simplex :=
  ⟨by rintro rfl; simp,
    fun h' ↦ (existsUnique_of_le h).unique ⟨inferInstance, by simp⟩ ⟨inferInstance, h'⟩⟩

variable (x) in
/--
@isnad1 id=eq.0h2v.s5.32f72dc9ff3d from=seed src=0 shape=b732feaf vocab=2297acea
-/
@[simp]
lemma monoOfLE_refl : monoOfLE (le_refl x) = 𝟙 _ := by
  simp [monoOfLE_eq_iff]

/--
@isnad1 id=eq.2h4v.s6.3c2d099f062f from=seed src=0 shape=94562e52 vocab=49fd9e21
-/
@[reassoc (attr := simp)]
lemma monoOfLE_comp (h' : y ≤ z) :
    monoOfLE h ≫ monoOfLE h' = monoOfLE (h.trans h') := by
  symm
  simp [monoOfLE_eq_iff]

end N

end SSet
