/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Tengoku.Seed.CategoryTheory.Sites.SheafCohomology.Basic
import Tengoku.Seed.Topology.Sheaves.Abelian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohomology of abelian sheaves on a topological space

For `X : TopCat.{u}` and `F : X.AbSheaf` (definitionally `X.Sheaf AddCommGrpCat.{u}`) we write
`TopCat.Sheaf.H F n` for the sheaf cohomology `Hⁿ(X, F)`, i.e. Mathlib's
`CategoryTheory.Sheaf.H F n`, the `Ext`-group `Extⁿ(ℤ_X, F)` in the Grothendieck abelian category
of abelian sheaves on `X`.

All statements are phrased in `X.AbSheaf = Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`
(an `abbrev`), so that instance search finds Mathlib's instances for sheaves on a site; objects
and morphisms of `X.Sheaf AddCommGrpCat` can be used directly.

## Main definitions and results

* `TopCat.Sheaf.H F n`: the cohomology group `Hⁿ(X, F) : Type u`.
* `TopCat.Sheaf.H.equiv₀ F : H F 0 ≃+ F.obj.obj (op ⊤)`: degree zero is global sections.
* `TopCat.Sheaf.H.map φ n : H F n →+ H G n`: functoriality.
* `TopCat.Sheaf.H.δ hS n₀ n₁ h : H S.X₃ n₀ →+ H S.X₁ n₁`: the connecting homomorphism of a short
  exact sequence `S` of sheaves, with exactness `TopCat.Sheaf.H.exact₁`, `TopCat.Sheaf.H.exact₂`,
  `TopCat.Sheaf.H.exact₃` and the long exact sequence `TopCat.Sheaf.H.sequence`,
  `TopCat.Sheaf.H.sequence_exact`.
* `TopCat.Sheaf.H.eq_zero_of_injective`: `Hⁿ⁺¹(X, I) = 0` for an injective sheaf `I`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat

variable {X : TopCat.{u}}

variable (X) in
/-- The category of abelian sheaves on `X`, written as sheaves on the site of opens. It is
definitionally `X.Sheaf AddCommGrpCat.{u}`; functors between such categories are best typed with
`AbSheaf`, so that instance search sees Mathlib's instances for sheaves on a site. -/
abbrev AbSheaf : Type (u + 1) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

namespace Sheaf

variable (X) in
/-- The constant sheaf `ℤ_X` (with values `ULift ℤ`), the source of the `Ext`-groups defining
sheaf cohomology. -/
noncomputable abbrev constZ : AbSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- The sheaf cohomology `Hⁿ(X, F)` of an abelian sheaf `F` on a topological space `X`. -/
abbrev H (F : AbSheaf X) (n : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u} (J := Opens.grothendieckTopology X) F n

namespace H

variable (F : AbSheaf X)

/-- Degree zero cohomology is the group of global sections. -/
noncomputable def equiv₀ : H F 0 ≃+ F.obj.obj (op ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop

variable {F} {G K : AbSheaf X} (φ : F ⟶ G)

/-- The map `Hⁿ(X, F) → Hⁿ(X, G)` induced by a morphism of sheaves. -/
noncomputable def map (n : ℕ) : H F n →+ H G n :=
  CategoryTheory.Sheaf.H.map φ n

/--
@isnad1 id=eq.0h6v.s11.69cf1561eb6d from=translated src=- shape=782dd5dc vocab=5149032c
-/
lemma map_apply {n : ℕ} (x : H F n) : map φ n x = x.comp (Ext.mk₀ φ) (add_zero n) := rfl

/--
@isnad1 id=eq.0h4v.s10.3b2dd610c632 from=translated src=- shape=ee52c632 vocab=e5628ce5
-/
@[simp]
lemma map_id_apply {n : ℕ} (x : H F n) : map (𝟙 F) n x = x :=
  CategoryTheory.Sheaf.H.map_id_apply x

/--
@isnad1 id=eq.0h8v.s12.5cec486ab1a4 from=translated src=- shape=e4dae70c vocab=8594d062
-/
lemma map_comp_apply {n : ℕ} (ψ : G ⟶ K) (x : H F n) :
    map (φ ≫ ψ) n x = map ψ n (map φ n x) :=
  CategoryTheory.Sheaf.H.map_comp_apply φ ψ x

/--
@isnad1 id=eq.0h7v.s12.67342e70163d from=translated src=- shape=920bc4ca vocab=3de15714
-/
@[simp]
lemma map_add_apply {n : ℕ} (φ φ' : F ⟶ G) (x : H F n) :
    map (φ + φ') n x = map φ n x + map φ' n x :=
  CategoryTheory.Sheaf.H.map_add_apply φ φ' x

/--
@isnad1 id=eq.0h5v.s11.37efeb218b2a from=translated src=- shape=159344f7 vocab=c8e91c5f
-/
@[simp]
lemma map_zero_apply {n : ℕ} (x : H F n) : map (0 : F ⟶ G) n x = 0 := by
  have h := map_add_apply (0 : F ⟶ G) 0 x
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- The identification of `H⁰` with global sections is natural.
@isnad1 id=eq.0h5v.s14.4448dfab866b from=translated src=- shape=be08c6e9 vocab=c7d5301e
-/
lemma equiv₀_map (x : H F 0) :
    equiv₀ G (map φ 0 x) = φ.hom.app (op ⊤) (equiv₀ F x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality (hT := isTerminalTop) (f := φ) x).symm

/--
@isnad1 id=eq.0h5v.s14.8083e8764b0d from=translated src=- shape=c7c7fb66 vocab=39b3a851
-/
lemma map_equiv₀_symm (s : F.obj.obj (op ⊤)) :
    map φ 0 ((equiv₀ F).symm s) = (equiv₀ G).symm (φ.hom.app (op ⊤) s) :=
  CategoryTheory.Sheaf.H.equiv₀_symm_naturality (hT := isTerminalTop) (f := φ) s

section LongExactSequence

variable {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)

/-- The connecting homomorphism `Hⁿ⁰(X, S.X₃) → Hⁿ¹(X, S.X₁)` (with `n₁ = n₀ + 1`) of a short
exact sequence of abelian sheaves. -/
noncomputable def δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

/--
@isnad1 id=eq.2h5v.s13.1265b4c22ae2 from=translated src=- shape=ecf759de vocab=04a94d2b
-/
lemma δ_apply {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl

include hS in
/-- Exactness of `Hⁿ(S.X₁) → Hⁿ(S.X₂) → Hⁿ(S.X₃)`.
@isnad1 id=exact.1h3v.s14.20529815690f from=translated src=- shape=05074ae9 vocab=29e6a259
-/
lemma exact₂ (n : ℕ) : Function.Exact (map S.f n) (map S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₂' (constZ X) hS n)

/-- Exactness of `Hⁿ⁰(S.X₂) → Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁)`.
@isnad1 id=exact.2h4v.s14.6cc7aadd70b4 from=translated src=- shape=fe09fa09 vocab=e9d4edfe
-/
lemma exact₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Function.Exact (map S.g n₀) (δ hS n₀ n₁ h) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₃' (constZ X) hS n₀ n₁ h)

/-- Exactness of `Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁) → Hⁿ¹(S.X₂)`.
@isnad1 id=exact.2h4v.s14.f9a01727b81f from=translated src=- shape=86045546 vocab=1282643b
-/
lemma exact₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' (constZ X) hS n₀ n₁ h)

/--
@isnad1 id=eq.0h4v.s14.b62bf88c5294 from=translated src=- shape=87a36e82 vocab=149cdccc
-/
@[simp]
lemma map_g_map_f {n : ℕ} (x : H S.X₁ n) : map S.g n (map S.f n x) = 0 := by
  rw [← map_comp_apply, S.zero, map_zero_apply]

/--
@isnad1 id=eq.2h5v.s14.956f80cad494 from=translated src=- shape=b4c9c1e4 vocab=07cf5a15
-/
@[simp]
lemma δ_map_g {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₂ n₀) : δ hS n₀ n₁ h (map S.g n₀ x) = 0 :=
  (exact₃ hS n₀ n₁ h).apply_apply_eq_zero x

/--
@isnad1 id=eq.2h5v.s14.33cd10bd8abd from=translated src=- shape=367fd0a7 vocab=03dcde62
-/
@[simp]
lemma map_f_δ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) : map S.f n₁ (δ hS n₀ n₁ h x) = 0 :=
  (exact₁ hS n₀ n₁ h).apply_apply_eq_zero x

include hS in
/-- `H⁰(S.X₁) → H⁰(S.X₂)` is injective.
@isnad1 id=injectiv.1h2v.s13.a1b8f7bcdce6 from=translated src=- shape=608ff928 vocab=5e89114e
-/
lemma map_f_injective_zero : Function.Injective (map S.f 0) := by
  have := hS.mono_f
  exact Ext.postcomp_mk₀_injective_of_mono (constZ X) S.f

/-- The long exact sequence
`Hⁿ⁰(S.X₁) → Hⁿ⁰(S.X₂) → Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁) → Hⁿ¹(S.X₂) → Hⁿ¹(S.X₃)`. -/
noncomputable abbrev sequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  Ext.covariantSequence (constZ X) hS n₀ n₁ h

/--
@isnad1 id=exact.2h4v.s8.511e3b19cdb4 from=translated src=- shape=96a43373 vocab=16ee0a6b
-/
lemma sequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : (sequence hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact (constZ X) hS n₀ n₁ h

end LongExactSequence

section Injective

/-- Higher cohomology of an injective sheaf vanishes. -/
lemma eq_zero_of_injective (I : AbSheaf X) [hI : Injective I] {n : ℕ}
    (x : H I (n + 1)) : x = 0 :=
  have : Injective (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) _) I := hI
  Ext.eq_zero_of_injective x

end Injective

/-- Isomorphic sheaves have isomorphic cohomology. -/
noncomputable def addEquivOfIso {F G : AbSheaf X} (e : F ≅ G) (n : ℕ) :
    H F n ≃+ H G n where
  toFun := map e.hom n
  invFun := map e.inv n
  left_inv x := by rw [← map_comp_apply, e.hom_inv_id, map_id_apply]
  right_inv x := by rw [← map_comp_apply, e.inv_hom_id, map_id_apply]
  map_add' := map_add _

end H

end Sheaf

end TopCat
