/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.KoszulPairResolution
import Tengoku.Seed.RingTheory.Regular.RegularSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Koszul resolutions for finite weakly regular sequences

This file constructs a bounded projective resolution of the quotient by an arbitrary finite
weakly regular sequence.  The construction iterates an explicit mapping cone: adjoining a
regular element to a resolved module replaces each positive-degree term by two adjacent terms
of the old resolution.  The cone exactness proof is direct and therefore does not depend on a
Koszul-complex implementation in Mathlib.

The resulting resolution has bound equal to the sequence length.  It gives high-Tor vanishing,
transport across isomorphic target modules, and canonical finite alternating Euler data against
every finite-length left module.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingTheory.Sequence
open scoped BigOperators Pointwise

universe u

namespace AlgebraicGeometry.Chow.SerreTor.BoundedProjectiveResolution

variable {A : Type u} [CommRing A]
variable {M : ModuleCat.{u} A}

private abbrev K (d : BoundedProjectiveResolution A M) := d.resolution.complex

/-- Terms of the mapping cone of multiplication by a scalar on a resolution.-/
def coneX (d : BoundedProjectiveResolution A M) : ℕ → ModuleCat.{u} A
  | 0 => d.K.X 0
  | n + 1 => ModuleCat.of A (d.K.X (n + 1) × d.K.X n)

/-- Degree-one differential of the scalar mapping cone.-/
def coneDZero (d : BoundedProjectiveResolution A M) (r : A) :
    d.coneX 1 ⟶ d.coneX 0 :=
  ModuleCat.ofHom
    { toFun := fun x ↦ d.K.d 1 0 x.1 + r • x.2
      map_add' := by
        intros
        simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add]
        abel
      map_smul' := by
        intros
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
        module }

/-- Positive-degree successor differential of the scalar mapping cone.-/
def coneDSucc (d : BoundedProjectiveResolution A M) (r : A) (n : ℕ) :
    d.coneX (n + 2) ⟶ d.coneX (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        (d.K.d (n + 2) (n + 1) x.1 + r • x.2,
          -(d.K.d (n + 1) n x.2))
      map_add' := by
        intros
        ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add, neg_add_rev]
        <;> abel
      map_smul' := by
        intros
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_neg,
          RingHom.id_apply]
        all_goals module }

/-- The complete family of adjacent differentials in the scalar mapping cone.-/
def coneD (d : BoundedProjectiveResolution A M) (r : A) :
    ∀ n, d.coneX (n + 1) ⟶ d.coneX n
  | 0 => d.coneDZero r
  | n + 1 => d.coneDSucc r n

/--
@isnad1 id=eq.0h5v.s8.bbce7975a076 from=translated src=- shape=8537d73d vocab=25af9b99
-/
lemma coneD_sq (d : BoundedProjectiveResolution A M) (r : A) (n : ℕ) :
    d.coneD r (n + 1) ≫ d.coneD r n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
      change d.K.d 1 0 (d.K.d 2 1 x.1 + r • x.2) + r • (-(d.K.d 1 0 x.2)) = 0
      rw [map_add, map_smul]
      have h := ConcreteCategory.congr_hom (d.K.d_comp_d 2 1 0) x.1
      change d.K.d 1 0 (d.K.d 2 1 x.1) = 0 at h
      rw [h]
      module
  | succ n =>
      apply Prod.ext
      · change d.K.d (n + 2) (n + 1)
            (d.K.d (n + 3) (n + 2) x.1 + r • x.2) +
            r • (-(d.K.d (n + 2) (n + 1) x.2)) = 0
        rw [map_add, map_smul]
        have h := ConcreteCategory.congr_hom
          (d.K.d_comp_d (n + 3) (n + 2) (n + 1)) x.1
        change d.K.d (n + 2) (n + 1) (d.K.d (n + 3) (n + 2) x.1) = 0 at h
        rw [h]
        module
      · change -(d.K.d (n + 1) n (-(d.K.d (n + 2) (n + 1) x.2))) = 0
        rw [map_neg]
        have h := ConcreteCategory.congr_hom
          (d.K.d_comp_d (n + 2) (n + 1) n) x.2
        change d.K.d (n + 1) n (d.K.d (n + 2) (n + 1) x.2) = 0 at h
        rw [h]
        simp

/-- The chain complex underlying the scalar mapping cone.-/
noncomputable def coneComplex (d : BoundedProjectiveResolution A M) (r : A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of d.coneX (d.coneD r) (d.coneD_sq r)

/--
@isnad1 id=eq.0h4v.s7.ef2310c837d3 from=translated src=- shape=ffc793c9 vocab=528b5dba
-/
@[simp]
lemma coneComplex_d_zero (d : BoundedProjectiveResolution A M) (r : A) :
    (d.coneComplex r).d 1 0 = d.coneDZero r := by
  change ChainComplex.of.d d.coneX (d.coneD r) 1 0 = d.coneDZero r
  change ChainComplex.of.d d.coneX (d.coneD r) (0 + 1) 0 = d.coneDZero r
  rw [ChainComplex.of_d]
  rfl

/--
@isnad1 id=eq.0h5v.s7.37dde082620d from=translated src=- shape=01eadffc vocab=60bf7815
-/
@[simp]
lemma coneComplex_d_succ (d : BoundedProjectiveResolution A M) (r : A) (n : ℕ) :
    (d.coneComplex r).d (n + 2) (n + 1) = d.coneDSucc r n := by
  change ChainComplex.of.d d.coneX (d.coneD r) (n + 2) (n + 1) = d.coneDSucc r n
  change ChainComplex.of.d d.coneX (d.coneD r) ((n + 1) + 1) (n + 1) =
    d.coneDSucc r n
  rw [ChainComplex.of_d]
  rfl

/--
@isnad1 id=iszero.1h5v.s6.a254391220fb from=translated src=- shape=9d392ff8 vocab=86ee470e
-/
theorem coneComplex_isZero (d : BoundedProjectiveResolution A M) (r : A)
    (n : ℕ) (hn : d.bound + 1 < n) : IsZero ((d.coneComplex r).X n) := by
  cases n with
  | zero => omega
  | succ n =>
      change IsZero (ModuleCat.of A (d.K.X (n + 1) × d.K.X n))
      apply ModuleCat.isZero_iff_subsingleton.mpr
      have h₁ : IsZero (d.K.X (n + 1)) := d.isZero (n + 1) (by omega)
      have h₂ : IsZero (d.K.X n) := d.isZero n (by omega)
      haveI : Subsingleton (d.K.X (n + 1)) :=
        ModuleCat.isZero_iff_subsingleton.mp h₁
      haveI : Subsingleton (d.K.X n) :=
        ModuleCat.isZero_iff_subsingleton.mp h₂
      infer_instance

/-- The degree-zero map from the cone to the quotient of the resolved module by `r`.-/
noncomputable def coneAugmentationLinear (d : BoundedProjectiveResolution A M) (r : A) :
    d.K.X 0 →ₗ[A] QuotSMulTop r M :=
  (Submodule.mkQ (r • (⊤ : Submodule A M))).comp (d.resolution.π.f 0).hom

/--
@isnad1 id=eq.0h4v.s13.17397a2944f4 from=translated src=- shape=6adcbba1 vocab=ee479fcd
-/
lemma cone_d_comp_augmentation (d : BoundedProjectiveResolution A M) (r : A) :
    d.coneD r 0 ≫ ModuleCat.ofHom (d.coneAugmentationLinear r) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Submodule.Quotient.mk
    (d.resolution.π.f 0 (d.K.d 1 0 x.1 + r • x.2)) : QuotSMulTop r M) = 0
  rw [map_add, map_smul]
  have h := ConcreteCategory.congr_hom d.resolution.complex_d_comp_π_f_zero x.1
  change d.resolution.π.f 0 (d.K.d 1 0 x.1) = 0 at h
  rw [h, zero_add]
  apply (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule A M))).mpr
  exact Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

/-- Augmentation of the cone complex to the single complex on the scalar quotient.-/
noncomputable def coneAugmentation (d : BoundedProjectiveResolution A M) (r : A) :
    d.coneComplex r ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (QuotSMulTop r M)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨
    ModuleCat.ofHom (d.coneAugmentationLinear r), d.cone_d_comp_augmentation r⟩

/--
@isnad1 id=exact.0h4v.s10.d12c04276af0 from=translated src=- shape=8e1584c0 vocab=656e2ca9
-/
theorem cone_augmentation_exact (d : BoundedProjectiveResolution A M) (r : A) :
    (ShortComplex.moduleCatMk (d.coneDZero r).hom (d.coneAugmentationLinear r)
      (by
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (d.cone_d_comp_augmentation r) x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change d.K.X 0 at x
  change (Submodule.Quotient.mk
    (d.resolution.π.f 0 x) : QuotSMulTop r M) = 0 at hx
  have hmem : d.resolution.π.f 0 x ∈ r • (⊤ : Submodule A M) :=
    (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule A M))).mp hx
  rcases (Submodule.mem_smul_pointwise_iff_exists _ r (⊤ : Submodule A M)).mp hmem with
    ⟨m, -, hm⟩
  have hsurj : Function.Surjective (d.resolution.π.f 0) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  rcases hsurj m with ⟨y, hy⟩
  have hker : d.resolution.π.f 0 (x - r • y) = 0 := by
    rw [map_sub, map_smul, hy]
    exact sub_eq_zero.mpr hm.symm
  have hExact := d.resolution.exact₀
  rw [ShortComplex.moduleCat_exact_iff] at hExact
  have hExact' : ∀ x : d.K.X 0, d.resolution.π.f 0 x = 0 →
      ∃ z : d.K.X 1, d.K.d 1 0 z = x := by
    simpa only using hExact
  rcases hExact' (x - r • y) hker with ⟨z, hz⟩
  refine ⟨(z, y), ?_⟩
  change d.K.d 1 0 z + r • y = x
  rw [hz]
  abel

/--
@isnad1 id=ex.1h5v.s11.af22a2663d4f from=translated src=- shape=07f70fe8 vocab=3b9ee983
-/
lemma resolution_exact_lift (d : BoundedProjectiveResolution A M) (n : ℕ)
    (x : d.K.X (n + 1)) (hx : d.K.d (n + 1) n x = 0) :
    ∃ z : d.K.X (n + 2), d.K.d (n + 2) (n + 1) z = x := by
  have hExact := d.resolution.exact_succ n
  rw [ShortComplex.moduleCat_exact_iff] at hExact
  simpa only using hExact x hx

/--
@isnad1 id=ex.1h4v.s12.24ef71db3d8c from=translated src=- shape=fc74e782 vocab=00678b1f
-/
lemma resolution_exact_zero_lift (d : BoundedProjectiveResolution A M)
    (x : d.K.X 0) (hx : d.resolution.π.f 0 x = 0) :
    ∃ z : d.K.X 1, d.K.d 1 0 z = x := by
  have hExact := d.resolution.exact₀
  rw [ShortComplex.moduleCat_exact_iff] at hExact
  simpa only using hExact x hx

/--
@isnad1 id=exactat.1h5v.s8.c6f2dd6eb5d4 from=translated src=- shape=3c172e13 vocab=d540c268
-/
theorem coneComplex_exactAt_succ (d : BoundedProjectiveResolution A M) (r : A)
    (reg : IsSMulRegular M r) (n : ℕ) :
    (d.coneComplex r).ExactAt (n + 1) := by
  cases n with
  | zero =>
      rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      change d.K.X 1 × d.K.X 0 at x
      change d.K.d 1 0 x.1 + r • x.2 = 0 at hx
      have hrπ : r • d.resolution.π.f 0 x.2 = 0 := by
        have h := congrArg (d.resolution.π.f 0) hx
        rw [map_add, map_smul, map_zero] at h
        have hdπ := ConcreteCategory.congr_hom
          d.resolution.complex_d_comp_π_f_zero x.1
        change d.resolution.π.f 0 (d.K.d 1 0 x.1) = 0 at hdπ
        rwa [hdπ, zero_add] at h
      have hπ : d.resolution.π.f 0 x.2 = 0 := reg.right_eq_zero_of_smul hrπ
      rcases d.resolution_exact_zero_lift x.2 hπ with ⟨z, hz⟩
      have hcycle : d.K.d 1 0 (x.1 + r • z) = 0 := by
        rw [map_add, map_smul, hz]
        exact hx
      rcases d.resolution_exact_lift 0 (x.1 + r • z) hcycle with ⟨w, hw⟩
      refine ⟨(w, -z), ?_⟩
      change (d.K.d 2 1 w + r • (-z), -(d.K.d 1 0 (-z))) = x
      apply Prod.ext
      · rw [hw, smul_neg]
        abel
      · rw [map_neg, hz]
        simp
  | succ n =>
      rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      change d.K.X (n + 2) × d.K.X (n + 1) at x
      change (d.coneComplex r).d (n + 2) (n + 1) x = 0 at hx
      rw [d.coneComplex_d_succ r n] at hx
      have hfirst := congrArg Prod.fst hx
      have hsecond := congrArg Prod.snd hx
      change d.K.d (n + 2) (n + 1) x.1 + r • x.2 = 0 at hfirst
      change -(d.K.d (n + 1) n x.2) = 0 at hsecond
      have hx₂ : d.K.d (n + 1) n x.2 = 0 := neg_eq_zero.mp hsecond
      rcases d.resolution_exact_lift n x.2 hx₂ with ⟨z, hz⟩
      have hcycle : d.K.d (n + 2) (n + 1) (x.1 + r • z) = 0 := by
        rw [map_add, map_smul, hz]
        exact hfirst
      rcases d.resolution_exact_lift (n + 1) (x.1 + r • z) hcycle with ⟨w, hw⟩
      refine ⟨(w, -z), ?_⟩
      change (d.coneComplex r).d (n + 3) (n + 2) (w, -z) = x
      rw [d.coneComplex_d_succ r (n + 1)]
      change (d.K.d (n + 3) (n + 2) w + r • (-z),
        -(d.K.d (n + 2) (n + 1) (-z))) = x
      apply Prod.ext
      · rw [hw, smul_neg]
        abel
      · rw [map_neg, hz]
        simp

/-- The scalar cone packaged as a projective resolution when the scalar is regular.-/
noncomputable def coneResolution (d : BoundedProjectiveResolution A M) (r : A)
    (reg : IsSMulRegular M r) :
    ProjectiveResolution (ModuleCat.of A (QuotSMulTop r M)) where
  complex := d.coneComplex r
  projective n := by
    cases n with
    | zero => exact d.resolution.projective 0
    | succ n =>
        change Projective (ModuleCat.of A (d.K.X (n + 1) × d.K.X n))
        infer_instance
  π := d.coneAugmentation r
  quasiIso := ⟨fun n ↦ by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨d.cone_augmentation_exact r, ?_⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by ext x; rfl) (by rfl)
        rw [ModuleCat.epi_iff_surjective]
        change Function.Surjective (d.coneAugmentationLinear r)
        exact (Submodule.mkQ_surjective _).comp
          ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply d.coneComplex_exactAt_succ r reg
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- Extending a bounded projective resolution by one regular element via its Koszul cone.-/
noncomputable def cone (d : BoundedProjectiveResolution A M) (r : A)
    (reg : IsSMulRegular M r) :
    BoundedProjectiveResolution A (ModuleCat.of A (QuotSMulTop r M)) where
  resolution := d.coneResolution r reg
  bound := d.bound + 1
  isZero n hn := d.coneComplex_isZero r n hn

/-- Finite length of every tensor-applied term is preserved by a Koszul cone.
@isnad1 id=ne.2h6v.s13.41cc2f0f1dd3 from=translated src=- shape=53c85c3a vocab=7eda27b9
-/
theorem cone_finiteTensorTerms (d : BoundedProjectiveResolution A M) (r : A)
    (reg : IsSMulRegular M r)
    (L : ModuleCat.{u} A)
    (h : ∀ n, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj (d.K.X n)) : Type u) ≠ ⊤) :
    ∀ n, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
        ((d.cone r reg).resolution.complex.X n)) :
        Type u) ≠ ⊤ := by
  intro n
  cases n with
  | zero => exact h 0
  | succ n =>
      change Module.length A
        (TensorProduct A (↑L : Type u) (d.K.X (n + 1) × d.K.X n)) ≠ ⊤
      rw [(TensorProduct.prodRight A A (↑L : Type u) (d.K.X (n + 1)) (d.K.X n)).length_eq,
        Module.length_prod]
      exact WithTop.add_ne_top.mpr ⟨h (n + 1), h n⟩

/-- Tensoring a zero module produces a module of finite (indeed zero) length.
@isnad1 id=ne.1h3v.s8.8ba93316fd21 from=translated src=- shape=62f8d98c vocab=c80baaa5
-/
theorem finiteTensorTerm_of_isZero (L P : ModuleCat.{u} A) (hP : IsZero P) :
    Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj P) : Type u) ≠ ⊤ := by
  have hZ := ((tensoringLeft (ModuleCat.{u} A)).obj L).map_isZero hP
  have hs : Subsingleton
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj P) : Type u) :=
    ModuleCat.isZero_iff_subsingleton.mp hZ
  rw [Module.length_eq_zero_iff.mpr hs]
  exact WithTop.zero_ne_top

/-- A projective module, viewed as its own degree-zero bounded resolution.-/
noncomputable def self (P : ModuleCat.{u} A) [Projective P] :
    BoundedProjectiveResolution A P where
  resolution := ProjectiveResolution.self P
  bound := 0
  isZero n hn := by
    exact HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 P n (by omega)

/-- A finite-length module tensored with the degree-zero resolution of `A` has finite-length
terms in every degree.
@isnad1 id=ne.1h3v.s9.3fd9d6e1da3f from=translated src=- shape=d935eaac vocab=c61a121d
-/
theorem self_finiteTensorTerms (L : ModuleCat.{u} A)
    (hL : Module.length A (↑L : Type u) ≠ ⊤) :
    ∀ n, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
        ((self (ModuleCat.of A A)).resolution.complex.X n)) : Type u) ≠ ⊤ := by
  intro n
  cases n with
  | zero =>
      change Module.length A (TensorProduct A (↑L : Type u) A) ≠ ⊤
      rwa [(TensorProduct.rid A (↑L : Type u)).length_eq]
  | succ n =>
      apply finiteTensorTerm_of_isZero (A := A) L
      exact HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 (ModuleCat.of A A) (n + 1)
        (by omega)

/-- Iterating the Koszul cone along a weakly regular sequence produces a bounded projective
resolution of the quotient by that sequence.-/
noncomputable def ofWeaklyRegular {P : ModuleCat.{u} A}
    (d : BoundedProjectiveResolution A P) :
    (rs : List A) → IsWeaklyRegular P rs →
      BoundedProjectiveResolution A
        (ModuleCat.of A (P ⧸ (Ideal.ofList rs • ⊤ : Submodule A P)))
  | [], _ => by
      exact BoundedProjectiveResolution.ofIso (A := A) d
        (Submodule.quotEquivOfEqBot
          (Ideal.ofList [] • ⊤ : Submodule A P) (by simp)).symm.toModuleIso
  | r :: rs, reg => by
      have hreg := (isWeaklyRegular_cons_iff P r rs).mp reg
      let tail := ofWeaklyRegular
        (P := ModuleCat.of A (QuotSMulTop r P)) (d.cone r hreg.1) rs hreg.2
      exact BoundedProjectiveResolution.ofIso (A := A) tail
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner P r rs).symm.toModuleIso

/-- The iterated Koszul construction preserves finite length of all tensor-applied resolution
terms.
@isnad1 id=ne.2h6v.s12.1fca0147a94b from=translated src=- shape=fff2a3be vocab=df80840f
-/
theorem ofWeaklyRegular_finiteTensorTerms {P : ModuleCat.{u} A}
    (d : BoundedProjectiveResolution A P) (rs : List A)
    (reg : IsWeaklyRegular P rs) (L : ModuleCat.{u} A)
    (h : ∀ n, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
        (d.resolution.complex.X n)) : Type u) ≠ ⊤) :
    ∀ n, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
        ((d.ofWeaklyRegular rs reg).resolution.complex.X n)) : Type u) ≠ ⊤ := by
  induction rs generalizing P with
  | nil =>
      intro n
      change Module.length A
        (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
          (d.resolution.complex.X n)) : Type u) ≠ ⊤
      exact h n
  | cons r rs ih =>
      have hreg := (isWeaklyRegular_cons_iff P r rs).mp reg
      have hcone := d.cone_finiteTensorTerms r hreg.1 L h
      have htail := ih (d.cone r hreg.1) hreg.2 hcone
      intro n
      change Module.length A
        (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
          (((d.cone r hreg.1).ofWeaklyRegular rs hreg.2).resolution.complex.X n)) :
            Type u) ≠ ⊤
      exact htail n

/--
@isnad1 id=eq.1h4v.s9.823fb7edce9a from=translated src=- shape=d0883422 vocab=134f78c4
-/
@[simp]
theorem ofWeaklyRegular_bound (d : BoundedProjectiveResolution A M)
    (rs : List A) (reg : IsWeaklyRegular M rs) :
    (d.ofWeaklyRegular rs reg).bound = d.bound + rs.length := by
  induction rs generalizing M with
  | nil => rfl
  | cons r rs ih =>
      rw [ofWeaklyRegular]
      simp only [ofIso]
      rw [ih]
      simp [cone]
      omega

/-- The recursive Koszul resolution of a quotient by an arbitrary finite weakly regular
sequence.-/
noncomputable def koszul (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs) :
    BoundedProjectiveResolution A (ModuleCat.of A (A ⧸ Ideal.ofList rs)) := by
  let d := (self (ModuleCat.of A A)).ofWeaklyRegular rs reg
  have h : (Ideal.ofList rs • ⊤ : Submodule A A) = Ideal.ofList rs := by simp
  exact BoundedProjectiveResolution.ofIso (A := A) d
    (Submodule.quotEquivOfEq _ _ h).toModuleIso

/--
@isnad1 id=eq.1h2v.s7.b060a3b4cfd1 from=translated src=- shape=7d6abb9d vocab=ac287804
-/
@[simp]
theorem koszul_bound (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs) :
    (koszul rs reg).bound = rs.length := by
  simp only [koszul, BoundedProjectiveResolution.ofIso]
  rw [ofWeaklyRegular_bound]
  simp [self]

/-- A finite-length left module makes every tensor-applied term of the recursive Koszul
resolution finite length.
@isnad1 id=ne.2h4v.s10.8d504cecff6e from=translated src=- shape=94aca426 vocab=e8806b3b
-/
theorem koszul_finiteTensorTerms (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs)
    (L : ModuleCat.{u} A) (hL : Module.length A (↑L : Type u) ≠ ⊤) :
    ∀ n, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
        ((koszul rs reg).resolution.complex.X n)) : Type u) ≠ ⊤ := by
  have h := ofWeaklyRegular_finiteTensorTerms (self (ModuleCat.of A A)) rs reg L
    (self_finiteTensorTerms L hL)
  intro n
  change Module.length A
    (↑(((tensoringLeft (ModuleCat.{u} A)).obj L).obj
      (((self (ModuleCat.of A A)).ofWeaklyRegular rs reg).resolution.complex.X n)) :
        Type u) ≠ ⊤
  exact h n

/-- Tor against the quotient by a finite weakly regular sequence vanishes above the sequence
length.
@isnad1 id=iszero.2h4v.s7.0fda599756ad from=translated src=- shape=c12a2ee1 vocab=121a499c
-/
theorem isZero_module_koszul (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs)
    (L : ModuleCat.{u} A) (n : ℕ) (hn : rs.length < n) :
    IsZero (module A L (ModuleCat.of A (A ⧸ Ideal.ofList rs)) n) := by
  apply (koszul rs reg).isZero_module A L
  rwa [koszul_bound]

/-- High-Tor vanishing for a weakly regular sequence transports across any isomorphic target
module.
@isnad1 id=iszero.2h6v.s7.a34eb97f8894 from=translated src=- shape=6345f1c2 vocab=adb591f7
-/
theorem isZero_module_of_iso_koszul (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs)
    (L : ModuleCat.{u} A) {N' : ModuleCat.{u} A}
    (e : ModuleCat.of A (A ⧸ Ideal.ofList rs) ≅ N')
    (n : ℕ) (hn : rs.length < n) : IsZero (module A L N' n) := by
  apply ((koszul rs reg).ofIso A e).isZero_module A L
  change (koszul rs reg).bound < n
  rwa [koszul_bound]

/-- Canonical Serre--Tor Euler data for a finite-length module against a quotient by a finite
weakly regular sequence.-/
noncomputable def koszulEulerData (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs)
    (L : ModuleCat.{u} A) (hL : Module.length A (↑L : Type u) ≠ ⊤) :
    EulerData A L (ModuleCat.of A (A ⧸ Ideal.ofList rs)) :=
  (koszul rs reg).toEulerDataOfFiniteTerms A L
    (fun n _ ↦ koszul_finiteTensorTerms rs reg L hL n)

/-- The resulting Serre multiplicity is the finite alternating Tor-length sum through the
length of the sequence.
@isnad1 id=eq.2h3v.s8.424b310fb802 from=translated src=- shape=d86f3e27 vocab=e5802c41
-/
theorem koszulEulerData_multiplicity (rs : List A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) rs)
    (L : ModuleCat.{u} A) (hL : Module.length A (↑L : Type u) ≠ ⊤) :
    (koszulEulerData rs reg L hL).multiplicity =
      ∑ n ∈ Finset.range (rs.length + 1),
        signedLength A L (ModuleCat.of A (A ⧸ Ideal.ofList rs)) n := by
  simp only [koszulEulerData, toEulerDataOfFiniteTerms, toEulerData,
    EulerData.multiplicity, koszul_bound]

end AlgebraicGeometry.Chow.SerreTor.BoundedProjectiveResolution
