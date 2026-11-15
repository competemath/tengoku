import Tengoku.Seed.AlgebraicGeometry.Sites.Fpqc
import Tengoku.Seed.AlgebraicGeometry.Limits
import Tengoku.Seed.Algebra.Category.Grp.AB
import Tengoku.Seed.Algebra.Category.Grp.Ulift
import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Tengoku.Seed.CategoryTheory.Sites.SheafCohomology.Basic
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Tengoku.Seed.RingTheory.ClassGroup
import Tengoku.Seed.RingTheory.PicardGroup
import Tengoku.Seed.Data.Int.Order.Units
import Tengoku.Seed.Data.Fintype.Units
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.Algebra.Group.Subgroup.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Definitions/Def_AlgebraicGeometry_FppfCohomologyLES.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable abbrev constIntSheaf : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))

/--
@isnad1 id=eq.0h4v.s6.6c923066f782 from=translated src=- shape=cd5dd1d0 vocab=580ce42e
-/
theorem sheafH_eq_ext (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    F.H n = Ext (constIntSheaf J) F n := rfl

variable {J}

noncomputable def cohomologyMap {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (n : ℕ) :
    F.H n →+ G.H n :=
  (Ext.mk₀ φ).postcomp (constIntSheaf J) (add_zero n)

/--
@isnad1 id=eq.0h7v.s9.164f1e862088 from=translated src=- shape=cb8dfc6e vocab=e18a3357
-/
@[simp]
lemma cohomologyMap_apply {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (n : ℕ)
    (x : Ext (constIntSheaf J) F n) :
    cohomologyMap φ n x = x.comp (Ext.mk₀ φ) (add_zero n) := rfl

noncomputable def cohomologyδ {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.X₃.H n₀ →+ S.X₁.H n₁ :=
  hS.extClass.postcomp (constIntSheaf J) h

/--
@isnad1 id=eq.2h6v.s11.db49ead6cac7 from=translated src=- shape=8a7d3ac6 vocab=3e568466
-/
@[simp]
lemma cohomologyδ_apply {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S.X₃ n₀) :
    cohomologyδ hS n₀ n₁ h x = x.comp hS.extClass h := rfl

/--
@isnad1 id=eq.0h5v.s9.5b36a868085a from=translated src=- shape=fa6f23c9 vocab=ea67a154
-/
theorem cohomologyMap_id (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ)
    (x : Ext (constIntSheaf J) F n) :
    cohomologyMap (𝟙 F) n x = x := by
  rw [cohomologyMap_apply]; simp

/--
@isnad1 id=eq.0h9v.s11.6d44ed15d098 from=translated src=- shape=cefac1aa vocab=8eda9a7a
-/
theorem cohomologyMap_comp {F G H : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (ψ : G ⟶ H)
    (n : ℕ) (x : Ext (constIntSheaf J) F n) :
    cohomologyMap (φ ≫ ψ) n x = cohomologyMap ψ n (cohomologyMap φ n x) := by
  rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero]

/--
@isnad1 id=exact.1h4v.s12.f9162f760248 from=translated src=- shape=5e1ccbe5 vocab=c6f1f6e7
-/
theorem cohomology_exact_two {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) := by
  have h2 := Ext.covariant_sequence_exact₂' (constIntSheaf J) hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at h2
  exact h2

/--
@isnad1 id=exact.2h5v.s12.a7d75656b05f from=translated src=- shape=385091a2 vocab=207cd513
-/
theorem cohomology_exact_three {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) := by
  have h3 := Ext.covariant_sequence_exact₃' (constIntSheaf J) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h3
  exact h3

/--
@isnad1 id=exact.2h5v.s12.dee996098a17 from=translated src=- shape=ad10adc2 vocab=d5b5ab23
-/
theorem cohomology_exact_one {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) := by
  have h1 := Ext.covariant_sequence_exact₁' (constIntSheaf J) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h1
  exact h1

/--
@isnad1 id=injectiv.0h5v.s9.d1924977e780 from=translated src=- shape=cae3cd2b vocab=104812ef
-/
theorem cohomologyMap_zero_injective_of_mono {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [Mono φ] :
    Function.Injective (cohomologyMap φ 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective (constIntSheaf J) F).surjective x
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective (constIntSheaf J) F).surjective y
  rw [cohomologyMap_apply, cohomologyMap_apply] at hxy
  have hxy' : Ext.mk₀ (a ≫ φ) = Ext.mk₀ (b ≫ φ) := by
    simpa only [Ext.mk₀_comp_mk₀] using hxy
  have hab : a ≫ φ = b ≫ φ := (Ext.mk₀_bijective _ _).injective hxy'
  rw [cancel_mono] at hab
  rw [hab]

/--
@isnad1 id=surjecti.1h7v.s9.62a2fb55cdc0 from=translated src=- shape=7919b7ed vocab=3c9a4964
-/
theorem cohomologyMap_surjective_of_section {F G : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) (s : G ⟶ F) (hs : s ≫ φ = 𝟙 G) (n : ℕ) :
    Function.Surjective (cohomologyMap φ n) := by
  intro y
  refine ⟨cohomologyMap s n y, ?_⟩
  rw [← cohomologyMap_comp, hs, cohomologyMap_id]

/--
@isnad1 id=and.1h3v.s14.bb1fff8b4695 from=translated src=- shape=5fce1151 vocab=93655e09
-/
theorem sixTermLES {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) :
    Function.Injective (cohomologyMap S.f 0) ∧
    Function.Exact (cohomologyMap S.f 0) (cohomologyMap S.g 0) ∧
    Function.Exact (cohomologyMap S.g 0) (cohomologyδ hS 0 1 rfl) ∧
    Function.Exact (cohomologyδ hS 0 1 rfl) (cohomologyMap S.f 1) ∧
    Function.Exact (cohomologyMap S.f 1) (cohomologyMap S.g 1) := by
  have : Mono S.f := hS.mono_f
  exact ⟨cohomologyMap_zero_injective_of_mono S.f, cohomology_exact_two hS 0,
    cohomology_exact_three hS 0 1 rfl, cohomology_exact_one hS 0 1 rfl,
    cohomology_exact_two hS 1⟩

noncomputable def cohomologyComposableArrows {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  Ext.covariantSequence (constIntSheaf J) hS n₀ n₁ h

/--
@isnad1 id=exact.2h5v.s7.81fbd4692a6c from=translated src=- shape=1577d2fb vocab=7d370151
-/
theorem cohomologyComposableArrows_exact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyComposableArrows hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact (constIntSheaf J) hS n₀ n₁ h

noncomputable def cohomologyZeroAddEquivHom (F : Sheaf J AddCommGrpCat.{w}) :
    F.H 0 ≃+ (constIntSheaf J ⟶ F) :=
  Ext.addEquiv₀

noncomputable def biprodSES (F G : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (biprod.inl : F ⟶ F ⊞ G) (biprod.snd : F ⊞ G ⟶ G) (by simp)

/--
@isnad1 id=shortexa.0h4v.s7.ee706a3357c7 from=translated src=- shape=ca8317cb vocab=162126cb
-/
theorem biprodSES_shortExact (F G : Sheaf J AddCommGrpCat.{w}) :
    (biprodSES F G).ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact

/--
@isnad1 id=eq.1h7v.s11.e8b396490fb9 from=translated src=- shape=afe4fbb1 vocab=5d321d4b
-/
theorem biprodSES_delta_apply_eq_zero (F G : Sheaf J AddCommGrpCat.{w}) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) (x : Ext (constIntSheaf J) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x = 0 := by
  have hsurj : Function.Surjective (cohomologyMap (biprodSES F G).g n₀) :=
    cohomologyMap_surjective_of_section (biprodSES F G).g biprod.inr (by simp [biprodSES]) n₀
  obtain ⟨z, rfl⟩ := hsurj x
  exact (cohomology_exact_three (biprodSES_shortExact F G) n₀ n₁ h).apply_apply_eq_zero z

end GenericSite

section FppfSite

open AlgebraicGeometry

/--
@isnad1 id=isgrothe.0h0v.s5.21d7c07f737e from=translated src=- shape=6516253f vocab=a3a70cca
-/
instance fppfSheavesIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} Scheme.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall Scheme.fppfTopology Ab.{u + 1}

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable abbrev FppfH (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

/--
@isnad1 id=eq.0h2v.s6.e636699c1d53 from=translated src=- shape=35cf72f2 vocab=8e68f044
-/
theorem fppfH_eq_sheafH (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    FppfH F n = F.H n := rfl

/--
@isnad1 id=exact.1h2v.s12.bbee9e3681fb from=translated src=- shape=ffcda3e6 vocab=559a6063
-/
theorem fppf_les_exact_two {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) :=
  cohomology_exact_two hS n

/--
@isnad1 id=exact.2h3v.s12.ca0583ed534d from=translated src=- shape=6c4795c0 vocab=41760091
-/
theorem fppf_les_exact_three {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) :=
  cohomology_exact_three hS n₀ n₁ h

/--
@isnad1 id=exact.2h3v.s12.e2d008e001f5 from=translated src=- shape=9ba0e081 vocab=773e231b
-/
theorem fppf_les_exact_one {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) :=
  cohomology_exact_one hS n₀ n₁ h

/--
@isnad1 id=and.1h1v.s14.3bb4f1ec03d5 from=translated src=- shape=8f3f8fe4 vocab=68303883
-/
theorem fppf_sixTermLES {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) :
    Function.Injective (cohomologyMap S.f 0) ∧
    Function.Exact (cohomologyMap S.f 0) (cohomologyMap S.g 0) ∧
    Function.Exact (cohomologyMap S.g 0) (cohomologyδ hS 0 1 rfl) ∧
    Function.Exact (cohomologyδ hS 0 1 rfl) (cohomologyMap S.f 1) ∧
    Function.Exact (cohomologyMap S.f 1) (cohomologyMap S.g 1) :=
  sixTermLES hS

/--
@isnad1 id=exact.2h3v.s7.64120c4ca881 from=translated src=- shape=162d0d3f vocab=bbfc61fa
-/
theorem fppf_composableArrowsLES_exact
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyComposableArrows hS n₀ n₁ h).Exact :=
  cohomologyComposableArrows_exact hS n₀ n₁ h

noncomputable def fppfCohomologyZeroAddEquivHom (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    FppfH F 0 ≃+ (constIntSheaf Scheme.fppfTopology.{u} ⟶ F) :=
  cohomologyZeroAddEquivHom F

/--
@isnad1 id=shortexa.0h2v.s7.74e109a0f980 from=translated src=- shape=94b56b91 vocab=93189077
-/
theorem fppf_satGate_biprodSES_shortExact (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    (biprodSES F G).ShortExact :=
  biprodSES_shortExact F G

/--
@isnad1 id=exact.0h3v.s12.ea6426ef0d01 from=translated src=- shape=549b118b vocab=88817d78
-/
theorem fppf_satGate_les_applies (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Function.Exact (cohomologyMap (biprodSES F G).f n) (cohomologyMap (biprodSES F G).g n) :=
  fppf_les_exact_two (biprodSES_shortExact F G) n

/--
@isnad1 id=eq.1h5v.s11.9637229cfec7 from=translated src=- shape=fd60820c vocab=60866184
-/
theorem fppf_satGate_delta_eq_zero (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x = 0 :=
  biprodSES_delta_apply_eq_zero F G n₀ n₁ h x

end WithLocalInstances

end FppfSite

section ElementaryComputations

/--
@isnad1 id=eq.0h0v.s4.827ab550e948 from=translated src=- shape=35225b15 vocab=a68fc0d2
-/
theorem classGroup_int_card_eq_one : Fintype.card (ClassGroup ℤ) = 1 :=
  card_classGroup_eq_one

/--
@isnad1 id=subsingl.0h0v.s2.2b5420e95513 from=translated src=- shape=87ceb31f vocab=704a1f1a
-/
theorem classGroup_int_subsingleton : Subsingleton (ClassGroup ℤ) :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq card_classGroup_eq_one)

/--
@isnad1 id=eq.0h0v.s3.bedbc1f0bfad from=translated src=- shape=35225b15 vocab=dad255ee
-/
theorem natCard_classGroup_int : Nat.card (ClassGroup ℤ) = 1 := by
  rw [Nat.card_eq_fintype_card, classGroup_int_card_eq_one]

/--
@isnad1 id=subsingl.0h0v.s2.01683e995f15 from=translated src=- shape=87ceb31f vocab=11d208be
-/
theorem pic_int_subsingleton : Subsingleton (CommRing.Pic ℤ) :=
  inferInstance

/--
@isnad1 id=eq.1h1v.s5.87220bda4823 from=translated src=- shape=cd0bfeb2 vocab=716ae80b
-/
theorem intUnits_powMonoidHom_ker_of_odd (p : ℕ) (hp : Odd p) :
    (powMonoidHom p : ℤˣ →* ℤˣ).ker = ⊥ := by
  ext u
  simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_bot]
  rw [Int.units_pow_eq_pow_mod_two u p, Nat.odd_iff.mp hp, pow_one]

/--
@isnad1 id=eq.0h0v.s5.c18bc5cd3889 from=translated src=- shape=81fea6b1 vocab=43673c66
-/
theorem intUnits_powMonoidHom_ker_two :
    (powMonoidHom 2 : ℤˣ →* ℤˣ).ker = ⊤ := by
  ext u
  simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_top, iff_true]
  exact Int.units_sq u

/--
@isnad1 id=eq.1h1v.s5.d4bd6e80f557 from=translated src=- shape=cd0bfeb2 vocab=abafd11d
-/
theorem intUnits_powMonoidHom_range_of_odd (p : ℕ) (hp : Odd p) :
    (powMonoidHom p : ℤˣ →* ℤˣ).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro u
  refine ⟨u, ?_⟩
  rw [powMonoidHom_apply, Int.units_pow_eq_pow_mod_two u p, Nat.odd_iff.mp hp, pow_one]

/--
@isnad1 id=eq.0h0v.s5.dd0cdd2e2f9a from=translated src=- shape=81fea6b1 vocab=929f83e7
-/
theorem intUnits_powMonoidHom_range_two :
    (powMonoidHom 2 : ℤˣ →* ℤˣ).range = ⊥ := by
  ext u
  simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_bot]
  constructor
  · rintro ⟨v, rfl⟩
    exact Int.units_sq v
  · rintro rfl
    exact ⟨1, one_pow 2⟩

/--
@isnad1 id=eq.0h0v.s3.680a0d1990fe from=translated src=- shape=35225b15 vocab=edb7a2ac
-/
theorem natCard_intUnits : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/--
@isnad1 id=eq.1h1v.s6.1b3371022dd0 from=translated src=- shape=b3c558aa vocab=291f9ddb
-/
theorem natCard_intUnits_pthTorsion (p : ℕ) (hp : p.Prime) :
    Nat.card (powMonoidHom p : ℤˣ →* ℤˣ).ker = if p = 2 then 2 else 1 := by
  split_ifs with h
  · subst h
    rw [intUnits_powMonoidHom_ker_two, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  · rw [intUnits_powMonoidHom_ker_of_odd p (hp.odd_of_ne_two h), Subgroup.card_bot]

/--
@isnad1 id=eq.1h1v.s6.46c6e71d7ae4 from=translated src=- shape=f91b8e56 vocab=66bace82
-/
theorem natCard_intUnits_modPthPowers (p : ℕ) (hp : p.Prime) :
    Nat.card (ℤˣ ⧸ (powMonoidHom p : ℤˣ →* ℤˣ).range) = if p = 2 then 2 else 1 := by
  split_ifs with h
  · subst h
    rw [intUnits_powMonoidHom_range_two]
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := ℤˣ)).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · rw [intUnits_powMonoidHom_range_of_odd p (hp.odd_of_ne_two h)]
    have : Subsingleton (ℤˣ ⧸ (⊤ : Subgroup ℤˣ)) := QuotientGroup.subsingleton_quotient_top
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨this, ⟨1⟩⟩

/--
@isnad1 id=eq.0h1v.s7.3df8d8f25f83 from=translated src=- shape=c0427fdb vocab=ebd57d80
-/
theorem intUnits_kummer_exact_left (p : ℕ) :
    ((powMonoidHom p : ℤˣ →* ℤˣ).ker.subtype).range = (powMonoidHom p : ℤˣ →* ℤˣ).ker :=
  Subgroup.range_subtype _

/--
@isnad1 id=eq.0h1v.s8.80a7c5015150 from=translated src=- shape=730ff105 vocab=93fc06ad
-/
theorem intUnits_kummer_exact_middle (p : ℕ) :
    (powMonoidHom p : ℤˣ →* ℤˣ).range =
      (QuotientGroup.mk' (powMonoidHom p : ℤˣ →* ℤˣ).range).ker :=
  (QuotientGroup.ker_mk' _).symm

/--
@isnad1 id=surjecti.0h1v.s9.8b92cb85c5c9 from=translated src=- shape=c2daed05 vocab=8827f8bb
-/
theorem intUnits_kummer_mk'_surjective (p : ℕ) :
    Function.Surjective (QuotientGroup.mk' (powMonoidHom p : ℤˣ →* ℤˣ).range) :=
  QuotientGroup.mk'_surjective _

end ElementaryComputations

end FppfCohomologyLES

set_option autoImplicit false

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/--
@isnad1 id=eq.0h7v.s13.2b6ff740dae2 from=translated src=- shape=a3be0d62 vocab=290a7b8a
-/
theorem cohomology_naturality_f {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf J) S₁.X₁ n) :
    cohomologyMap φ.τ₂ n (cohomologyMap S₁.f n x) =
      cohomologyMap S₂.f n (cohomologyMap φ.τ₁ n x) := by
  rw [← cohomologyMap_comp, ← cohomologyMap_comp, ShortComplex.Hom.comm₁₂]

/--
@isnad1 id=eq.0h7v.s13.de0543b8ceb9 from=translated src=- shape=a3be0d62 vocab=633aa32c
-/
theorem cohomology_naturality_g {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf J) S₁.X₂ n) :
    cohomologyMap φ.τ₃ n (cohomologyMap S₁.g n x) =
      cohomologyMap S₂.g n (cohomologyMap φ.τ₂ n x) := by
  rw [← cohomologyMap_comp, ← cohomologyMap_comp, ShortComplex.Hom.comm₂₃]

/--
@isnad1 id=eq.0h6v.s12.75ed17d3198c from=translated src=- shape=dd8ec9c6 vocab=44ee6e05
-/
theorem cohomology_naturality_f_hom {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) :
    (cohomologyMap φ.τ₂ n).comp (cohomologyMap S₁.f n) =
      (cohomologyMap S₂.f n).comp (cohomologyMap φ.τ₁ n) :=
  AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.comp_apply]
    exact cohomology_naturality_f φ n x

/--
@isnad1 id=eq.0h6v.s12.0c35803272bd from=translated src=- shape=dd8ec9c6 vocab=35cad58f
-/
theorem cohomology_naturality_g_hom {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) :
    (cohomologyMap φ.τ₃ n).comp (cohomologyMap S₁.g n) =
      (cohomologyMap S₂.g n).comp (cohomologyMap φ.τ₂ n) :=
  AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.comp_apply]
    exact cohomology_naturality_g φ n x

/--
@isnad1 id=eq.3h8v.s13.2fbf1b6675e7 from=translated src=- shape=430f2a1d vocab=d8b13fde
-/
theorem cohomologyδ_naturality {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S₁.X₃ n₀) :
    cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
      cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x) := by
  simp only [cohomologyMap_apply, cohomologyδ_apply, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]
  rw [ShortComplex.ShortExact.extClass_naturality hS₁ hS₂ φ]

/--
@isnad1 id=eq.3h7v.s12.ff66b7a68e79 from=translated src=- shape=671e09e2 vocab=4b9f0458
-/
theorem cohomologyδ_naturality_hom {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyδ hS₂ n₀ n₁ h).comp (cohomologyMap φ.τ₃ n₀) =
      (cohomologyMap φ.τ₁ n₁).comp (cohomologyδ hS₁ n₀ n₁ h) :=
  AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.comp_apply]
    exact cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h x

/--
@isnad1 id=and.3h7v.s15.6fd002ff1c48 from=translated src=- shape=67828cfa vocab=16bfad8e
-/
theorem cohomologyLES_ladder {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (∀ x, cohomologyMap φ.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap φ.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap φ.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap φ.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
        cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  ⟨fun x => cohomology_naturality_f φ n₀ x, fun x => cohomology_naturality_g φ n₀ x,
    fun x => cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h x⟩

noncomputable def cohomologyMapAddEquiv {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ) :
    F.H n ≃+ G.H n where
  toFun := cohomologyMap e.hom n
  invFun := cohomologyMap e.inv n
  left_inv x := by rw [← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id]
  right_inv x := by rw [← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id]
  map_add' x y := map_add (cohomologyMap e.hom n) x y

/--
@isnad1 id=eq.0h7v.s10.0e6bcf970edf from=translated src=- shape=b78bb678 vocab=2886eb9f
-/
@[simp]
lemma cohomologyMapAddEquiv_apply {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ)
    (x : Ext (constIntSheaf J) F n) :
    cohomologyMapAddEquiv e n x = cohomologyMap e.hom n x := rfl

/--
@isnad1 id=eq.0h7v.s10.707d59880559 from=translated src=- shape=4762e4e6 vocab=2f738727
-/
@[simp]
lemma cohomologyMapAddEquiv_symm_apply {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ)
    (y : Ext (constIntSheaf J) G n) :
    (cohomologyMapAddEquiv e n).symm y = cohomologyMap e.inv n y := rfl

/--
@isnad1 id=bijectiv.0h6v.s9.617bdce36f6b from=translated src=- shape=fede2600 vocab=60280345
-/
theorem cohomologyMap_bijective_of_isIso {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsIso φ] (n : ℕ) :
    Function.Bijective (cohomologyMap φ n) := by
  constructor
  · intro x y hxy
    have h2 := congrArg (cohomologyMap (inv φ) n) hxy
    rwa [← cohomologyMap_comp, ← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id,
      cohomologyMap_id] at h2
  · intro y
    refine ⟨cohomologyMap (inv φ) n y, ?_⟩
    rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]

/--
@isnad1 id=and.3h7v.s15.385eb29f65eb from=translated src=- shape=d9639b8c vocab=6308b1f0
-/
theorem cohomologyLES_iso_compatible {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap e.hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap e.hom.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap e.hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap e.hom.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap e.hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x) =
        cohomologyMap e.hom.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  ⟨cohomologyMap_bijective_of_isIso e.hom.τ₁ n₀,
    cohomologyMap_bijective_of_isIso e.hom.τ₂ n₀,
    cohomologyMap_bijective_of_isIso e.hom.τ₃ n₀,
    fun x => cohomology_naturality_f e.hom n₀ x,
    fun x => cohomology_naturality_g e.hom n₀ x,
    fun x => cohomologyδ_naturality hS₁ hS₂ e.hom n₀ n₁ h x⟩

/--
@isnad1 id=eq.3h8v.s13.9a884ac45713 from=translated src=- shape=0e314dd8 vocab=d3a0e01d
-/
theorem cohomologyδ_conj_of_iso {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S₁.X₃ n₀) :
    cohomologyδ hS₁ n₀ n₁ h x =
      cohomologyMap e.inv.τ₁ n₁ (cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x)) := by
  rw [cohomologyδ_naturality hS₁ hS₂ e.hom n₀ n₁ h x, ← cohomologyMap_comp,
    ← ShortComplex.comp_τ₁, Iso.hom_inv_id, ShortComplex.id_τ₁, cohomologyMap_id]

/--
@isnad1 id=and.2h6v.s14.5c6bd903a62b from=translated src=- shape=6257c893 vocab=4f4b9aac
-/
theorem satGate_id_delta_naturality {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S.X₃ n₀) :
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) ∧
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyδ hS n₀ n₁ h x ∧
    cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) =
        cohomologyδ hS n₀ n₁ h x :=
  ⟨cohomologyδ_naturality hS hS (𝟙 S) n₀ n₁ h x,
    by rw [ShortComplex.id_τ₃, cohomologyMap_id],
    by rw [ShortComplex.id_τ₁, cohomologyMap_id]⟩

noncomputable def biprodSESHom (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') :
    biprodSES F G ⟶ biprodSES F G' where
  τ₁ := 𝟙 F
  τ₂ := biprod.map (𝟙 F) ψ
  τ₃ := ψ
  comm₁₂ := by simp [biprodSES]
  comm₂₃ := by simp [biprodSES]

/--
@isnad1 id=eq.0h6v.s8.3dbe3355d06e from=translated src=- shape=c3f40d8d vocab=22c8f0f1
-/
@[simp]
lemma biprodSESHom_τ₁ (F : Sheaf J AddCommGrpCat.{w}) {G G' : Sheaf J AddCommGrpCat.{w}}
    (ψ : G ⟶ G') : (biprodSESHom F ψ).τ₁ = 𝟙 F := rfl

/--
@isnad1 id=eq.0h6v.s8.7580d012a734 from=translated src=- shape=6f28b14a vocab=ef87e3a1
-/
@[simp]
lemma biprodSESHom_τ₃ (F : Sheaf J AddCommGrpCat.{w}) {G G' : Sheaf J AddCommGrpCat.{w}}
    (ψ : G ⟶ G') : (biprodSESHom F ψ).τ₃ = ψ := rfl

/--
@isnad1 id=eq.1h9v.s13.2ac38671acd7 from=translated src=- shape=01bf9ba6 vocab=619336ba
-/
theorem satGate_biprodSESHom_delta_naturality (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G') n₀ n₁ h
        (cohomologyMap (biprodSESHom F ψ).τ₃ n₀ x) =
      cohomologyMap (biprodSESHom F ψ).τ₁ n₁
        (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x) :=
  cohomologyδ_naturality (biprodSES_shortExact F G) (biprodSES_shortExact F G')
    (biprodSESHom F ψ) n₀ n₁ h x

/--
@isnad1 id=and.1h9v.s13.0f48c2be86ab from=translated src=- shape=77d50493 vocab=619336ba
-/
theorem satGate_biprodSESHom_delta_zero_consistency (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G') n₀ n₁ h
        (cohomologyMap (biprodSESHom F ψ).τ₃ n₀ x) = 0 ∧
    cohomologyMap (biprodSESHom F ψ).τ₁ n₁
        (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x) = 0 :=
  ⟨biprodSES_delta_apply_eq_zero F G' n₀ n₁ h _,
    by rw [biprodSES_delta_apply_eq_zero F G n₀ n₁ h x, map_zero]⟩

noncomputable def biprodSESSwap (F G : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (biprod.inr : F ⟶ G ⊞ F) (biprod.fst : G ⊞ F ⟶ G) (by simp)

noncomputable def biprodSESSwapIso (F G : Sheaf J AddCommGrpCat.{w}) :
    biprodSES F G ≅ biprodSESSwap F G :=
  ShortComplex.isoMk (Iso.refl F) (biprod.braiding F G) (Iso.refl G)
    (by
      dsimp [biprodSES, biprodSESSwap]
      apply biprod.hom_ext <;> simp)
    (by
      dsimp [biprodSES, biprodSESSwap]
      simp)

/--
@isnad1 id=shortexa.0h4v.s7.6b60f8b592f6 from=translated src=- shape=ca8317cb vocab=9e6bc37a
-/
theorem biprodSESSwap_shortExact (F G : Sheaf J AddCommGrpCat.{w}) :
    (biprodSESSwap F G).ShortExact :=
  ShortComplex.shortExact_of_iso (biprodSESSwapIso F G) (biprodSES_shortExact F G)

/--
@isnad1 id=and.1h6v.s15.57ef1b61d034 from=translated src=- shape=b536da69 vocab=46557196
-/
theorem satGate_swapIso_les_compatible (F G : Sheaf J AddCommGrpCat.{w}) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀
            (cohomologyMap (biprodSES F G).f n₀ x) =
        cohomologyMap (biprodSESSwap F G).f n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀
            (cohomologyMap (biprodSES F G).g n₀ x) =
        cohomologyMap (biprodSESSwap F G).g n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ (biprodSESSwap_shortExact F G) n₀ n₁ h
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀ x) =
        cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₁
            (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x)) :=
  cohomologyLES_iso_compatible (biprodSES_shortExact F G) (biprodSESSwap_shortExact F G)
    (biprodSESSwapIso F G) n₀ n₁ h

end GenericSite

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

/--
@isnad1 id=eq.0h5v.s13.101e8a7cc20e from=translated src=- shape=4310d0a8 vocab=49fc74af
-/
theorem fppf_naturality_f {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₁ n) :
    cohomologyMap φ.τ₂ n (cohomologyMap S₁.f n x) =
      cohomologyMap S₂.f n (cohomologyMap φ.τ₁ n x) :=
  cohomology_naturality_f φ n x

/--
@isnad1 id=eq.0h5v.s13.53c3d8119b27 from=translated src=- shape=4310d0a8 vocab=5fa88500
-/
theorem fppf_naturality_g {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₂ n) :
    cohomologyMap φ.τ₃ n (cohomologyMap S₁.g n x) =
      cohomologyMap S₂.g n (cohomologyMap φ.τ₂ n x) :=
  cohomology_naturality_g φ n x

/--
@isnad1 id=eq.3h6v.s13.c268024f843b from=translated src=- shape=918c09a8 vocab=53b6c9a0
-/
theorem fppf_delta_naturality {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₃ n₀) :
    cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
      cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x) :=
  cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h x

/--
@isnad1 id=eq.3h5v.s12.6eab84c4c2f7 from=translated src=- shape=a7dd5935 vocab=089eb44d
-/
theorem fppf_delta_naturality_hom
    {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyδ hS₂ n₀ n₁ h).comp (cohomologyMap φ.τ₃ n₀) =
      (cohomologyMap φ.τ₁ n₁).comp (cohomologyδ hS₁ n₀ n₁ h) :=
  cohomologyδ_naturality_hom hS₁ hS₂ φ n₀ n₁ h

/--
@isnad1 id=and.3h5v.s15.dc008109b7da from=translated src=- shape=a17604c0 vocab=8ed320f4
-/
theorem fppf_les_ladder {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (∀ x, cohomologyMap φ.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap φ.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap φ.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap φ.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
        cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  cohomologyLES_ladder hS₁ hS₂ φ n₀ n₁ h

/--
@isnad1 id=and.3h5v.s15.d6eb76a0be32 from=translated src=- shape=6ab6bb88 vocab=755f6176
-/
theorem fppf_les_iso_compatible
    {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap e.hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap e.hom.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap e.hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap e.hom.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap e.hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x) =
        cohomologyMap e.hom.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  cohomologyLES_iso_compatible hS₁ hS₂ e n₀ n₁ h

/--
@isnad1 id=eq.3h6v.s13.cd0d5a4d0b5c from=translated src=- shape=c86ffa01 vocab=fce4ab70
-/
theorem fppf_delta_conj_of_iso
    {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₃ n₀) :
    cohomologyδ hS₁ n₀ n₁ h x =
      cohomologyMap e.inv.τ₁ n₁ (cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x)) :=
  cohomologyδ_conj_of_iso hS₁ hS₂ e n₀ n₁ h x

/--
@isnad1 id=eq.1h7v.s13.61c80633d107 from=translated src=- shape=84d11831 vocab=21ba509b
-/
theorem fppf_satGate_biprodSESHom_delta_naturality
    (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    {G G' : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (ψ : G ⟶ G') (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G') n₀ n₁ h
        (cohomologyMap (biprodSESHom F ψ).τ₃ n₀ x) =
      cohomologyMap (biprodSESHom F ψ).τ₁ n₁
        (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x) :=
  satGate_biprodSESHom_delta_naturality F ψ n₀ n₁ h x

/--
@isnad1 id=and.2h4v.s14.8b938a4dad45 from=translated src=- shape=3663e070 vocab=504fad2c
-/
theorem fppf_satGate_id_delta_naturality
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S.X₃ n₀) :
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) ∧
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyδ hS n₀ n₁ h x ∧
    cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) =
        cohomologyδ hS n₀ n₁ h x :=
  satGate_id_delta_naturality hS n₀ n₁ h x

/--
@isnad1 id=and.1h4v.s15.0971b21e3fe4 from=translated src=- shape=48dab4d2 vocab=be094334
-/
theorem fppf_satGate_swapIso_les_compatible (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀
            (cohomologyMap (biprodSES F G).f n₀ x) =
        cohomologyMap (biprodSESSwap F G).f n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀
            (cohomologyMap (biprodSES F G).g n₀ x) =
        cohomologyMap (biprodSESSwap F G).g n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ (biprodSESSwap_shortExact F G) n₀ n₁ h
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀ x) =
        cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₁
            (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x)) :=
  satGate_swapIso_les_compatible F G n₀ n₁ h

end WithLocalInstances

end FppfSite

end FppfCohomologyLES
