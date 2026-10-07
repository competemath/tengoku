/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact
public import Tengoku.Seed.AlgebraicGeometry.Properties
public import Tengoku.Seed.Tactic.DepRewrite

/-!
# Ideal sheaves on schemes

We define ideal sheaves of schemes and provide various constructors for it.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData`: A structure that contains the data to uniquely define
  an ideal sheaf, consisting of
  1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
  2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`:
  The largest ideal sheaf contained in a family of ideals.
* `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`:
  Over affine schemes, ideal sheaves are in bijection with ideals of the global sections.
* `AlgebraicGeometry.Scheme.IdealSheafData.support`: The support of an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`: The vanishing ideal of a set.
* `AlgebraicGeometry.Scheme.Hom.ker`: The kernel of a morphism.

## Main results
* `AlgebraicGeometry.Scheme.IdealSheafData.gc`:
  `support` and `vanishingIdeal` forms a Galois connection.
* `AlgebraicGeometry.Scheme.Hom.support_ker`: The support of a kernel of a quasi-compact morphism
  is the closure of the range.

## Implementation detail

Ideal sheaves are not yet defined in this file as actual subsheaves of `𝒪ₓ`.
Instead, for the ease of development and application,
we define the structure `IdealSheafData` containing all necessary data to uniquely define an
ideal sheaf. This should be refactored as a constructor for ideal sheaves once they are introduced
into mathlib.

-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/--
A structure that contains the data to uniquely define an ideal sheaf, consisting of
1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`
3. a subset of `X` equal to the support.

Also see `Scheme.IdealSheafData.mkOfMemSupportIff` for a constructor with the condition on the
support being (usually) easier to prove.
-/
structure IdealSheafData (X : Scheme.{u}) : Type u where
  /-- The component of an ideal sheaf at an affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal Γ(X, U)
  /-- Also see `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` -/
  map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
    (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
      ideal (X.affineBasicOpen f)
  /-- The support of an ideal sheaf. Use `IdealSheafData.support` instead for most occasions. -/
  supportSet : Set X := ⋂ U, X.zeroLocus (U := U.1) (ideal U)
  supportSet_eq_iInter_zeroLocus : supportSet = ⋂ U, X.zeroLocus (U := U.1) (ideal U) := by rfl

namespace IdealSheafData

/--
@isnad1 id=eq.1h3v.s9.fab690e9752d from=seed src=0 shape=bf8d872e vocab=9753c29f
-/
@[ext]
protected lemma ext {I J : X.IdealSheafData} (h : I.ideal = J.ideal) : I = J := by
  obtain ⟨i, _, s, hs⟩ := I
  obtain ⟨j, _, t, ht⟩ := J
  subst h
  congr
  rw [hs, ht]

section Order

instance : PartialOrder (IdealSheafData X) := PartialOrder.lift ideal fun _ _ ↦ IdealSheafData.ext

/--
@isnad1 id=iff.0h3v.s11.9a85476860fb from=seed src=0 shape=d1bae131 vocab=ae26b0f3
-/
lemma le_def {I J : IdealSheafData X} : I ≤ J ↔ ∀ U, I.ideal U ≤ J.ideal U := .rfl

set_option backward.isDefEq.respectTransparency false in
instance : CompleteSemilatticeSup (IdealSheafData X) where
  sSup s :=
  { ideal := sSup (ideal '' s),
    map_ideal_basicOpen := by
      have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
        conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
        rfl
      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
  isLUB_sSup _ := .of_image (f := ideal) le_def (isLUB_sSup _)

/-- The largest ideal sheaf contained in a family of ideals. -/
def ofIdeals (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) : IdealSheafData X :=
  sSup { J : IdealSheafData X | J.ideal ≤ I }

/--
@isnad1 id=le.0h2v.s12.58ed5d4aa373 from=seed src=0 shape=14e51464 vocab=0d258c71
-/
lemma ideal_ofIdeals_le (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) :
    (ofIdeals I).ideal ≤ I :=
  sSup_le (Set.forall_mem_image.mpr fun _ ↦ id)

/-- The Galois coinsertion between ideal sheaves and arbitrary families of ideals. -/
protected def gci : GaloisCoinsertion ideal (ofIdeals (X := X)) where
  choice I hI :=
  { ideal := I
    map_ideal_basicOpen U f :=
      (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f }
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ ↦ id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))

/--
@isnad1 id=strictmo.0h1v.s11.11feb99213aa from=seed src=0 shape=f995a6f6 vocab=7a973858
-/
lemma strictMono_ideal : StrictMono (ideal (X := X)) := IdealSheafData.gci.strictMono_l
/--
@isnad1 id=monotone.0h1v.s11.e62f0ac39ebf from=seed src=0 shape=f995a6f6 vocab=e24de54a
-/
lemma ideal_mono : Monotone (ideal (X := X)) := strictMono_ideal.monotone
/--
@isnad1 id=monotone.0h1v.s11.8bfff06ee45e from=seed src=0 shape=4396a224 vocab=34cd976e
-/
lemma ofIdeals_mono : Monotone (ofIdeals (X := X)) := IdealSheafData.gci.gc.monotone_u
/--
@isnad1 id=eq.0h2v.s3.3fe30da8d5fe from=seed src=0 shape=6ddf6d3e vocab=3d404957
-/
lemma ofIdeals_ideal (I : IdealSheafData X) : ofIdeals I.ideal = I := IdealSheafData.gci.u_l_eq _
/--
@isnad1 id=iff.0h3v.s12.253543dface4 from=seed src=0 shape=1df5626d vocab=b671d76c
-/
lemma le_ofIdeals_iff {I : IdealSheafData X} {J} : I ≤ ofIdeals J ↔ I.ideal ≤ J :=
  IdealSheafData.gci.gc.le_iff_le.symm

set_option backward.isDefEq.respectTransparency false in
instance : OrderTop (IdealSheafData X) where
  top.ideal := ⊤
  top.map_ideal_basicOpen := by simp [Ideal.map_top]
  top.supportSet := ⊥
  top.supportSet_eq_iInter_zeroLocus := by
    ext x
    simpa using X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  le_top I U := le_top

set_option backward.isDefEq.respectTransparency false in
instance : OrderBot (IdealSheafData X) where
  bot.ideal := ⊥
  bot.map_ideal_basicOpen := by simp
  bot.supportSet := ⊤
  bot.supportSet_eq_iInter_zeroLocus := by ext; simp
  bot_le I U := bot_le

set_option backward.isDefEq.respectTransparency false in
instance : SemilatticeInf (IdealSheafData X) where
  inf I J :=
  { ideal := I.ideal ⊓ J.ideal
    map_ideal_basicOpen U f := by
      dsimp
      have : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap _ _ := rfl
      have inst := U.2.isLocalization_basicOpen f
      rw [← I.map_ideal_basicOpen U f, ← J.map_ideal_basicOpen U f, this]
      ext x
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
      simp only [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff, Ideal.mem_inf,
        exists_exists_eq_and]
      refine ⟨fun ⟨n, h₁, h₂⟩ ↦ ⟨⟨n, h₁⟩, ⟨n, h₂⟩⟩, ?_⟩
      rintro ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
      refine ⟨n₁ + n₂, ?_, ?_⟩
      · rw [add_comm, pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₁
      · rw [pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₂ }
  inf_le_left I J U := inf_le_left
  inf_le_right I J U := inf_le_right
  le_inf I J K hIJ hIK U := le_inf (hIJ U) (hIK U)

instance : CompleteLattice (IdealSheafData X) where
  __ := (inferInstance : OrderTop (IdealSheafData X))
  __ := (inferInstance : OrderBot (IdealSheafData X))
  __ := (inferInstance : SemilatticeInf (IdealSheafData X))
  __ := (inferInstance : CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

/--
@isnad1 id=eq.0h1v.s11.3659f3b3aaf1 from=seed src=0 shape=2b70b724 vocab=572a134f
-/
@[simp]
lemma ideal_top : ideal (X := X) ⊤ = ⊤ := rfl

/--
@isnad1 id=eq.0h1v.s11.5d8e627f53ba from=seed src=0 shape=2b70b724 vocab=9f3320fb
-/
@[simp]
lemma ideal_bot : ideal (X := X) ⊥ = ⊥ := rfl

/--
@isnad1 id=eq.0h3v.s12.c3b5eeaf4c92 from=seed src=0 shape=f9676240 vocab=d152201b
-/
@[simp]
lemma ideal_sup {I J : IdealSheafData X} : (I ⊔ J).ideal = I.ideal ⊔ J.ideal := rfl

/--
@isnad1 id=eq.0h2v.s12.86424a4c5690 from=seed src=0 shape=281af2bc vocab=7468d7cc
-/
@[simp]
lemma ideal_sSup {I : Set (IdealSheafData X)} : (sSup I).ideal = sSup (ideal '' I) := rfl

/--
@isnad1 id=eq.0h3v.s12.7d5f6533adf8 from=seed src=0 shape=33c6a141 vocab=9ff464f1
-/
@[simp]
lemma ideal_iSup {ι : Type*} {I : ι → IdealSheafData X} : (iSup I).ideal = ⨆ i, (I i).ideal := by
  rw [← sSup_range, ← sSup_range, ideal_sSup, ← Set.range_comp, Function.comp_def]

/--
@isnad1 id=eq.0h3v.s11.7e94a4461645 from=seed src=0 shape=f9676240 vocab=e8e1142c
-/
@[simp]
lemma ideal_inf {I J : IdealSheafData X} : (I ⊓ J).ideal = I.ideal ⊓ J.ideal := rfl

/--
@isnad1 id=eq.1h4v.s12.eced527a4041 from=seed src=0 shape=0dd49ba0 vocab=5bcd2cbf
-/
@[simp]
lemma ideal_biInf {ι : Type*} (I : ι → IdealSheafData X) {s : Set ι} (hs : s.Finite) :
    (⨅ i ∈ s, I i).ideal = ⨅ i ∈ s, (I i).ideal := by
  refine hs.induction_on _ (by simp) fun {i s} his hs e ↦ ?_
  simp only [iInf_insert, e, ideal_inf]

/--
@isnad1 id=eq.0h3v.s11.df84a390603b from=seed src=0 shape=b10a23a8 vocab=90dba60e
-/
@[simp]
lemma ideal_iInf {ι : Type*} (I : ι → IdealSheafData X) [Finite ι] :
    (⨅ i, I i).ideal = ⨅ i, (I i).ideal := by
  simpa using ideal_biInf I Set.finite_univ

end Order

variable (I : IdealSheafData X)

section map_ideal

/-- subsumed by `IdealSheafData.map_ideal` below. -/
private lemma map_ideal_basicOpen_of_eq
    {U V : X.affineOpens} (f : Γ(X, U)) (hV : V = X.affineBasicOpen f) :
    (I.ideal U).map (X.presheaf.map
        (homOfLE (X := X.Opens) (hV.trans_le (X.affineBasicOpen_le f))).op).hom =
      I.ideal V := by
  subst hV; exact I.map_ideal_basicOpen _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h4v.s12.59168637f884 from=seed src=0 shape=365a82c8 vocab=f99cd8f6
-/
lemma map_ideal {U V : X.affineOpens} (h : U ≤ V) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = I.ideal U := by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, h hxU⟩
  have := I.map_ideal_basicOpen_of_eq (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
  rw [← I.map_ideal_basicOpen] at this
  apply_fun Ideal.map (X.presheaf.germ (X.basicOpen g) x (hfg ▸ hxf)).hom at this
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, affineBasicOpen_coe, X.presheaf.germ_res]
    at this ⊢
  simp only [homOfLE_leOfHom, TopCat.Presheaf.germ_res', this]

/-- A form of `map_ideal` that is easier to rewrite with.
@isnad1 id=eq.0h5v.s12.e956f0730178 from=seed src=0 shape=ef0938b8 vocab=eaaa3371
-/
lemma map_ideal' {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) :
    (I.ideal V).map (X.presheaf.map h).hom = I.ideal U :=
  map_ideal _ _

/--
@isnad1 id=le.1h4v.s13.5be00a353158 from=seed src=0 shape=5d4b27b7 vocab=d0a16bcc
-/
lemma ideal_le_comap_ideal {U V : X.affineOpens} (h : U ≤ V) :
    I.ideal V ≤ (I.ideal U).comap (X.presheaf.map (homOfLE h).op).hom := by
  rw [← Ideal.map_le_iff_le_comap, ← I.map_ideal h]

/--
@isnad1 id=le.2h5v.s11.82cd0f6f3f8f from=seed src=0 shape=6479ad6c vocab=151af4ec
-/
lemma le_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (H : ∀ i, I.ideal (U i) ≤ J.ideal (U i)) :
    I ≤ J := by
  intro V
  have : ∀ x : V.1, ∃ (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 ∈ X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter V.2 (U i).2 _ ⟨hxV, hi⟩⟩
  choose i r rU e hxr using this
  have : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.le_of_isLocalized_span _ this (fun i ↦ Γ(X, X.basicOpen i.1))
    (fun i ↦ Algebra.linearMap Γ(X, V.1) Γ(X, X.basicOpen i.1)) ?_
  rintro ⟨_, j, rfl⟩
  simp only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (r j)),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  erw [I.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j)),
    J.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j))]
  delta algebra_section_section_basicOpen
  rw! [e]
  rw [← I.map_ideal (V := (U _)) (X.basicOpen_le _), ← J.map_ideal (V := (U _)) (X.basicOpen_le _)]
  exact Ideal.map_mono (f := (X.presheaf.map (homOfLE (X.basicOpen_le (rU j))).op).hom) (H (i j))

/--
@isnad1 id=eq.2h5v.s9.98657fbbb51d from=seed src=0 shape=31c4cad9 vocab=8981afb7
-/
lemma ext_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (H : ∀ i, I.ideal (U i) = J.ideal (U i)) :
    I = J :=
  (le_of_iSup_eq_top U hU (by aesop)).antisymm (le_of_iSup_eq_top U hU (by aesop))

end map_ideal

section support

/--
@isnad1 id=iff.0h3v.s11.ebb0132fcd4d from=seed src=0 shape=5021c302 vocab=47b1ff10
-/
lemma mem_supportSet_iff {I : IdealSheafData X} {x} :
    x ∈ I.supportSet ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

/--
@isnad1 id=le.0h3v.s11.a39d4d4c54df from=seed src=0 shape=15e6a599 vocab=2492bc83
-/
lemma supportSet_subset_zeroLocus (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet ⊆ X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus.trans_subset (Set.iInter_subset _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=le.0h3v.s11.e8d9478d082d from=seed src=0 shape=d4bf24d6 vocab=8b68ac7c
-/
lemma zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpens) :
    X.zeroLocus (U := U.1) (I.ideal U) ∩ U ⊆ I.supportSet := by
  rw [I.supportSet_eq_iInter_zeroLocus]
  refine Set.subset_iInter fun V ↦ ?_
  apply (X.codisjoint_zeroLocus (U := V) (I.ideal V)).symm.left_le_of_le_inf_right
  rintro x ⟨⟨hx, hxU⟩, hxV⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx ⊢
  intro s hfU hxs
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have inst := U.2.isLocalization_basicOpen f
  have := (I.map_ideal (U := X.affineBasicOpen f) (hfg.trans_le (X.basicOpen_le g))).le
    (Ideal.mem_map_of_mem _ hfU)
  rw [← I.map_ideal_basicOpen] at this
  obtain ⟨⟨s', ⟨_, n, rfl⟩⟩, hs'⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (.powers f) Γ(X, X.basicOpen f)).mp this
  apply_fun (x ∈ X.basicOpen ·) at hs'
  refine hx s' s'.2 ?_
  cases n <;>
    simpa [RingHom.algebraMap_toAlgebra, ← hfg, hxf, hxs, Scheme.basicOpen_pow] using hs'

/--
@isnad1 id=iff.1h4v.s11.d01c508a4201 from=seed src=0 shape=240ce429 vocab=47b1ff10
-/
lemma mem_supportSet_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x ∈ U.1) :
    x ∈ I.supportSet ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  ⟨I.supportSet_eq_iInter_zeroLocus ▸ fun h ↦ Set.iInter_subset _ U h,
    fun h ↦ I.zeroLocus_inter_subset_supportSet U ⟨h, hxU⟩⟩

/--
@isnad1 id=eq.0h3v.s11.e52ba4a2a949 from=seed src=0 shape=7e11a908 vocab=df8981b6
-/
lemma supportSet_inter (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U := by
  ext x
  by_cases hxU : x ∈ U.1
  · simp [hxU, mem_supportSet_iff_of_mem hxU]
  · simp [hxU]

/--
@isnad1 id=isclosed.0h2v.s4.ec6a49e0fcb2 from=seed src=0 shape=99c5ebf9 vocab=b896c05b
-/
lemma isClosed_supportSet (I : IdealSheafData X) : IsClosed I.supportSet := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set.image_preimage_eq_inter_range, I.supportSet_inter]

/-- The support of an ideal sheaf. Also see `IdealSheafData.mem_support_iff_of_mem`. -/
def support : Closeds X := ⟨I.supportSet, I.isClosed_supportSet⟩

/--
@isnad1 id=eq.0h2v.s11.6620af888956 from=seed src=0 shape=08443182 vocab=8ff570de
-/
lemma coe_support_eq_eq_iInter_zeroLocus :
    (I.support : Set X) = ⋂ U, X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus

/--
@isnad1 id=iff.0h3v.s7.ccb0144b00e6 from=seed src=0 shape=afc5e13e vocab=c0194dda
-/
@[simp] lemma mem_supportSet_iff_mem_support {I : IdealSheafData X} {x} :
    x ∈ I.supportSet ↔ x ∈ I.support := .rfl

/--
@isnad1 id=iff.0h3v.s11.5bdccaf2a3c6 from=seed src=0 shape=c6bd4f43 vocab=3d246f7f
-/
lemma mem_support_iff {I : IdealSheafData X} {x} :
    x ∈ I.support ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

/--
@isnad1 id=iff.1h4v.s11.31dfd69f3b31 from=seed src=0 shape=5ee06611 vocab=3d246f7f
-/
lemma mem_support_iff_of_mem {I : IdealSheafData X} {x : X} {U : X.affineOpens} (h : x ∈ U.1) :
    x ∈ I.support ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) := by
  simpa [-mem_zeroLocus_iff, h] using congr(x ∈ $(I.supportSet_inter U))

/--
@isnad1 id=eq.0h3v.s11.d53d029470da from=seed src=0 shape=5a037466 vocab=3d910a12
-/
lemma coe_support_inter (I : IdealSheafData X) (U : X.affineOpens) :
    (I.support : Set X) ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U :=
  I.supportSet_inter U

/-- Custom simps projection for `IdealSheafData`. -/
def Simps.coe_support : Set X := I.support

initialize_simps_projections IdealSheafData (supportSet → coe_support, as_prefix coe_support)

/-- A useful constructor of `IdealSheafData`
with the condition on `supportSet` being easier to check. -/
@[simps ideal coe_support]
def mkOfMemSupportIff
    (ideal : ∀ U : X.affineOpens, Ideal Γ(X, U))
    (map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
      (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
        ideal (X.affineBasicOpen f))
    (supportSet : Set X)
    (supportSet_inter :
      ∀ U : X.affineOpens, ∀ x ∈ U.1, x ∈ supportSet ↔ x ∈ X.zeroLocus (U := U.1) (ideal U)) :
    X.IdealSheafData where
  ideal := ideal
  map_ideal_basicOpen := map_ideal_basicOpen
  supportSet := supportSet
  supportSet_eq_iInter_zeroLocus := by
    let I' : X.IdealSheafData := { ideal := ideal, map_ideal_basicOpen := map_ideal_basicOpen }
    change supportSet = I'.supportSet
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (supportSet_inter ⟨U, hU⟩ x hxU).trans
      (I'.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).symm

/--
@isnad1 id=eq.0h1v.s8.e45eeaedc89a from=seed src=0 shape=949873c3 vocab=feb65908
-/
@[simp]
lemma support_top : support (X := X) ⊤ = ⊥ := rfl

/--
@isnad1 id=eq.0h1v.s8.43d7cc8987d3 from=seed src=0 shape=949873c3 vocab=feb65908
-/
@[simp]
lemma support_bot : support (X := X) ⊥ = ⊤ := rfl

/--
@isnad1 id=antitone.0h1v.s6.ceed46289261 from=seed src=0 shape=0e8d42a7 vocab=df2a0cad
-/
lemma support_antitone : Antitone (support (X := X)) := by
  intro I J h
  rw [← SetLike.coe_subset_coe, I.coe_support_eq_eq_iInter_zeroLocus,
    J.coe_support_eq_eq_iInter_zeroLocus]
  exact Set.iInter_mono fun U ↦ X.zeroLocus_mono (h U)

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iff.0h2v.s8.c272473c8e00 from=seed src=0 shape=59595d08 vocab=feb65908
-/
@[simp]
lemma support_eq_bot_iff : support I = ⊥ ↔ I = ⊤ := by
  refine ⟨fun H ↦ top_le_iff.mp fun U ↦ ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_supportSet I U).trans H.le)
  simp only [Set.subset_empty_iff, Set.image_eq_empty, Closeds.coe_bot] at this
  simp [PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp this]

end support

section Semiring

variable (I J K : X.IdealSheafData)

instance : Zero X.IdealSheafData where zero := ⊥
instance : One X.IdealSheafData where one := ⊤
instance : Add X.IdealSheafData where add := (· ⊔ ·)

set_option backward.isDefEq.respectTransparency false in
instance : Mul X.IdealSheafData where
  mul I J := mkOfMemSupportIff (I.ideal * J.ideal) (by simp [Ideal.map_mul, map_ideal_basicOpen])
    (I.supportSet ∪ J.supportSet) fun U x hxU ↦ by
    simp [-mem_zeroLocus_iff, zeroLocus_mul, mem_support_iff_of_mem hxU]

set_option backward.isDefEq.respectTransparency false in
instance : Pow X.IdealSheafData ℕ where
  pow I n := mkOfMemSupportIff (I.ideal ^ n) (by simp [Ideal.map_pow, map_ideal_basicOpen])
    (if n = 0 then ∅ else I.supportSet) fun U x hxU ↦ .symm <| by
    induction n <;> simp_all [-mem_zeroLocus_iff, zeroLocus_mul,
      pow_succ, mem_support_iff_of_mem hxU]

/--
@isnad1 id=eq.0h3v.s12.cd8e9f4cab7f from=seed src=0 shape=06790657 vocab=a639f6c3
-/
@[simp] lemma ideal_mul : (I * J).ideal = I.ideal * J.ideal := rfl
/--
@isnad1 id=eq.0h3v.s7.d004ffd2e094 from=seed src=0 shape=9f6f44c9 vocab=e641dd6a
-/
@[simp] lemma support_mul : (I * J).support = I.support ⊔ J.support := rfl
/--
@isnad1 id=eq.0h3v.s12.321a61eaa1ec from=seed src=0 shape=41ac084b vocab=a2b7df87
-/
@[simp] lemma ideal_pow (n : ℕ) : (I ^ n).ideal = I.ideal ^ n := rfl
/--
@isnad1 id=eq.0h3v.s5.a61f959bd573 from=seed src=0 shape=6f787840 vocab=d471a49e
-/
@[simp] lemma support_pow_succ (n : ℕ) : (I ^ (n + 1)).support = I.support := rfl
/--
@isnad1 id=eq.1h3v.s5.924376e807de from=seed src=0 shape=ddf51622 vocab=b4838386
-/
lemma support_pow (n : ℕ) (hn : n ≠ 0) : (I ^ n).support = I.support := by cases n <;> simp_all

/--
@isnad1 id=eq.0h2v.s5.c75910d4f675 from=seed src=0 shape=5e521b2d vocab=43a6e3ee
-/
@[simp] lemma top_mul : ⊤ * I = I := by ext; simp
/--
@isnad1 id=eq.0h2v.s5.f19072591fb0 from=seed src=0 shape=0bf5281b vocab=43a6e3ee
-/
@[simp] lemma mul_top : I * ⊤ = I := by ext; simp
/--
@isnad1 id=eq.0h2v.s5.ba87d1d2fc03 from=seed src=0 shape=14f4d8e9 vocab=0f240551
-/
@[simp] lemma bot_mul : ⊥ * I = ⊥ := by ext; simp
/--
@isnad1 id=eq.0h2v.s5.d9919e910974 from=seed src=0 shape=f7b068b3 vocab=0f240551
-/
@[simp] lemma mul_bot : I * ⊥ = ⊥ := by ext; simp
/--
@isnad1 id=eq.0h4v.s6.87bec0a7da91 from=seed src=0 shape=2c482265 vocab=eec73903
-/
lemma mul_inf : I * (J ⊔ K) = I * J ⊔ I * K := by ext U : 2; exact mul_add _ _ _
/--
@isnad1 id=eq.0h4v.s6.74afa7bc7c8c from=seed src=0 shape=63791b0b vocab=eec73903
-/
lemma inf_mul : (I ⊔ J) * K = I * K ⊔ J * K := by ext U : 2; exact add_mul _ _ _

instance : IdemCommSemiring X.IdealSheafData where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc _ _ _ := IdealSheafData.ext (mul_assoc _ _ _)
  mul_comm _ _ := IdealSheafData.ext (mul_comm _ _)
  zero_mul := bot_mul
  mul_zero := mul_bot
  one_mul := top_mul
  mul_one := mul_top
  nsmul := nsmulRec
  left_distrib := mul_inf
  right_distrib := inf_mul
  npow n I := I ^ n
  npow_zero _ := by ext; simp [show (1 : X.IdealSheafData) = ⊤ from rfl]
  npow_succ _ _ := by ext; rfl

instance : IsOrderedRing X.IdealSheafData where

/-! We follow `Ideal` and set the simp normal form to be `⊥` and `⊤` and `⊔`. -/
/--
@isnad1 id=eq.0h1v.s4.725f95cb9631 from=seed src=0 shape=73d73524 vocab=03cc7dc6
-/
@[simp] lemma zero_eq_bot : (0 : X.IdealSheafData) = ⊥ := rfl
/--
@isnad1 id=eq.0h1v.s4.c3370daec1af from=seed src=0 shape=73d73524 vocab=20ec0b91
-/
@[simp] lemma one_eq_top : (1 : X.IdealSheafData) = ⊤ := rfl
/--
@isnad1 id=eq.0h3v.s5.d142d4be20ca from=seed src=0 shape=5279f093 vocab=94fd8dc1
-/
@[simp] lemma add_eq_sup : I + J = I ⊔ J := rfl

end Semiring

section IsAffine

/-- The ideal sheaf induced by an ideal of the global sections. -/
@[simps! ideal coe_support]
def ofIdealTop (I : Ideal Γ(X, ⊤)) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ I.map (X.presheaf.map (homOfLE le_top).op).hom)
    (fun U f ↦ by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (X.zeroLocus (U := ⊤) I)
    (fun U x hxU ↦ by
      simp only [Ideal.map, zeroLocus_span, zeroLocus_map, Set.mem_union, Set.mem_compl_iff,
        SetLike.mem_coe, hxU, not_true_eq_false, iff_self_or, IsEmpty.forall_iff])

/--
@isnad1 id=le.1h3v.s12.bbf716d6c1cd from=seed src=0 shape=4bb1d635 vocab=c7a6d033
-/
lemma le_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ ≤ J.ideal ⟨⊤, isAffineOpen_top X⟩) : I ≤ J := by
  intro U
  rw [← map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) I (le_top (a := U.1)),
    ← map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) J (le_top (a := U.1))]
  exact Ideal.map_mono H

/--
@isnad1 id=eq.1h3v.s10.ece18444c322 from=seed src=0 shape=4bb1d635 vocab=7c480f25
-/
lemma ext_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  (le_of_isAffine H.le).antisymm (le_of_isAffine H.ge)

/-- Over affine schemes, ideal sheaves are in bijection with ideals of the global sections. -/
def equivOfIsAffine [IsAffine X] : IdealSheafData X ≃+*o Ideal Γ(X, ⊤) where
  toFun := (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp
  map_mul' := by simp
  map_add' := by simp
  map_le_map_iff' := ⟨le_of_isAffine, (· _)⟩

/--
@isnad1 id=eq.0h2v.s15.8d52ac89d871 from=seed src=0 shape=1f503d21 vocab=cb5670a9
-/
@[simp]
lemma equivOfIsAffine_apply [IsAffine X] (I : IdealSheafData X) :
    equivOfIsAffine I = I.ideal ⟨⊤, isAffineOpen_top X⟩ := rfl

/--
@isnad1 id=eq.0h2v.s15.7f82179a8ba5 from=seed src=0 shape=bd01df34 vocab=70817572
-/
@[simp]
lemma equivOfIsAffine_symm_apply [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    equivOfIsAffine.symm I = ofIdealTop I := rfl

end IsAffine

section ofIsClosed

open _root_.PrimeSpectrum TopologicalSpace

/-- The radical of an ideal sheaf. -/
@[simps! ideal]
def radical (I : IdealSheafData X) : IdealSheafData X :=
  mkOfMemSupportIff
  (fun U ↦ (I.ideal U).radical)
  (fun U f ↦
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLocalization.map_radical (.powers f) Γ(X, X.basicOpen f) (I.ideal U)).trans
      congr($(I.map_ideal_basicOpen U f).radical))
  I.supportSet
  (fun U x hx ↦ by
    simp only [mem_supportSet_iff_of_mem hx, AlgebraicGeometry.Scheme.zeroLocus_radical])

/--
@isnad1 id=eq.0h2v.s4.ca15ab8e1b97 from=seed src=0 shape=0153dc7c vocab=85b4d0fb
-/
@[simp]
lemma support_radical (I : IdealSheafData X) : I.radical.support = I.support := rfl

/-- The nilradical of a scheme. -/
def _root_.AlgebraicGeometry.Scheme.nilradical (X : Scheme.{u}) : IdealSheafData X :=
  .radical ⊥

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.support_nilradical (X : Scheme.{u}) :
    X.nilradical.support = ⊤ := rfl

/--
@isnad1 id=le.0h2v.s4.e88225b58799 from=seed src=0 shape=c0b2db31 vocab=0cd5c65d
-/
lemma le_radical : I ≤ I.radical := fun _ ↦ Ideal.le_radical

/--
@isnad1 id=eq.0h1v.s5.36e51b19909e from=seed src=0 shape=7437c357 vocab=9ede77c4
-/
@[simp]
lemma radical_top : radical (X := X) ⊤ = ⊤ := top_le_iff.mp (le_radical _)

/--
@isnad1 id=eq.0h1v.s4.16f8e1dfa632 from=seed src=0 shape=8db5b4ae vocab=485c053d
-/
lemma radical_bot : radical ⊥ = nilradical X := rfl

/--
@isnad1 id=eq.0h3v.s5.41aedbf6562a from=seed src=0 shape=83dde6e8 vocab=e73fa129
-/
lemma radical_sup {I J : IdealSheafData X} :
    radical (I ⊔ J) = radical (radical I ⊔ radical J) := by
  ext U : 2
  exact (Ideal.radical_sup (I.ideal U) (J.ideal U))

/--
@isnad1 id=eq.0h3v.s5.c3893bc0fda1 from=seed src=0 shape=02b38b83 vocab=a08c69ce
-/
@[simp]
lemma radical_inf {I J : IdealSheafData X} :
    radical (I ⊓ J) = radical I ⊓ radical J := by
  ext U : 2
  simp only [radical_ideal, ideal_inf, Pi.inf_apply, Ideal.radical_inf]

/--
@isnad1 id=eq.0h3v.s5.1a31ce84dd8d from=seed src=0 shape=dffffb41 vocab=c0a836ad
-/
@[simp]
lemma radical_mul {I J : IdealSheafData X} :
    radical (I * J) = radical I ⊓ radical J := by
  ext U : 2
  simp only [radical_ideal, ideal_mul, Pi.mul_apply, Ideal.radical_mul, ideal_inf, Pi.inf_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The vanishing ideal sheaf of a closed set,
which is the largest ideal sheaf whose support is equal to it.
The reduced induced scheme structure on the closed set is the quotient of this ideal. -/
@[simps! ideal coe_support]
noncomputable nonrec def vanishingIdeal (Z : Closeds X) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ vanishingIdeal (U.2.fromSpec ⁻¹' Z))
    (fun U f ↦ by
      let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        suffices ∀ p, (X.affineBasicOpen f).2.fromSpec p ∈ Z → F.hom x ∈ p.asIdeal by
          simpa [PrimeSpectrum.mem_vanishingIdeal] using! this
        intro x hxZ
        refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx
          (Spec.map (X.presheaf.map (homOfLE _).op) x) ?_
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply,
          IsAffineOpen.map_fromSpec _ (X.affineBasicOpen f).2]
      · let : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) := F.hom.toAlgebra
        have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
          U.2.isLocalization_of_eq_basicOpen _ _ rfl
        intro x hx
        dsimp only at hx ⊢
        have : Topology.IsOpenEmbedding (Spec.map F) :=
          localization_away_isOpenEmbedding Γ(X, X.basicOpen f) f
        rw [← U.2.map_fromSpec (X.affineBasicOpen f).2 (homOfLE (X.basicOpen_le f)).op,
          Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hx
        generalize U.2.fromSpec ⁻¹' Z = Z' at hx ⊢
        replace hx : x ∈ vanishingIdeal (Spec.map F ⁻¹' Z') := hx
        obtain ⟨I, hI, e⟩ :=
          (isClosed_iff_zeroLocus_radical_ideal _).mp (isClosed_closure (s := Z'))
        rw [← vanishingIdeal_closure,
          ← this.isOpenMap.preimage_closure_eq_closure_preimage this.continuous, e] at hx
        rw [← vanishingIdeal_closure, e]
        erw [preimage_comap_zeroLocus] at hx
        rwa [← PrimeSpectrum.zeroLocus_span, ← Ideal.map, vanishingIdeal_zeroLocus_eq_radical,
          ← RingHom.algebraMap_toAlgebra (X.presheaf.map _).hom,
          ← IsLocalization.map_radical (.powers f), ← vanishingIdeal_zeroLocus_eq_radical] at hx)
    Z
    (fun U x hxU ↦ by
      trans x ∈ X.zeroLocus (U := U.1) (vanishingIdeal (U.2.fromSpec ⁻¹' Z)) ∩ U.1
      · rw [← U.2.fromSpec_image_zeroLocus, zeroLocus_vanishingIdeal_eq_closure,
          ← U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
            U.2.fromSpec.continuous,
          Set.image_preimage_eq_inter_range, Z.isClosed.closure_eq, IsAffineOpen.range_fromSpec]
        simp [hxU]
      · simp [hxU])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h3v.s6.ce42bb8a4ff5 from=seed src=0 shape=baa5bead vocab=48f7f87a
-/
lemma le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} :
    Z ≤ I.support ↔ I ≤ vanishingIdeal Z := by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans ∀ U : X.affineOpens, (Z : Set X) ∩ U ⊆ I.support ∩ U
  · refine ⟨fun H U x hx ↦ ⟨H hx.1, hx.2⟩, fun H x hx ↦ ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (H ⟨U, hU⟩ ⟨hx, hxU⟩).1
  refine forall_congr' fun U ↦ ?_
  rw [coe_support_inter, ← Set.image_subset_image_iff U.2.fromSpec.isOpenEmbedding.injective,
    Set.image_preimage_eq_inter_range, IsAffineOpen.fromSpec_image_zeroLocus,
    IsAffineOpen.range_fromSpec]

/-- `support` and `vanishingIdeal` forms a Galois connection.
This is the global version of `PrimeSpectrum.gc`.
@isnad1 id=galoisco.0h1v.s6.69277c8bdf2d from=seed src=0 shape=caac5a09 vocab=dc4161d0
-/
lemma gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
  fun _ _ ↦ le_support_iff_le_vanishingIdeal

/--
@isnad1 id=le.1h3v.s7.a449762d4bcf from=seed src=0 shape=91534d71 vocab=aedf0ff6
-/
lemma vanishingIdeal_antimono {S T : Closeds X} (h : S ≤ T) : vanishingIdeal T ≤ vanishingIdeal S :=
  gc.monotone_u h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h2v.s4.2cb7c0f5a5d1 from=seed src=0 shape=78b01572 vocab=99560a94
-/
lemma vanishingIdeal_support {I : IdealSheafData X} :
    vanishingIdeal I.support = I.radical := by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
    IsAffineOpen.fromSpec_image_zeroLocus, coe_support_inter]

/--
@isnad1 id=eq.0h1v.s8.121a74d305aa from=seed src=0 shape=5d05eead vocab=71ed6f97
-/
@[simp] lemma vanishingIdeal_bot : vanishingIdeal (X := X) ⊥ = ⊤ := gc.u_top

/--
@isnad1 id=eq.0h1v.s7.468fa2e482f7 from=seed src=0 shape=01adfa0d vocab=9dd0ff0b
-/
@[simp] lemma vanishingIdeal_top : vanishingIdeal (X := X) ⊤ = X.nilradical := by
  rw [← support_bot, vanishingIdeal_support, nilradical]

/--
@isnad1 id=eq.0h3v.s7.df20d366ec20 from=seed src=0 shape=9eecad77 vocab=70a97c7b
-/
@[simp] lemma vanishingIdeal_iSup {ι : Sort*} (Z : ι → Closeds X) :
    vanishingIdeal (iSup Z) = ⨅ i, vanishingIdeal (Z i) := gc.u_iInf

/--
@isnad1 id=eq.0h2v.s8.a56ae179837e from=seed src=0 shape=76be53f9 vocab=a0566ea0
-/
@[simp] lemma vanishingIdeal_sSup (Z : Set (Closeds X)) :
    vanishingIdeal (sSup Z) = ⨅ z ∈ Z, vanishingIdeal z := gc.u_sInf

/--
@isnad1 id=eq.0h3v.s7.6d8bf537c52e from=seed src=0 shape=74719ee6 vocab=c4e4733e
-/
@[simp] lemma vanishingIdeal_sup (Z Z' : TopologicalSpace.Closeds X) :
    vanishingIdeal (Z ⊔ Z') = vanishingIdeal Z ⊓ vanishingIdeal Z' := gc.u_inf

/--
@isnad1 id=eq.0h3v.s7.8478f264765c from=seed src=0 shape=86e4283b vocab=1e2b41dc
-/
@[simp] lemma support_sup (I J : X.IdealSheafData) :
    (I ⊔ J).support = I.support ⊓ J.support := gc.l_sup

/--
@isnad1 id=eq.0h3v.s7.2bdf5f2ea8d8 from=seed src=0 shape=bac2ffb5 vocab=62427265
-/
@[simp] lemma support_iSup {ι : Sort*} (I : ι → X.IdealSheafData) :
    (iSup I).support = ⨅ i, (I i).support := gc.l_iSup

/--
@isnad1 id=eq.0h2v.s8.ddd4e9e449d6 from=seed src=0 shape=c5fd5dc2 vocab=787ccca3
-/
@[simp] lemma support_sSup (I : Set X.IdealSheafData) :
    (sSup I).support = ⨅ i ∈ I, i.support := gc.l_sSup

end ofIsClosed

end IdealSheafData

section IsReduced

/--
@isnad1 id=eq.0h1v.s4.61e026d2568c from=seed src=0 shape=dfc0d94f vocab=6cd04853
-/
lemma nilradical_eq_bot [IsReduced X] : X.nilradical = ⊥ := by
  ext; simp [nilradical, Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]

/--
@isnad1 id=iff.0h2v.s8.6cacafbcfc35 from=seed src=0 shape=0092661b vocab=3299cf61
-/
lemma IdealSheafData.support_eq_top_iff [IsReduced X] {I : X.IdealSheafData} :
    I.support = ⊤ ↔ I = ⊥ := by
  rw [← top_le_iff, le_support_iff_le_vanishingIdeal,
    vanishingIdeal_top, nilradical_eq_bot, le_bot_iff]

end IsReduced

section ker

open IdealSheafData

variable {Y Z : Scheme.{u}}

/-- The kernel of a morphism,
defined as the largest (quasi-coherent) ideal sheaf contained in the component-wise kernel.
This is usually only well-behaved when `f` is quasi-compact. -/
def Hom.ker (f : X.Hom Y) : IdealSheafData Y :=
  ofIdeals fun U ↦ RingHom.ker (f.app U).hom

/--
@isnad1 id=le.0h4v.s13.b58149a7b2d9 from=seed src=0 shape=06932a1b vocab=e5586d19
-/
lemma Hom.ideal_ker_le (f : X.Hom Y) (U : Y.affineOpens) :
    f.ker.ideal U ≤ RingHom.ker (f.app U).hom :=
  ideal_ofIdeals_le _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s12.9153c9dfab06 from=seed src=0 shape=8d48e46c vocab=809388a2
-/
@[simp]
lemma Hom.ker_apply (f : X.Hom Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := by
  let I : IdealSheafData Y := ⟨fun U ↦ RingHom.ker (f.app U).hom, ?_, _, rfl⟩
  · exact congr($(ofIdeals_ideal I).ideal U)
  intro U s
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    simp_rw [RingHom.comap_ker, ← CommRingCat.hom_comp, Scheme.affineBasicOpen_coe, f.naturality,
      CommRingCat.hom_comp, ← RingHom.comap_ker]
    exact Ideal.ker_le_comap _ hx
  · intro x hx
    have := U.2.isLocalization_basicOpen s
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    refine (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ?_
    suffices ∃ (V : X.Opens) (hV : V = X.basicOpen ((f.app U).hom s)),
        letI := hV.trans_le (X.basicOpen_le _); ((f.app U).hom x |_ V) = 0 by
      obtain ⟨_, rfl, H⟩ := this
      obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        X (U := f ⁻¹ᵁ U) (QuasiCompact.isCompact_preimage (f := f) _ U.1.2 U.2.isCompact)
        (f.app U x) (f.app U s) H
      exact ⟨_, ⟨n, rfl⟩, by simpa using hn⟩
    refine ⟨f ⁻¹ᵁ Y.basicOpen s, by simp, ?_⟩
    replace hx : (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op ≫ f.app _).hom x = 0 := by
      trans (f.app (Y.basicOpen s)).hom (algebraMap Γ(Y, U) _ x)
      · simp [-NatTrans.naturality, RingHom.algebraMap_toAlgebra]
      · simp only [Scheme.affineBasicOpen_coe, RingHom.mem_ker] at hx
        rw [← IsLocalization.mk'_spec' (M := .powers s), map_mul, hx, mul_zero]
    rwa [f.naturality] at hx

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=le.0h5v.s5.dad71ef197f0 from=seed src=0 shape=dcc78091 vocab=0c4b9f3e
-/
lemma Hom.le_ker_comp (f : X ⟶ Y) (g : Y.Hom Z) : g.ker ≤ (f ≫ g).ker := by
  refine ofIdeals_mono fun U ↦ ?_
  rw [Scheme.Hom.comp_app f g U, CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact Ideal.ker_le_comap _

/--
@isnad1 id=eq.0h3v.s5.6ea1bac0be5c from=seed src=0 shape=a38e31a6 vocab=626741c5
-/
lemma ker_eq_top_of_isEmpty (f : X.Hom Y) [IsEmpty X] : f.ker = ⊤ :=
  top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ ↦ by simpa using Subsingleton.elim _ _)

/--
@isnad1 id=eq.0h3v.s5.bbc1b92623b5 from=seed src=0 shape=03c6b4dd vocab=3f835379
-/
@[simp]
lemma Hom.ker_eq_bot_of_isIso (f : X ⟶ Y) [IsIso f] : f.ker = ⊥ := by
  ext U
  simp [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f.app U)).1]

/--
@isnad1 id=eq.0h5v.s5.351b150444d9 from=seed src=0 shape=aade9575 vocab=0c76d628
-/
lemma Hom.ker_comp_of_isIso (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : (f ≫ g).ker = g.ker :=
  (f.le_ker_comp g).antisymm' (((inv f).le_ker_comp _).trans (by simp))

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s12.4d4f44337ba3 from=seed src=0 shape=62f940e9 vocab=fc753c88
-/
lemma ker_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    f.ker = ofIdealTop (RingHom.ker f.appTop.hom) := by
  refine (le_of_isAffine ((f.ideal_ker_le _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U ↦ ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual

/--
@isnad1 id=le.0h3v.s8.69c714aae9af from=seed src=0 shape=31fd44eb vocab=059467c2
-/
lemma Hom.range_subset_ker_support (f : X ⟶ Y) :
    Set.range f ⊆ f.ker.support := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ((coe_support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x ∈ f ⁻¹ᵁ Y.basicOpen s := hxs
  rwa [Scheme.preimage_basicOpen, RingHom.mem_ker.mp (f.ideal_ker_le _ hs),
    Scheme.basicOpen_zero] at this

/--
@isnad1 id=iff.0h3v.s5.db23369cb547 from=seed src=0 shape=f8b07b8e vocab=626741c5
-/
lemma Hom.ker_eq_top_iff_isEmpty (f : X.Hom Y) : f.ker = ⊤ ↔ IsEmpty X :=
  ⟨fun H ↦ by simpa [H] using f.range_subset_ker_support, fun _ ↦ ker_eq_top_of_isEmpty f⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h5v.s11.df794fcd9622 from=seed src=0 shape=fa654c19 vocab=b6ca7c62
-/
lemma Hom.iInf_ker_openCover_map_comp_apply
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) (U : Y.affineOpens) :
    ⨅ i, (𝒰.f i ≫ f).ker.ideal U = f.ker.ideal U := by
  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, map_zero, exists_and_left]
  refine ⟨𝒰.f i ''ᵁ 𝒰.f i ⁻¹ᵁ f ⁻¹ᵁ U.1, ⟨_, hxU, rfl⟩,
    Set.image_preimage_subset (𝒰.f i) (f ⁻¹ᵁ U), ?_⟩
  apply ((𝒰.f i).appIso _).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  simpa [Scheme.Hom.appLE] using! ideal_ker_le _ _ (Ideal.mem_iInf.mp hs i)

/--
@isnad1 id=eq.0h4v.s6.019b7e8b5953 from=seed src=0 shape=45c2887a vocab=e2b1b9bb
-/
lemma Hom.iInf_ker_openCover_map_comp (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover) :
    ⨅ i, (𝒰.f i ≫ f).ker = f.ker := by
  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f)
  refine iInf_le_iff.mpr fun I hI U ↦ ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰, le_iInf_iff]
  exact fun i ↦ hI i U

/--
@isnad1 id=eq.0h4v.s7.7c763a2c341e from=seed src=0 shape=cc94b3b7 vocab=a73f9181
-/
lemma Hom.iUnion_support_ker_openCover_map_comp
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) [Finite 𝒰.I₀] :
    ⋃ i, ((𝒰.f i ≫ f).ker.support : Set Y) = f.ker.support := by
  cases isEmpty_or_nonempty 𝒰.I₀
  · have : IsEmpty X := Function.isEmpty 𝒰.idx
    simp [ker_eq_top_of_isEmpty]
  suffices ∀ U : Y.affineOpens,
      (⋃ i, (𝒰.f i ≫ f).ker.support) ∩ U = (f.ker.support ∩ U : Set Y) by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    simpa [hxU] using congr(x ∈ $(this ⟨U, hU⟩))
  intro U
  simp only [Set.iUnion_inter, coe_support_inter, ← f.iInf_ker_openCover_map_comp_apply 𝒰,
    Scheme.zeroLocus_iInf_of_nonempty]

/--
@isnad1 id=eq.0h5v.s10.f7f1b265edb0 from=seed src=0 shape=0ee9602c vocab=4120a011
-/
lemma ker_morphismRestrict_ideal (f : X.Hom Y) [QuasiCompact f]
    (U : Y.Opens) (V : U.toScheme.affineOpens) :
    (f ∣_ U).ker.ideal V = f.ker.ideal ⟨U.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩ := by
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).1

/--
@isnad1 id=eq.1h9v.s12.da97de11caab from=seed src=0 shape=3f827973 vocab=8a23eb22
-/
lemma ker_ideal_of_isPullback_of_isOpenImmersion {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV]
    [QuasiCompact f] (H : IsPullback f' iU iV f) (W) :
    f'.ker.ideal W =
      (f.ker.ideal ⟨iV ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).comap (iV.appIso W).inv.hom := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback H inferInstance
  ext x
  have : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
  let e : Γ(X, f ⁻¹ᵁ iV ''ᵁ W) ≅ Γ(U, f' ⁻¹ᵁ W) :=
    X.presheaf.mapIso (eqToIso this).op ≪≫ iU.appIso _
  have : (iV.appIso W).inv ≫ f.app _ = f'.app W ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, e, Scheme.Hom.appLE_comp_appLE, H.w]
  simp only [Scheme.Hom.ker_apply, RingHom.mem_ker, Ideal.mem_comap, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, this]
  simpa using (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv).1).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h3v.s8.23e79b64a8f0 from=seed src=0 shape=5fe95bb1 vocab=466279e4
-/
lemma Hom.support_ker (f : X ⟶ Y) [QuasiCompact f] :
    f.ker.support = closure (Set.range f) := by
  apply subset_antisymm
  · wlog hY : ∃ S, Y = Spec S
    · intro x hx
      let 𝒰 := Y.affineCover
      obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
      have inst : QuasiCompact (𝒰.pullbackHom f i) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      have := this (𝒰.pullbackHom f i) ⟨_, rfl⟩
        ((coe_support_inter _ ⟨⊤, isAffineOpen_top _⟩).ge ⟨?_, Set.mem_univ x⟩).1
      · have := image_closure_subset_closure_image (f := 𝒰.f i)
          (𝒰.f i).continuous (Set.mem_image_of_mem _ this)
        rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, 𝒰.pullbackHom_map] at this
        exact closure_mono (Set.range_comp_subset_range _ _) this
      · rw [← (𝒰.f i).isOpenEmbedding.injective.mem_set_image, Scheme.image_zeroLocus,
          ker_ideal_of_isPullback_of_isOpenImmersion f (𝒰.pullbackHom f i)
            ((𝒰.pullback₁ f).f i) (𝒰.f i),
          Ideal.coe_comap, Set.image_preimage_eq]
        · exact ⟨((coe_support_inter _ _).le ⟨hx, by simp⟩).1, ⟨_, rfl⟩⟩
        · exact (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso ⊤).inv).2
        · exact (IsPullback.of_hasPullback _ _).flip
    obtain ⟨S, rfl⟩ := hY
    wlog hX : ∃ R, X = Spec R generalizing X S
    · intro x hx
      have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
      let 𝒰 := X.affineCover.finiteSubcover
      obtain ⟨_, ⟨i, rfl⟩, hx⟩ := (f.iUnion_support_ker_openCover_map_comp 𝒰).ge hx
      have inst : QuasiCompact (𝒰.f i ≫ f) := HasAffineProperty.iff_of_isAffine.mpr
        (inferInstanceAs <| CompactSpace (Spec _))
      exact closure_mono (Set.range_comp_subset_range _ _) (this S (𝒰.f i ≫ f) ⟨_, rfl⟩ hx)
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    rw [ker_of_isAffine, coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap,
      RingHom.comap_ker, ← PrimeSpectrum.closure_range_comap, ← CommRingCat.hom_comp,
      ← Scheme.ΓSpecIso_inv_naturality]
    simp only [CommRingCat.hom_comp, PrimeSpectrum.comap_comp]
    exact closure_mono (Set.range_comp_subset_range _ (Spec.map φ))
  · rw [(support _).isClosed.closure_subset_iff]
    exact f.range_subset_ker_support

/-- The functor taking a morphism into `Y` to its kernel as an ideal sheaf on `Y`. -/
@[simps]
def kerFunctor (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ IdealSheafData Y where
  obj f := f.unop.hom.ker
  map {f g} hfg := homOfLE <| by simpa only [Functor.id_obj, Functor.const_obj_obj,
    OrderDual.toDual_le_toDual, ← Over.w hfg.unop] using hfg.unop.left.le_ker_comp f.unop.hom
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable (X) in
/--
@isnad1 id=eq.0h1v.s10.36a95b8abd7c from=seed src=0 shape=c680d4ec vocab=44bbf65c
-/
@[simp]
lemma ker_toSpecΓ [CompactSpace X] : X.toSpecΓ.ker = ⊥ := by
  apply IdealSheafData.ext_of_isAffine
  simpa using! RingHom.ker_coe_equiv (ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv

end ker

end Scheme

end AlgebraicGeometry
