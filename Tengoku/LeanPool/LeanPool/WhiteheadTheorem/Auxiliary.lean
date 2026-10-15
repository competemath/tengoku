/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku

/-!
# LeanPool.WhiteheadTheorem.Auxiliary

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Auxiliary`.
-/

@[expose] public section

namespace CategoryTheory

lemma eq_of_comp_right_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (h : X ⟶ Y) [IsIso h] {f g : Y ⟶ Z} (e : h ≫ f = h ≫ g) : f = g := by
  simpa only [IsIso.inv_hom_id_assoc] using congrArg (inv h ≫ ·) e
lemma eq_of_comp_left_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (h : Y ⟶ Z) [IsIso h] {f g : X ⟶ Y} (e : f ≫ h = g ≫ h) : f = g := by
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using congrArg (· ≫ inv h) e

end CategoryTheory

namespace TopCat

open CategoryTheory

/--
@isnad1 id=isiso.0h3v.s4.0a0332b42569 from=translated src=- shape=58f4f9a4 vocab=ce6081f2
-/
instance isIso_of_isEmpty {X Y : TopCat.{u}} [IsEmpty X] [IsEmpty Y] (f : X ⟶ Y) : IsIso f := by
  use ofHom ⟨isEmptyElim, by fun_prop⟩
  constructor
  all_goals ext x; exact isEmptyElim x

end TopCat

namespace ContinuousMap

lemma eq_of_topCat_ofHom {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (e : TopCat.ofHom f = TopCat.ofHom g) : f = g :=
  TopCat.hom_ext_iff.mp e

namespace Homotopic

/--
@isnad1 id=homotopi.1h4v.s5.37fc457dabb4 from=translated src=- shape=74ddf61c vocab=93e143b9
-/
lemma of_eq (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (hfg : f = g) : f.Homotopic g :=
  hfg ▸ ContinuousMap.Homotopic.refl f

end Homotopic

end ContinuousMap

/-!
Auxiliary lemmas used in `largeCubeHomeoPDisk` and `largeCubeBoundaryHomeoPDiskBoundary`
-/

/--
@isnad1 id=le.2h4v.s5.25a052fe958e from=translated src=- shape=e5a9ed49 vocab=d6206558
-/
lemma Real.forall_le_of_iSup_le_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a := fun i ↦ by
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact Real.isLUB_sSup ‹_› hbdd |>.left (Set.mem_range_self i) |>.trans hf

/--
@isnad1 id=bddabove.0h2v.s4.b031f27ee2b8 from=translated src=- shape=6d1b6c0e vocab=7a83cde8
-/
lemma Real.range_bddAbove_of_finite_domain {ι : Type*} (f : ι → ℝ) [Finite ι] :
    BddAbove (Set.range f) :=
  (Set.finite_range f).bddAbove

/--
@isnad1 id=le.1h4v.s5.0a8507be2219 from=translated src=- shape=21753e7e vocab=7ad48cca
-/
lemma Real.forall_le_of_iSup_le_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a :=
  forall_le_of_iSup_le_of_bddAbove (range_bddAbove_of_finite_domain f) hf

/--
@isnad1 id=le.2h3v.s5.fc4d9d597cc5 from=translated src=- shape=71af8ca0 vocab=d6206558
-/
lemma Real.le_iSup_of_exists_ge_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i := by
  obtain ⟨i, hi⟩ := hf
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact hi.trans <| (Real.isLUB_sSup ‹_› hbdd).left (Set.mem_range_self i)

/--
@isnad1 id=le.1h3v.s5.13b9b57cf00b from=translated src=- shape=4719e927 vocab=7ad48cca
-/
lemma Real.le_iSup_of_exists_ge_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i :=
  le_iSup_of_exists_ge_of_bddAbove (range_bddAbove_of_finite_domain f) hf

/--
@isnad1 id=ex.2h3v.s5.0562058adade from=translated src=- shape=f652fd49 vocab=8bc0e8c8
-/
lemma Real.exists_eq_of_iSup_eq_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hfz : ∃ i, f i ≥ 0) (hf : ⨆ i, f i = a) : ∃ i, f i = a := by
  have : Nonempty ι := hfz.nonempty
  have iSup_lt_iff : ⨆ i ∈ (Set.univ : Set ι), f i < a ↔ ∀ i ∈ Set.univ, f i < a := by
    apply Set.Finite.ciSup_lt_iff Set.finite_univ
    simp_all
  have lt_iSup_iff : a < ⨆ i, f i ↔ ∃ i, a < f i :=
    lt_ciSup_iff (range_bddAbove_of_finite_domain f)
  by_contra nex; simp only [not_exists] at nex
  have : ∀ (i : ι), f i < a := fun i ↦ by
    obtain h | h | h := lt_trichotomy (f i) a
    · exact h
    · exfalso; exact nex i h
    · exfalso; exact ne_of_lt (lt_iSup_iff.mpr ⟨i, h⟩) hf.symm
  simp_all

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
variable
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j),
    φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS_cover : ∀ x : α, ∃ i, x ∈ S i) (hS_closed : ∀ i, IsClosed (S i))

/-- `liftCoverClosed` -/
noncomputable def liftCoverClosed : C(α, β) :=
  have H : ⋃ i, S i = Set.univ := Set.iUnion_eq_univ_iff.2 hS_cover
  let Φ := Set.liftCover S (fun i ↦ φ i) hφ H
  ContinuousMap.mk Φ <| continuous_iff_isClosed.mpr fun Y hY ↦ by
    have : ∀ i, φ i ⁻¹' Y = S i ∩ Φ ⁻¹' Y := fun i ↦ by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_inter_iff]
      conv => lhs; rhs; ext hxi; arg 2; equals Φ x => exact Eq.symm (Set.liftCover_of_mem hxi)
      tauto
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv_rhs => ext x; arg 1; ext i; rw [this]
      conv_rhs => ext x; rw [← Set.iUnion_inter, H, Set.univ_inter]
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      IsClosed.trans (IsClosed.preimage (φ i).continuous hY) (hS_closed i)

/--
@isnad1 id=eq.3h7v.s8.3006bb4125e0 from=translated src=- shape=6d5091e3 vocab=900a4b7c
-/
theorem liftCoverClosed_coe {i : ι} (x : S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i x := by
  rw [liftCoverClosed, ContinuousMap.coe_mk, Set.liftCover_coe _]

/--
@isnad1 id=eq.4h7v.s8.97538c973cf6 from=translated src=- shape=fea777fd vocab=a79bab4f
-/
theorem liftCoverClosed_coe' {i : ι} (x : α) (hx : x ∈ S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i ⟨x, hx⟩ := by
  rw [← liftCoverClosed_coe]

end ContinuousMap
