/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.DTop
public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.SplitPath.SplitDipath
import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.CoverLemma
import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.DipathSubtype
import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.SplitPath.SplitProperties

/-!
# LeanPool.DirectedTopologyLean4.PathCover
-/

@[expose] public section

/-
  This file contains the definition of a directed path being n-covered by two subspaces X₁ and X₂:
  It maps any subinterval [i/n, (i+1)/n] into either X₁ or X₂.
  We give this definition inductively.
  This file contains properties about dipaths and parts of dipaths being n-covered.
-/

open Set
open scoped unitInterval

noncomputable section

namespace Dipath

variable {X : dTopCat} {X₀ X₁ : Set X}

/-- A dipath `γ` is *covered* by the cover `X₀ ∪ X₁ = univ` when its range lies inside one of
the two sets. -/
def covered {x₀ x₁ : X} (hX : X₀ ∪ X₁ = univ) (γ : Dipath x₀ x₁) : Prop :=
  let _ : X₀ ∪ X₁ = univ := hX
  (range γ ⊆ X₀) ∨ (range γ ⊆ X₁)

namespace covered

variable {x₀ x₁ : X}

/--
@isnad1 id=covered.1h4v.s5.f121f0225ad1 from=translated src=- shape=ccd587c9 vocab=2cd0aa3a
-/
lemma covered_refl (x : X) (hX : X₀ ∪ X₁ = univ) : covered hX (Dipath.refl x) := by
  rcases (Set.mem_union x X₀ X₁).mp (Filter.mem_top.mpr hX x) with hx₀ | hx₁
  · exact Or.inl (DiSubtype.range_refl_subset_of_mem hx₀)
  · exact Or.inr (DiSubtype.range_refl_subset_of_mem hx₁)

/--
@isnad1 id=covered.2h6v.s7.94ab75b36fcc from=translated src=- shape=ddb60f00 vocab=970890ca
-/
lemma covered_of_extended_image_subset (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ)
    (hγ : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁) :
    covered hX γ := by
  rw [(Dipath.range_eq_image γ).symm] at hγ
  exact hγ

/--
@isnad1 id=and.2h8v.s6.37883e036ebf from=translated src=- shape=de2e4436 vocab=934840c4
-/
lemma covered_of_covered_trans {x₂ : X} {γ₁ : Dipath x₀ x₁} {γ₂ : Dipath x₁ x₂}
  {hX : X₀ ∪ X₁ = univ} (hγ : covered hX (γ₁.trans γ₂)) :
    (covered hX γ₁ ∧ covered hX γ₂) := by
  unfold covered at *
  rw [Dipath.trans_range _ _] at hγ
  rcases hγ with h | h
  · simp_all
  · simp_all

/--
@isnad1 id=covered.2h7v.s7.4e78d44ea4c7 from=translated src=- shape=25b8bd6d vocab=79f0ff93
-/
lemma covered_subparam_of_covered {γ : Dipath x₀ x₁} {hX : X₀ ∪ X₁ = univ} (hγ : covered hX γ)
    (f : D(I,I)) :
    covered hX (γ.subparam f) := by
  rcases hγ with hγ | hγ
  · exact Or.inl (subset_trans (Dipath.subparam_range γ f) hγ)
  · exact Or.inr (subset_trans (Dipath.subparam_range γ f) hγ)

/--
@isnad1 id=iff.3h7v.s7.cd8378009a10 from=translated src=- shape=289c930a vocab=cc8bfe6c
-/
lemma covered_reparam_iff (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (f : D(I,I)) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) :
    covered hX γ ↔ covered hX (γ.reparam f hf₀ hf₁) := by
  unfold covered
  rw [Dipath.range_reparam _ _]

/--
@isnad1 id=iff.3h8v.s6.185b6196ddb3 from=translated src=- shape=2022ba77 vocab=7e1055b8
-/
lemma covered_cast_iff {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ)
    (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) :
    covered hX γ ↔ covered hX (γ.cast hx₀ hx₁) := by rfl

/-- If γ is a dipath that is covered, then by splitting it into two parts [0, T] and [T, 1], both
parts remain covered
@isnad1 id=and.4h7v.s7.5b91d0222769 from=translated src=- shape=f6c7be1f vocab=1523bf2c
-/
lemma covered_split_path {γ : Dipath x₀ x₁} {hX : X₀ ∪ X₁ = Set.univ} {T : I}
    (hT₀ : 0 < T) (hT₁ : T < 1) (hγ : covered hX γ) :
    covered hX (SplitDipath.FirstPart γ T) ∧ covered hX (SplitDipath.SecondPart γ T) := by
  apply covered_of_covered_trans
  apply (covered_reparam_iff _ hX (SplitDipath.transReparamMap hT₀ hT₁) _ _).mpr
  · rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁] at hγ
    exact hγ

end covered

open covered

/-- We say that `coveredPartwise hX γ n` if a dipath γ can be split into n+1 parts, each of which
is covered by `X₁` or `X₂`
-/
def coveredPartwise (hX : X₀ ∪ X₁ = Set.univ) {x y : X} (γ : Dipath x y) (n : ℕ) : Prop :=
  match n with
  | Nat.zero => covered hX γ
  | Nat.succ n =>
      covered hX (SplitDipath.FirstPart γ
        (Fraction.ofPos (show 0 < (n.succ + 1) by norm_num))) ∧
      coveredPartwise hX (SplitDipath.SecondPart γ
        (Fraction.ofPos (show 0 < (n.succ + 1) by norm_num))) n

namespace coveredPartwise

/--
@isnad1 id=coveredp.4h9v.s6.fae404ccebe7 from=translated src=- shape=0201e15c vocab=3b73fda8
-/
lemma covered_partwise_of_equal (hX : X₀ ∪ X₁ = Set.univ) {x₀ x₁ : X} {γ₁ γ₂ : Dipath x₀ x₁}
    {n m : ℕ} (h : γ₁ = γ₂) (h' : n = m) (hγ₁ : coveredPartwise hX γ₁ n) :
  coveredPartwise hX γ₂ m := by subst_vars; exact hγ₁

/-- If γ is a dipath that is fully covered, then it is also partwise covered for all n ∈ ℕ
@isnad1 id=coveredp.2h7v.s5.a565edd18ae1 from=translated src=- shape=91c1d2b4 vocab=e4c7add9
-/
lemma covered_partwise_of_covered {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered hX γ → coveredPartwise hX γ n := by
  induction n
  case zero =>
    intros _ _ _ hγ
    exact hγ
  case succ n ih =>
    intros x₀ x₁ γ hγ
    constructor
    · exact (covered_split_path (Fraction.ofPos_pos _)
        (Fraction.ofPos_lt_one (by norm_num)) hγ).left
    · apply ih
      exact (covered_split_path (Fraction.ofPos_pos _)
        (Fraction.ofPos_lt_one (by norm_num)) hγ).right

/--
@isnad1 id=iff.3h9v.s6.4f436ccab271 from=translated src=- shape=fc968e6b vocab=63d7bb2c
-/
lemma covered_partwise_cast_iff (hX : X₀ ∪ X₁ = univ) {n : ℕ} :
    ∀ {x₀ x₁ x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁),
    coveredPartwise hX γ n ↔ coveredPartwise hX (γ.cast hx₀ hx₁) n := by
  induction n
  case zero =>
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁
    exact covered_cast_iff _ _ _ _
  case succ n ih =>
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁
    unfold coveredPartwise
    rw [SplitProperties.firstPart_cast, SplitProperties.secondPart_cast]
    constructor
    · rintro ⟨hγ₁, hγ₂⟩
      exact ⟨(covered_cast_iff _ _ _ _).mp hγ₁, (ih _ _ _).mp hγ₂⟩
    · rintro ⟨hγ₁, hγ₂⟩
      exact ⟨(covered_cast_iff _ _ _ _).mpr hγ₁, (ih _ _ _).mpr hγ₂⟩

/-- A dipath γ that can be covered with n+1 intervals can satisfied `coveredPartwise _ γ n`.
 This is the converse of `covered_by_intervals_of_covered_partwise`.
@isnad1 id=coveredp.2h7v.s8.309fb643e29e from=translated src=- shape=9ddf9b22 vocab=27611f9d
-/
lemma covered_partwise_of_covered_by_intervals {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, (∀ (i : ℕ) (_ : i < (n + 1)),
      γ.extend '' Set.Icc ((↑i) / (↑n + 1)) ((↑i + 1) / (↑n + 1)) ⊆ X₀ ∨
      γ.extend '' Set.Icc ((↑i) / (↑n + 1)) ((↑i + 1) / (↑n + 1))
          ⊆ X₁) → coveredPartwise hX γ n := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ
    have := hγ 0 (by linarith)
    unfold coveredPartwise covered
    rw [Dipath.range_eq_image]
    convert this <;> simp
  case succ n ih =>
    intros x₀ x₁ γ hγ
    constructor
    · unfold covered
      rw [SplitProperties.firstPart_range_interval γ _, ←Dipath.image_extend_eq_image]
      convert hγ 0 (by norm_num) <;> norm_num
    · apply ih
      intros i hi
      have : i + 1 < n + 2 := by linarith
      have h := hγ (i+1) (this)
      suffices hsuff :
          (SplitDipath.SecondPart γ _).extend '' Set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₀ ∨
          (SplitDipath.SecondPart γ _).extend '' Set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₁ by
        convert hsuff <;> exact (Nat.cast_succ n).symm
      rw [SplitProperties.secondPart_range_interval_coe γ _ _]
      convert h <;> exact (Nat.cast_succ i).symm
      · exact hi
      · exact Nat.succ_pos n

/-- A dipath γ that satisfies `coveredPartwise _ γ n` can be covered with n+1 intervals.
 This is the converse of `covered_partwise_of_covered_by_intervals`.
@isnad1 id=or.3h8v.s8.997a90e1e107 from=translated src=- shape=552e3f6e vocab=27611f9d
-/
lemma covered_by_intervals_of_covered_partwise {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, coveredPartwise hX γ n →
      (∀ (i : ℕ) (_ : i < (n + 1)),
        γ.extend '' Set.Icc ((↑i) / (↑n + 1)) ((↑i + 1) / (↑n + 1)) ⊆ X₀ ∨
        γ.extend '' Set.Icc ((↑i) / (↑n + 1)) ((↑i + 1) / (↑n + 1)) ⊆ X₁) := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ i hi
    rw [show i = 0 by linarith]
    suffices hsuff : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁ by
      convert hsuff <;> simp
    rw [←Dipath.range_eq_image γ]
    exact hγ
  case succ n ih =>
    intros x₀ x₁ γ hγ i hi
    by_cases h_i_eq_0 : i = 0
    · have hγ_first_cov := hγ.left
      rw [h_i_eq_0]
      have := SplitProperties.firstPart_range_interval_coe γ (show 0 < n+2 by linarith)
      unfold covered at hγ_first_cov
      rw [this] at hγ_first_cov
      convert hγ_first_cov <;> simp
      · ring
      ring
    · suffices hsuff :
          γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₀ ∨
            γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1))
                ⊆ X₁ by
        convert hsuff <;> rw [Nat.cast_sub (Nat.pos_of_ne_zero h_i_eq_0)] <;> simp
      have : i - 1 < n.succ := Nat.lt_of_succ_lt_succ
        ((Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h_i_eq_0)).symm ▸ hi)
      rw [←SplitProperties.secondPart_range_interval_coe γ (this) (by linarith)]
      convert ih hγ.right (i-1) (this) <;> exact (Nat.cast_succ n)

/--
@isnad1 id=ex.3h6v.s8.f9681cbf8bbd from=translated src=- shape=552eab58 vocab=bf2df448
-/
lemma has_interval_division {X₁ X₂ : Set X} (hX : X₁ ∪ X₂ = Set.univ) (X₁_open : IsOpen X₁)
  (X₂_open : IsOpen X₂) (γ : Dipath x₀ x₁) :
    ∃ (n : ℕ), (n > 0) ∧ ∀ (i : ℕ) (_ : i < n),
      Set.Icc ((i :ℝ)/(n :ℝ)) ((i+1 :ℝ)/(n :ℝ)) ⊆ γ.extend ⁻¹' X₁ ∨
      Set.Icc ((i :ℝ)/(n :ℝ)) ((i+1 :ℝ)/(n :ℝ)) ⊆ γ.extend ⁻¹' X₂ := by
  set c : ℕ → Set ℝ := fun i => if i = 0 then γ.extend ⁻¹' X₁ else γ.extend ⁻¹'  X₂ with c_def
  have h₁ : ∀ i, IsOpen (c i) := by
    intro i
    rw [c_def]
    by_cases i = 0
    case pos h =>
      simpa only [h, ite_eq_left]
        using (Path.continuous_extend γ.toPath).isOpen_preimage X₁ X₁_open
    case neg h =>
      simpa only [ite_eq_right h]
        using (Path.continuous_extend γ.toPath).isOpen_preimage X₂ X₂_open
  have h₂ : I ⊆ ⋃ (i : ℕ), c i := by
    intros x _
    simp only [mem_iUnion]
    have hin : γ.extend x ∈ X₁ ∪ X₂ := hX.symm ▸ (Set.mem_univ <| γ.extend x)
    rcases hin with h | h
    · exact ⟨0, by simp only [c_def, ite_eq_left rfl, Set.mem_preimage]; exact h⟩
    · exact ⟨1, by simp only [c_def, ite_eq_right one_ne_zero, Set.mem_preimage]; exact h⟩
  rcases (lebesgue_number_lemma_unit_interval h₁ h₂) with ⟨n, n_pos, hn⟩
  refine ⟨n, n_pos, ?_⟩
  intros i hi
  obtain ⟨j, hj⟩ := hn i hi
  rw [c_def] at hj
  change Icc _ _ ⊆ (if j = 0 then γ.extend ⁻¹' X₁ else γ.extend ⁻¹' X₂) at hj
  by_cases h : j = 0
  · exact Or.inl (by convert hj; simp only [h, ite_eq_left])
  · exact Or.inr (by convert hj; simp only [ite_eq_right h])

/-- If `γ` is a dipath and a directed space `X` is covered by two opens `X₁` and `X₂`, then `γ` is
n-covered for some `n`.
@isnad1 id=ex.3h6v.s6.185d2d2376ae from=translated src=- shape=1f63fb62 vocab=bf01c9c3
-/
lemma has_subpaths {X₁ X₂ : Set X} (hX : X₁ ∪ X₂ = Set.univ) (X₁_open : IsOpen X₁)
  (X₂_open : IsOpen X₂) (γ : Dipath x₀ x₁) :
    ∃ (n : ℕ), coveredPartwise hX γ n := by
  have := has_interval_division hX X₁_open X₂_open γ
  rcases this with ⟨n, n_pos, hn⟩
  use n-1
  apply covered_partwise_of_covered_by_intervals
  simp only [Order.lt_add_one_iff, image_subset_iff]
  intros i hi
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos n_pos
  have := hn i (by linarith)
  convert this <;> nth_rewrite 2 [←h] <;> simp

end coveredPartwise
end Dipath
