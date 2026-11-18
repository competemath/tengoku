import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

namespace LexGrowth

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)
def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

/--
@isnad1 id=eq.0h1v.s4.4c1971dcb6e5 from=translated src=- shape=fe2c2146 vocab=9e4fbcdb
-/
theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

/--
@isnad1 id=eq.0h2v.s5.c3b368da4e89 from=translated src=- shape=030f4f4e vocab=d7303e44
-/
theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

/--
@isnad1 id=le.0h2v.s4.07ec6f5cf2c6 from=translated src=- shape=d2ff0e15 vocab=2297b6f3
-/
theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

/--
@isnad1 id=le.0h2v.s4.ada48ae50f09 from=translated src=- shape=d5c96991 vocab=0ad24dc9
-/
theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

/--
@isnad1 id=lt.1h3v.s5.dbf71b4d3eb4 from=translated src=- shape=daa6bc3d vocab=20d1a381
-/
theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

/--
@isnad1 id=lt.0h2v.s5.81276d841d58 from=translated src=- shape=cb038863 vocab=20d1a381
-/
theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

/--
@isnad1 id=le.1h3v.s5.2c2d798fa682 from=translated src=- shape=9e65ee99 vocab=0ad24dc9
-/
theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

/--
@isnad1 id=le.0h2v.s3.96e83aae8722 from=translated src=- shape=70252ff3 vocab=4ccc40eb
-/
theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

/--
@isnad1 id=eq.0h2v.s5.8e4bd8b9761a from=translated src=- shape=98a64286 vocab=e2032075
-/
theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

/--
@isnad1 id=lt.0h2v.s3.dc2c7eeb3c8a from=translated src=- shape=167e73b6 vocab=ffb9f4d5
-/
theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

/--
@isnad1 id=eq.0h1v.s3.fbd6f9ea6f4a from=translated src=- shape=a60e91e3 vocab=be08688e
-/
theorem top_zero_left (a : ℕ) : top 0 a = a := by
  apply le_antisymm
  · have := choose_top_le 0 a; simpa using this
  · exact le_top_of_choose_le 0 a a (by simp)

/--
@isnad1 id=eq.0h1v.s4.767ac59fa63e from=translated src=- shape=fe2c2146 vocab=99d8a73d
-/
theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

/--
@isnad1 id=eq.0h1v.s3.140b6754962f from=translated src=- shape=1fa26838 vocab=be08688e
-/
theorem top_zero_right (d : ℕ) : top d 0 = d := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have h1 : (d + 1).choose (d + 1) ≤ (top d 0).choose (d + 1) := Nat.choose_le_choose _ h
    have h2 := choose_top_le d 0
    simp at h1; omega
  · exact d_le_top d 0

/--
@isnad1 id=eq.0h1v.s4.03c7ea0a1949 from=translated src=- shape=1d838610 vocab=99d8a73d
-/
theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

/--
@isnad1 id=eq.0h1v.s4.1e3b0bba89c7 from=translated src=- shape=1d838610 vocab=9e4fbcdb
-/
theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

variable (n : ℕ)

noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

/--
@isnad1 id=iff.0h3v.s8.f6e88b98f5a1 from=translated src=- shape=d4edef69 vocab=0ade84a4
-/
@[scoped simp] theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

noncomputable def MonW (w e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  (Mon n e).filter (fun m => ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0)

/--
@isnad1 id=iff.0h4v.s8.1b2267867008 from=translated src=- shape=fa9e9568 vocab=12904b75
-/
theorem mem_MonW (w e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ MonW n w e ↔ m.degree = e ∧ ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0 := by
  simp [MonW]

/--
@isnad1 id=le.1h4v.s6.2ca3394e114f from=translated src=- shape=332ddfc8 vocab=5227ae66
-/
theorem MonW_mono {w w' : ℕ} (h : w ≤ w') (e : ℕ) : MonW n w e ⊆ MonW n w' e := by
  intro m hm
  rw [mem_MonW] at hm ⊢
  exact ⟨hm.1, fun i hi => hm.2 i (h.trans hi)⟩

/--
@isnad1 id=eq.1h3v.s5.c9cb05fbf81f from=translated src=- shape=21d58703 vocab=1ecf30a4
-/
theorem MonW_of_le {w : ℕ} (h : n + 1 ≤ w) (e : ℕ) : MonW n w e = Mon n e := by
  ext m
  simp only [mem_MonW, mem_Mon, and_iff_left_iff_imp]
  intro _ i hi
  exact absurd (lt_of_lt_of_le i.2 (h.trans hi)) (lt_irrefl _)

noncomputable def var (j : ℕ) (h : j < n + 1) : Fin (n + 1) →₀ ℕ := Finsupp.single ⟨j, h⟩ 1

/--
@isnad1 id=eq.1h3v.s7.6bc14ef34277 from=translated src=- shape=d581fc2e vocab=66487c59
-/
@[scoped simp] theorem var_apply (j : ℕ) (h : j < n + 1) (i : Fin (n + 1)) :
    var n j h i = if (i : ℕ) = j then 1 else 0 := by
  simp only [var, Finsupp.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/--
@isnad1 id=eq.1h2v.s8.b6d3019fb53b from=translated src=- shape=ee9e025a vocab=8df04997
-/
@[scoped simp] theorem degree_var (j : ℕ) (h : j < n + 1) : (var n j h).degree = 1 := by
  simp [var]

noncomputable def shift (j : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  if h : j < n + 1 then B.map (addRightEmbedding (var n j h)) else ∅

/--
@isnad1 id=eq.1h3v.s6.5093090080a0 from=translated src=- shape=b7073d37 vocab=5c6b07f6
-/
theorem shift_of_le {j : ℕ} (h : n + 1 ≤ j) (B : Finset (Fin (n + 1) →₀ ℕ)) : shift n j B = ∅ := by
  simp [shift, not_lt.mpr h]

/--
@isnad1 id=iff.1h4v.s8.0d7246185252 from=translated src=- shape=e9dfaa98 vocab=6fe95326
-/
theorem mem_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ ∃ b ∈ B, b + var n j h = u := by
  simp [shift, h]

/--
@isnad1 id=eq.1h3v.s6.638595e2b347 from=translated src=- shape=1d28bff7 vocab=02875085
-/
theorem card_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    (shift n j B).card = B.card := by
  simp [shift, h]

/--
@isnad1 id=eq.0h2v.s6.b0ba1dc39d98 from=translated src=- shape=e9a03af2 vocab=0da485ac
-/
@[scoped simp] theorem shift_empty (j : ℕ) : shift n j (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  unfold shift; split_ifs <;> simp

/--
@isnad1 id=le.1h4v.s7.b2d9ecc10155 from=translated src=- shape=72a0c855 vocab=ca358a11
-/
theorem shift_mono (j : ℕ) {B B' : Finset (Fin (n + 1) →₀ ℕ)} (hB : B ⊆ B') :
    shift n j B ⊆ shift n j B' := by
  unfold shift; split_ifs
  · exact Finset.map_subset_map.mpr hB
  · exact Finset.Subset.refl _

/--
@isnad1 id=eq.2h3v.s8.05a36d604492 from=translated src=- shape=b766b891 vocab=81fc6bfe
-/
theorem sub_var_add_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    u - var n j h + var n j h = u := by
  unfold var
  exact Finsupp.sub_add_single_one_cancel (by omega)

/--
@isnad1 id=iff.1h4v.s8.9d30dfbae61e from=translated src=- shape=d7627f3a vocab=d03bcc09
-/
theorem mem_shift_iff {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ))
    (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ 1 ≤ u ⟨j, h⟩ ∧ u - var n j h ∈ B := by
  rw [mem_shift n h]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, by simpa using hb⟩
    simp [var]
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, sub_var_add_var n h u h1⟩

/--
@isnad1 id=eq.2h3v.s9.66027b771903 from=translated src=- shape=85443efb vocab=5936e70c
-/
theorem degree_sub_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    (u - var n j h).degree + 1 = u.degree := by
  conv_rhs => rw [← sub_var_add_var n h u hu]
  rw [map_add, degree_var]

/--
@isnad1 id=eq.1h3v.s7.3480a944f7de from=translated src=- shape=e58a5fb5 vocab=288f228b
-/
theorem MonW_succ {j : ℕ} (h : j < n + 1) (e : ℕ) :
    MonW n (j + 1) (e + 1) = MonW n j (e + 1) ∪ shift n j (MonW n (j + 1) e) := by
  ext u
  rw [Finset.mem_union, mem_shift_iff n h, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨hdeg, hsupp⟩
    by_cases huj : u ⟨j, h⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, h⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp i hij
    · refine Or.inr ⟨by omega, ?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u (by omega)
        omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
        rw [hsupp i hi]; simp
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, hdeg, hsupp⟩)
    · exact ⟨hdeg, fun i hi => hsupp i (by omega)⟩
    · refine ⟨?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u h1
        omega
      · have := hsupp i hi
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at this
        have hij : (i : ℕ) ≠ j := by omega
        simpa [hij] using this

/--
@isnad1 id=disjoint.0h4v.s6.37c7bd12b494 from=translated src=- shape=8d9aa4d9 vocab=0c931c1f
-/
theorem disjoint_MonW_shift (j e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    Disjoint (MonW n j e) (shift n j B) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  by_cases h : j < n + 1
  · rw [mem_shift_iff n h] at hu'
    rw [mem_MonW] at hu
    have := hu.2 ⟨j, h⟩ le_rfl
    omega
  · rw [shift_of_le n (not_lt.mp h)] at hu'
    simp at hu'

/--
@isnad1 id=eq.0h2v.s6.768eec7accc5 from=translated src=- shape=cb9bcdc6 vocab=0c056caa
-/
theorem MonW_zero_succ (e : ℕ) : MonW n 0 (e + 1) = ∅ := by
  ext u
  simp only [mem_MonW, Finset.notMem_empty, iff_false, not_and]
  intro hdeg hsupp
  have : u = 0 := by
    ext i; exact hsupp i (Nat.zero_le _)
  rw [this, map_zero] at hdeg
  omega

/--
@isnad1 id=eq.0h2v.s7.883de208c127 from=translated src=- shape=8bb72c75 vocab=8848efff
-/
theorem MonW_zero_right (w : ℕ) : MonW n w 0 = {0} := by
  ext u
  simp only [mem_MonW, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; simp

/--
@isnad1 id=eq.1h3v.s6.66bcd5005839 from=translated src=- shape=08a34086 vocab=23955f0a
-/
theorem card_MonW : ∀ (w e : ℕ), w ≤ n + 1 → (MonW n w e).card = (w + e - 1).choose e
  | w, 0, _ => by simp [MonW_zero_right]
  | 0, e + 1, _ => by
      rw [MonW_zero_succ, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
  | w + 1, e + 1, hw => by
      rw [MonW_succ n (by omega), Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _),
        card_shift n (by omega), card_MonW w (e + 1) (by omega), card_MonW (w + 1) e hw,
        show w + 1 + (e + 1) - 1 = (w + e) + 1 by omega, Nat.choose_succ_succ',
        show w + (e + 1) - 1 = w + e by omega, show w + 1 + e - 1 = w + e by omega, add_comm]

/--
@isnad1 id=eq.0h2v.s5.5f2b1c13b1ec from=translated src=- shape=df3adde0 vocab=edd62fcb
-/
theorem card_Mon (e : ℕ) : (Mon n e).card = (n + e).choose n := by
  rw [← MonW_of_le n le_rfl, card_MonW n (n + 1) e le_rfl, show n + 1 + e - 1 = n + e by omega,
    Nat.choose_symm_add]

/--
@isnad1 id=eq.1h3v.s9.73518bdb3f4a from=translated src=- shape=cdf4c5cc vocab=7d021da7
-/
theorem degree_sub_single (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hu : 1 ≤ u i) :
    (u - Finsupp.single i 1).degree + 1 = u.degree := by
  conv_rhs => rw [← Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)]
  rw [map_add, Finsupp.degree_single]

/--
@isnad1 id=ex.1h2v.s8.cd601016c52b from=translated src=- shape=4f42fe10 vocab=ca4988da
-/
theorem exists_one_le_of_degree_ne_zero (u : Fin (n + 1) →₀ ℕ) (hu : u.degree ≠ 0) :
    ∃ i, 1 ≤ u i := by
  rw [Finsupp.degree_eq_sum] at hu
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  exact ⟨i, by omega⟩

/--
@isnad1 id=ex.2h3v.s9.ddaacca4552c from=translated src=- shape=b44f4992 vocab=7d021da7
-/
theorem exists_sub_single_pos (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hi : 1 ≤ u i)
    (hdeg : 2 ≤ u.degree) : ∃ i', 1 ≤ u i' ∧ 1 ≤ (u - Finsupp.single i' 1 : Fin (n + 1) →₀ ℕ) i := by
  by_cases h2 : 2 ≤ u i
  · refine ⟨i, hi, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
  · have hui : u i = 1 := by omega
    have hsum : u i + ∑ k ∈ Finset.univ.erase i, u k = u.degree := by
      rw [Finsupp.degree_eq_sum]; exact Finset.add_sum_erase _ _ (Finset.mem_univ i)
    have hne : ∑ k ∈ Finset.univ.erase i, u k ≠ 0 := by omega
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    refine ⟨k, by omega, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, ite_eq_right hki]; omega

noncomputable def BW : ℕ → ℕ → Finset (Fin (n + 1) →₀ ℕ)
  | 0, a => if a = 0 then ∅ else {0}
  | δ + 1, a => MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW δ (rem δ a))

/--
@isnad1 id=eq.0h3v.s7.693e101fa119 from=translated src=- shape=4a04cec2 vocab=17885df9
-/
theorem BW_succ (δ a : ℕ) :
    BW n (δ + 1) a = MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW n δ (rem δ a)) := rfl

/--
@isnad1 id=eq.0h2v.s6.0fdd26fe02ee from=translated src=- shape=a575b913 vocab=a0f539dc
-/
theorem BW_zero_right : ∀ d : ℕ, BW n d 0 = ∅
  | 0 => by simp [BW]
  | δ + 1 => by
      rw [BW_succ, top_zero_right, rem_zero_right, BW_zero_right δ, Nat.sub_self, MonW_zero_succ,
        shift_empty, Finset.empty_union]

/--
@isnad1 id=eq.1h3v.s6.4b13f37cb040 from=translated src=- shape=094029ed vocab=3c21d7c9
-/
theorem card_MonW_succ_eq (w δ : ℕ) (hw : w ≤ n + 1) :
    (MonW n w (δ + 1)).card = (w + δ).choose (δ + 1) := by
  rw [card_MonW n w (δ + 1) hw, show w + (δ + 1) - 1 = w + δ by omega]

/--
@isnad1 id=eq.0h2v.s4.1fc8d253c55b from=translated src=- shape=0ed2de28 vocab=86a1cd52
-/
theorem top_sub_add (δ a : ℕ) : top δ a - δ + δ = top δ a := Nat.sub_add_cancel (d_le_top δ a)

/--
@isnad1 id=le.1h3v.s5.b89f79df5470 from=translated src=- shape=9a047311 vocab=0ad24dc9
-/
theorem top_le_of_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a ≤ w + δ := by
  by_contra h
  push Not at h
  have h1 : (w + δ + 1).choose (δ + 1) ≤ (top δ a).choose (δ + 1) := Nat.choose_le_choose _ h
  have h2 := choose_top_le δ a
  rw [Nat.choose_succ_succ'] at h1
  have h3 : 1 ≤ (w + δ).choose δ := Nat.choose_pos (by omega)
  omega

/--
@isnad1 id=le.1h3v.s5.a49f55a6cf77 from=translated src=- shape=7f55437a vocab=a20e2f06
-/
theorem j_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a - δ ≤ w := by
  have := top_le_of_le w δ a ha; omega

/--
@isnad1 id=lt.2h3v.s5.10408ddf1feb from=translated src=- shape=20c26ab5 vocab=c00366c3
-/
theorem j_lt_of_rem_ne_zero (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) (hr : rem δ a ≠ 0) :
    top δ a - δ < w := by
  have hj := j_le w δ a ha
  rcases hj.lt_or_eq with h | h
  · exact h
  · exfalso
    have htop : top δ a = w + δ := by have := d_le_top δ a; omega
    have := rem_add_choose δ a
    rw [htop] at this
    omega

/--
@isnad1 id=le.1h3v.s6.f6a192a73fc4 from=translated src=- shape=b2f138f4 vocab=7a066b20
-/
theorem rem_le_card (δ a : ℕ) (hj : top δ a - δ + 1 ≤ n + 1) :
    rem δ a ≤ (MonW n (top δ a - δ + 1) δ).card := by
  rw [card_MonW n _ _ hj, show top δ a - δ + 1 + δ - 1 = top δ a by have := d_le_top δ a; omega]
  exact (rem_lt δ a).le

/--
@isnad1 id=le.2h4v.s7.cb4870f59cbf from=translated src=- shape=89c1ce74 vocab=3b99fc08
-/
theorem BW_subset : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → BW n d a ⊆ MonW n w d
  | 0, w, a, hw, ha => by
      simp only [BW]
      split_ifs
      · exact Finset.empty_subset _
      · rw [MonW_zero_right]
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ]
      have hj := j_le w δ a ha
      refine Finset.union_subset (MonW_mono n hj _) ?_
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty]; exact Finset.empty_subset _
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have ih := BW_subset δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        refine (shift_mono n _ ih).trans ?_
        refine subset_trans ?_ (MonW_mono n (show top δ a - δ + 1 ≤ w by omega) (δ + 1))
        rw [MonW_succ n (show top δ a - δ < n + 1 by omega) δ]
        exact Finset.subset_union_right

/--
@isnad1 id=eq.2h4v.s6.10d280f9fb20 from=translated src=- shape=c06f0f1a vocab=07c991eb
-/
theorem card_BW : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → (BW n d a).card = a
  | 0, w, a, hw, ha => by
      rw [MonW_zero_right, Finset.card_singleton] at ha
      simp only [BW]
      split_ifs with h
      · simp [h]
      · simp; omega
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ, Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _)]
      have hj := j_le w δ a ha
      rw [card_MonW_succ_eq n _ δ (hj.trans hw), top_sub_add]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.card_empty]
        have := rem_add_choose δ a; omega
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        rw [card_shift n (by omega), card_BW δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]
        have := rem_add_choose δ a; omega

noncomputable def Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e + 1)).filter (fun u => ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B)

/--
@isnad1 id=iff.0h5v.s9.2fdd88018b9f from=translated src=- shape=026cd04c vocab=6f9d9cb2
-/
theorem mem_Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ Bplus n w e B ↔
      u ∈ MonW n w (e + 1) ∧ ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B := by
  simp [Bplus]

/--
@isnad1 id=eq.1h4v.s6.96fce112bcf7 from=translated src=- shape=ec53f0df vocab=257372ff
-/
theorem Bplus_MonW (w j δ : ℕ) (hjw : j ≤ w) :
    Bplus n w (δ + 1) (MonW n j (δ + 1)) = MonW n j (δ + 2) := by
  ext u
  rw [mem_Bplus, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩
    refine ⟨hdeg, fun i hi => ?_⟩
    by_contra hui
    obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
    have := ((mem_MonW n _ _ _).1 (hdiv i' hi')).2 i hi
    omega
  · rintro ⟨hdeg, hsupp⟩
    refine ⟨⟨hdeg, fun i hi => hsupp i (hjw.trans hi)⟩, fun i hi => ?_⟩
    rw [mem_MonW]
    refine ⟨by have := degree_sub_single n u i hi; omega, fun k hk => ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]

/--
@isnad1 id=eq.3h5v.s8.1bc2f25cf2dc from=translated src=- shape=203ff3d9 vocab=966dd7fa
-/
theorem Bplus_union_shift (w j δ : ℕ) (hj : j < n + 1) (hjw : j + 1 ≤ w)
    (B' : Finset (Fin (n + 1) →₀ ℕ)) (hB' : B' ⊆ MonW n (j + 1) δ) :
    Bplus n w (δ + 1) (MonW n j (δ + 1) ∪ shift n j B') =
      MonW n j (δ + 2) ∪ shift n j (Bplus n (j + 1) δ B') := by

  have hB : MonW n j (δ + 1) ∪ shift n j B' ⊆ MonW n (j + 1) (δ + 1) := by
    refine Finset.union_subset (MonW_mono n (Nat.le_succ j) _) ?_
    rw [MonW_succ n hj δ]
    exact (shift_mono n j hB').trans Finset.subset_union_right
  have hvar : var n j hj = Finsupp.single ⟨j, hj⟩ 1 := rfl
  ext u
  rw [mem_Bplus, Finset.mem_union, mem_shift_iff n hj, mem_Bplus, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩

    have hsupp' : ∀ i : Fin (n + 1), j < (i : ℕ) → u i = 0 := by
      intro i hi
      by_contra hui
      obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
      have := ((mem_MonW n _ _ _).1 (hB (hdiv i' hi'))).2 i (by omega)
      omega
    by_cases huj : u ⟨j, hj⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, hj⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp' i hij
    · refine Or.inr ⟨by omega, ⟨?_, fun i hi => ?_⟩, fun l hl => ?_⟩
      · have := degree_sub_var n hj u (by omega); omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp' i (by omega), Nat.zero_sub]
      ·
        have hul : 1 ≤ u l := by
          have : (u - var n j hj) l ≤ u l := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
          omega
        have hv := hdiv l hul
        rw [Finset.mem_union, mem_shift_iff n hj] at hv
        rcases hv with hv | ⟨-, hv⟩
        · exfalso
          have h0 := ((mem_MonW n _ _ _).1 hv).2 ⟨j, hj⟩ le_rfl
          by_cases hlj : l = ⟨j, hj⟩
          · subst hlj
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same, var] at h0 hl
            omega
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, ite_eq_right hlj] at h0
            omega
        · have : u - var n j hj - Finsupp.single l 1 = u - Finsupp.single l 1 - var n j hj := by
            ext k
            simp only [Finsupp.coe_tsub, Pi.sub_apply]
            omega
          rw [this]; exact hv
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, ⟨hdeg, hsupp⟩, hdiv⟩)
    ·
      refine ⟨⟨hdeg, fun i hi => hsupp i (by omega)⟩, fun i hi => ?_⟩
      refine Finset.mem_union_left _ ((mem_MonW n _ _ _).2 ⟨?_, fun k hk => ?_⟩)
      · have := degree_sub_single n u i hi; omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]
    ·
      have hu : u - var n j hj + var n j hj = u := sub_var_add_var n hj u h1
      refine ⟨⟨?_, fun i hi => ?_⟩, fun i hi => ?_⟩
      · have := degree_sub_var n hj u h1; omega
      · have h0 := hsupp i (by omega)
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at h0
        have hij : (i : ℕ) ≠ j := by omega
        simp only [hij, ite_false] at h0
        omega
      · rw [Finset.mem_union, mem_shift_iff n hj]
        by_cases hij : i = ⟨j, hj⟩
        ·
          subst hij
          rw [← hvar]
          by_cases hujj : (u - var n j hj) ⟨j, hj⟩ = 0
          · left
            rw [mem_MonW]
            refine ⟨hdeg, fun k hk => ?_⟩
            rcases hk.eq_or_lt with hkj | hkj
            · have : k = ⟨j, hj⟩ := Fin.ext hkj.symm
              rw [this]; exact hujj
            · exact hsupp k hkj
          · right
            have := hdiv ⟨j, hj⟩ (by omega)
            rw [← hvar] at this
            refine ⟨?_, this⟩
            simp only [Finsupp.coe_tsub, Pi.sub_apply] at hujj ⊢
            omega
        · right
          have hii : 1 ≤ (u - var n j hj) i := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
            have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            simp only [this, ite_false]; omega
          have hv := hdiv i hii
          refine ⟨?_, ?_⟩
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, ite_eq_right hij]; omega
          · have : u - Finsupp.single i 1 - var n j hj = u - var n j hj - Finsupp.single i 1 := by
              ext k
              simp only [Finsupp.coe_tsub, Pi.sub_apply]
              omega
            rw [this]; exact hv

/--
@isnad1 id=eq.2h4v.s7.f2fb1f02b0d1 from=translated src=- shape=8cc123eb vocab=ab01bc98
-/
theorem card_Bplus_BW : ∀ (δ w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w (δ + 1)).card →
    (Bplus n w (δ + 1) (BW n (δ + 1) a)).card = Nat.macaulayPow (δ + 1) a := by
  intro δ
  induction δ with
  | zero =>
      intro w a hw ha
      rw [card_MonW_succ_eq n w 0 hw] at ha
      have hj := j_le w 0 a ha
      rw [BW_succ, rem_zero_left, BW_zero_right, shift_empty, Finset.union_empty,
        Bplus_MonW n w _ 0 hj, card_MonW n _ _ (hj.trans hw), macaulayPow_succ, macaulayPow_zero,
        Nat.sub_zero, show top 0 a + (0 + 2) - 1 = top 0 a + 1 by omega]
      simp
  | succ δ' ih =>
      intro w a hw ha
      set δ := δ' + 1 with hδ
      rw [card_MonW_succ_eq n w δ hw] at ha
      have hj := j_le w δ a ha
      rw [BW_succ, macaulayPow_succ]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.union_empty, Bplus_MonW n w _ δ hj,
          card_MonW n _ _ (hj.trans hw), macaulayPow_zero_right,
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega]
        simp
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hjn : top δ a - δ < n + 1 := by omega
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have hB' := BW_subset n δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        rw [Bplus_union_shift n w _ δ hjn (by omega) _ hB',
          Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _), card_shift n hjn,
          card_MonW n _ _ (hj.trans hw),
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega,
          ih (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]

theorem eq_of_le_of_degree_eq (g m : Fin (n + 1) →₀ ℕ) (h : g ≤ m) (hd : g.degree = m.degree) :
    g = m := by
  have h1 : g + (m - g) = m := add_tsub_cancel_of_le h
  have h2 : (m - g).degree = 0 := by
    have := congrArg Finsupp.degree h1
    rw [map_add] at this; omega
  rw [Finsupp.degree_eq_zero_iff] at h2
  rw [h2, add_zero] at h1
  exact h1

/--
@isnad1 id=ex.2h3v.s9.457469d1ef91 from=translated src=- shape=a018d577 vocab=7d021da7
-/
theorem exists_eq_sub_single (g u : Fin (n + 1) →₀ ℕ) (h : g ≤ u) (hd : g.degree + 1 = u.degree) :
    ∃ i, 1 ≤ u i ∧ g = u - Finsupp.single i 1 := by
  have h1 : g + (u - g) = u := add_tsub_cancel_of_le h
  have h2 : (u - g).degree = 1 := by
    have := congrArg Finsupp.degree h1
    rw [map_add] at this; omega
  obtain ⟨i, hi⟩ := exists_one_le_of_degree_ne_zero n (u - g) (by omega)
  have h3 : (u - g - Finsupp.single i 1).degree = 0 := by
    have := degree_sub_single n (u - g) i hi; omega
  rw [Finsupp.degree_eq_zero_iff] at h3
  have h4 : u - g = Finsupp.single i 1 := by
    have := Finsupp.sub_add_single_one_cancel (u := u - g) (i := i) (by omega)
    rw [h3, zero_add] at this
    exact this.symm
  refine ⟨i, ?_, ?_⟩
  · have : (u - g) i ≤ u i := by simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
    omega
  · rw [← h4]

    exact (tsub_tsub_cancel_of_le h).symm

open MvPolynomial AlgebraicGeometry.HilbertFunctor

/--
@isnad1 id=eq.2h5v.s8.d988b45c7a33 from=translated src=- shape=2a68abc4 vocab=80f1af4b
-/
theorem degree_eq_of_mem_support (K : Type) [Field K] {e : ℕ} {p : MvPolynomial (Fin (n + 1)) K}
    (hp : p.IsHomogeneous e) {m : Fin (n + 1) →₀ ℕ} (hm : m ∈ p.support) : m.degree = e := by
  have h : p ∈ homogeneousSubmodule (Fin (n + 1)) K e := hp
  rw [homogeneousSubmodule_eq_finsupp_supported] at h
  exact h hm

/--
@isnad1 id=eq.2h5v.s12.df6109ef2006 from=translated src=- shape=ee9ce1a6 vocab=e150dade
-/
theorem finrank_piece_eq_card (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    (D : Finset (Fin (n + 1) →₀ ℕ)) (hD : ∀ m ∈ D, m.degree = e)
    (hJ : ∀ p : MvPolynomial (Fin (n + 1)) K, p.IsHomogeneous e →
      (p ∈ J ↔ ∀ m ∈ D, coeff m p = 0)) :
    Module.finrank K (piece J e) = D.card := by
  classical
  set V := homogeneousSubmodule (Fin (n + 1)) K e with hV

  let φ : ↥V →ₗ[K] (↥D → K) :=
    { toFun := fun p m => coeff m.1 p.1
      map_add' := fun p q => by ext m; simp
      map_smul' := fun c p => by ext m; simp [coeff_smul] }
  have hφ : ∀ (p : ↥V) (m : ↥D), φ p m = coeff m.1 p.1 := fun _ _ => rfl

  have hker : LinearMap.ker φ = Submodule.comap V.subtype (J.restrictScalars K) := by
    ext p
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.subtype_apply,
      hJ p.1 p.2, funext_iff]
    constructor
    · intro h m hm; exact h ⟨m, hm⟩
    · intro h m; exact h m.1 m.2

  have hsurj : Function.Surjective φ := by
    intro f
    let q : MvPolynomial (Fin (n + 1)) K := ∑ m : ↥D, f m • monomial m.1 (1 : K)
    have hq : q ∈ V :=
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (isHomogeneous_monomial _ (hD m.1 m.2))
    refine ⟨⟨q, hq⟩, funext fun m' => ?_⟩
    rw [hφ]
    simp only [q, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single m']
    · simp
    · intro m _ hm
      rw [ite_eq_right]
      exact fun h => hm (Subtype.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  have e₁ : piece J e ≃ₗ[K] (↥D → K) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  rw [e₁.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/--
@isnad1 id=ex.1h4v.s13.8d20c7bfb2d2 from=translated src=- shape=b4867a63 vocab=cd81201b
-/
theorem exists_ideal (δ a : ℕ) (ha : a ≤ (n + (δ + 1)).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous (δ + 1)) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J (δ + 1)) = a ∧
      Module.finrank K (piece J (δ + 1 + 1)) = Nat.macaulayPow (δ + 1) a := by
  classical

  have hcardMon : (MonW n (n + 1) (δ + 1)).card = (n + (δ + 1)).choose n := by
    rw [MonW_of_le n le_rfl, card_Mon]
  have ha' : a ≤ (MonW n (n + 1) (δ + 1)).card := hcardMon ▸ ha
  set B := BW n (δ + 1) a with hBdef
  have hB : B ⊆ MonW n (n + 1) (δ + 1) := BW_subset n (δ + 1) (n + 1) a le_rfl ha'
  have hBcard : B.card = a := card_BW n (δ + 1) (n + 1) a le_rfl ha'
  have hBplus : (Bplus n (n + 1) (δ + 1) B).card = Nat.macaulayPow (δ + 1) a :=
    card_Bplus_BW n δ (n + 1) a le_rfl ha'
  have hmemB : ∀ m ∈ B, m.degree = δ + 1 := fun m hm => ((mem_MonW n _ _ _).1 (hB hm)).1
  set G : Finset (Fin (n + 1) →₀ ℕ) := Mon n (δ + 1) \ B with hGdef
  have hmemG : ∀ m : Fin (n + 1) →₀ ℕ, m ∈ G ↔ m.degree = δ + 1 ∧ m ∉ B := fun m => by
    simp [hGdef, Finset.mem_sdiff]
  set s : Set (MvPolynomial (Fin (n + 1)) K) := (fun m => monomial m (1 : K)) '' (↑G : Set _) with hsdef
  refine ⟨Ideal.span s, ⟨s, ?_, rfl⟩, ?_, ?_⟩
  ·
    rintro p ⟨m, hm, rfl⟩
    exact isHomogeneous_monomial _ ((hmemG m).1 hm).1
  ·
    rw [← hBcard]
    refine finrank_piece_eq_card n K _ _ B hmemB fun p hp => ?_
    rw [hsdef, mem_ideal_span_monomial_image]
    constructor
    · intro h m hmB
      by_contra hc
      obtain ⟨g, hg, hgm⟩ := h m (by simpa [mem_support_iff] using hc)
      have hg' := (hmemG g).1 hg
      have : g = m := eq_of_le_of_degree_eq n g m hgm (by rw [hg'.1, hmemB m hmB])
      exact hg'.2 (this ▸ hmB)
    · intro h m hm
      refine ⟨m, (hmemG m).2 ⟨degree_eq_of_mem_support n K hp hm, fun hmB => ?_⟩, le_rfl⟩
      exact (mem_support_iff.1 hm) (h m hmB)
  ·
    rw [← hBplus]
    refine finrank_piece_eq_card n K _ _ (Bplus n (n + 1) (δ + 1) B) (fun u hu => ?_) fun p hp => ?_
    · exact ((mem_MonW n _ _ _).1 ((mem_Bplus n _ _ _ _).1 hu).1).1
    · rw [hsdef, mem_ideal_span_monomial_image]
      constructor
      · intro h u hu
        by_contra hc
        obtain ⟨g, hg, hgu⟩ := h u (by simpa [mem_support_iff] using hc)
        have hg' := (hmemG g).1 hg
        have hu' := (mem_Bplus n _ _ _ _).1 hu
        have hdeg : g.degree + 1 = u.degree := by
          rw [hg'.1, ((mem_MonW n _ _ _).1 hu'.1).1]
        obtain ⟨i, hi, rfl⟩ := exists_eq_sub_single n g u hgu hdeg
        exact hg'.2 (hu'.2 i hi)
      · intro h u hu
        have hdeg : u.degree = δ + 1 + 1 := degree_eq_of_mem_support n K hp hu

        have hnot : u ∉ Bplus n (n + 1) (δ + 1) B := fun hb => (mem_support_iff.1 hu) (h u hb)
        rw [mem_Bplus, mem_MonW] at hnot
        simp only [not_and, not_forall] at hnot
        obtain ⟨i, hi, hiB⟩ := hnot ⟨hdeg, fun i hi => absurd (lt_of_lt_of_le i.2 hi) (lt_irrefl _)⟩
        refine ⟨u - Finsupp.single i 1, (hmemG _).2 ⟨?_, hiB⟩, tsub_le_self⟩
        have := degree_sub_single n u i hi; omega

end LexGrowth
open scoped _root_.P2MW.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow.LexGrowth

open LexGrowth AlgebraicGeometry.HilbertFunctor in
/--
@isnad1 id=ex.2h4v.s13.b4ab54cfef7b from=translated src=- shape=f2b5e9f3 vocab=cd81201b
-/
theorem solution
    (n d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : a ≤ (n + d).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J d) = a ∧ Module.finrank K (piece J (d + 1)) = Nat.macaulayPow d a := by
  obtain ⟨δ, rfl⟩ : ∃ δ, d = δ + 1 := ⟨d - 1, by omega⟩
  exact exists_ideal n δ a ha K
