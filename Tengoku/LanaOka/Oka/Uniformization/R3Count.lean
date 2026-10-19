/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.Algebra.Polynomial.FieldDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An orbifold Riemann–Hurwitz count for polynomial maps `A¹ → A¹`

Let `s ∈ K[X]` (`K` algebraically closed of characteristic `0`) have degree `D ≥ 1`, and let
`E₂ ⊆ K` have three elements. Give the points of `E₂` multiplicity `m = 2`, all other points
`m = 1`, and write `e(w)` for the ramification index of `s` at `w`. If `e(w) m(w)` is constant
on the fibres of `s` (the map is étale for suitable multiplicities on the target), then either
`D = 1`, or `D = 2` and `E₂` is symmetric about a point, or `D = 3` and `E₂` is an equilateral
triangle (`RatFuncPoly.orbifold_count`).

Proof: over the finite set `V` of values of `s` on `E₂` and on the critical points, with
`n_v` points outside `E₂`, `a_v` points in `E₂` and common value `M_v ≥ 2` of `e m` on the fibre,
`2D = 2 M_v n_v + M_v a_v`; Riemann–Hurwitz `Σ_v (D - n_v - a_v) = D - 1` and `Σ a_v = 3` give
`Σ_v (M_v - 2)(2 n_v + a_v) = (4 - 2|V|) D + 2`.
-/

open Polynomial

namespace Uniformization

namespace RatFuncPoly

variable {K : Type*} [Field K]

/-- The ramification index of `s` at `w`. -/
noncomputable def ramIdx (s : K[X]) (w : K) : ℕ := rootMultiplicity w (s - C (s.eval w))

/-- The multiplicity: `2` on `E₂`, `1` elsewhere. -/
def mult [DecidableEq K] (E₂ : Finset K) (w : K) : ℕ := if w ∈ E₂ then 2 else 1

theorem natDegree_sub_C_of_pos (s : K[X]) (v : K) :
    (s - C v).natDegree = s.natDegree := natDegree_sub_C

theorem sub_C_ne_zero {s : K[X]} (hs : 0 < s.natDegree) (v : K) : s - C v ≠ 0 := by
  intro h
  have := natDegree_sub_C_of_pos s v
  rw [h, natDegree_zero] at this
  omega

theorem mem_roots_sub_C [DecidableEq K] {s : K[X]} (hs : 0 < s.natDegree) {v w : K} :
    w ∈ (s - C v).roots.toFinset ↔ s.eval w = v := by
  rw [Multiset.mem_toFinset, mem_roots (sub_C_ne_zero hs v), IsRoot, eval_sub, eval_C,
    sub_eq_zero]

theorem sum_rootMultiplicity_sub_C [DecidableEq K] [IsAlgClosed K] (s : K[X]) (v : K) :
    ∑ w ∈ (s - C v).roots.toFinset, rootMultiplicity w (s - C v) = s.natDegree := by
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_sub_C_of_pos s]

theorem ramIdx_pos {s : K[X]} (hs : 0 < s.natDegree) (w : K) : 0 < ramIdx s w := by
  rw [ramIdx, rootMultiplicity_pos (sub_C_ne_zero hs _)]
  simp

theorem ramIdx_sub_one [CharZero K] (s : K[X]) (w : K) :
    ramIdx s w - 1 = rootMultiplicity w (derivative s) := by
  have h := derivative_rootMultiplicity_of_root (p := s - C (s.eval w)) (t := w) (by simp)
  rw [derivative_sub, derivative_C, sub_zero] at h
  rw [ramIdx, h]

theorem sum_rootMultiplicity_derivative [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (s : K[X]) :
    ∑ w ∈ (derivative s).roots.toFinset, rootMultiplicity w (derivative s) =
      s.natDegree - 1 := by
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_derivative]

/-- A polynomial with a root of full multiplicity is a power of a linear factor. -/
theorem eq_C_mul_X_sub_C_pow {p : K[X]} (hp : p ≠ 0) {c : K}
    (hc : rootMultiplicity c p = p.natDegree) :
    p = C p.leadingCoeff * (X - C c) ^ p.natDegree := by
  obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd p c
  rw [hc] at hq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hp hq
  have hdeg : q.natDegree = 0 := by
    have := congrArg natDegree hq
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero c)) hq0, natDegree_pow,
      natDegree_X_sub_C, mul_one] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg] at hq
  have hlc : p.leadingCoeff = q.coeff 0 := by
    rw [hq, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_X_sub_C, one_pow, one_mul,
      leadingCoeff_C]
  rw [hlc, mul_comm]
  exact hq

/-- **The orbifold Riemann–Hurwitz count** (see the module docstring). -/
theorem orbifold_count [DecidableEq K] [IsAlgClosed K] [CharZero K] {s : K[X]}
    (hs : 0 < s.natDegree) {E₂ : Finset K} (hE : E₂.card = 3)
    (h : ∀ w w', s.eval w = s.eval w' → ramIdx s w * mult E₂ w = ramIdx s w' * mult E₂ w') :
    s.natDegree = 1 ∨ (s.natDegree = 2 ∧ ∃ c, ∀ w ∈ E₂, 2 * c - w ∈ E₂) ∨
      (s.natDegree = 3 ∧ ∃ c ρ, ∀ w ∈ E₂, (w - c) ^ 3 = ρ) := by
  set D := s.natDegree with hDdef
  set crit := (derivative s).roots.toFinset
  set V := (E₂ ∪ crit).image s.eval
  set F : K → Finset K := fun v ↦ (s - C v).roots.toFinset
  have hF : ∀ v w, w ∈ F v ↔ s.eval w = v := fun v w ↦ mem_roots_sub_C hs
  have hram : ∀ v, ∀ w ∈ F v, ramIdx s w = rootMultiplicity w (s - C v) := by
    intro v w hw; rw [ramIdx, (hF v w).mp hw]
  have hsumF : ∀ v, ∑ w ∈ F v, ramIdx s w = D := fun v ↦ by
    rw [Finset.sum_congr rfl (hram v)]; exact sum_rootMultiplicity_sub_C s v
  have hV : ∀ v ∈ V, ∃ w₀ ∈ E₂ ∪ crit, s.eval w₀ = v := fun v hv ↦ Finset.mem_image.mp hv
  choose! w₀ hw₀ hw₀v using hV
  set M : K → ℕ := fun v ↦ ramIdx s (w₀ v) * mult E₂ (w₀ v)
  have hM : ∀ v ∈ V, ∀ w ∈ F v, ramIdx s w * mult E₂ w = M v := fun v hv w hw ↦
    h w (w₀ v) (by rw [(hF v w).mp hw, hw₀v v hv])
  have hderiv0 : derivative s ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hmult : ∀ w, mult E₂ w = if w ∈ E₂ then 2 else 1 := fun w ↦ rfl
  have hM2 : ∀ v ∈ V, 2 ≤ M v := by
    intro v hv
    have hpos := ramIdx_pos hs (w₀ v)
    rcases Finset.mem_union.mp (hw₀ v hv) with h1 | h1
    · simp only [M, hmult, h1, ite_true]; omega
    · have h2 : 0 < rootMultiplicity (w₀ v) (derivative s) := by
        rw [rootMultiplicity_pos hderiv0]
        exact (mem_roots hderiv0).mp (Multiset.mem_toFinset.mp h1)
      have h3 := ramIdx_sub_one s (w₀ v)
      have h4 : 1 ≤ mult E₂ (w₀ v) := by rw [hmult]; split_ifs <;> omega
      have h5 : 2 ≤ ramIdx s (w₀ v) := by omega
      simp only [M]
      calc 2 = 2 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul h5 h4
  set n : K → ℕ := fun v ↦ (F v \ E₂).card
  set a : K → ℕ := fun v ↦ (F v ∩ E₂).card
  have hD : ∀ v ∈ V, 2 * D = 2 * M v * n v + M v * a v := by
    intro v hv
    rw [← hsumF v, Finset.mul_sum, ← Finset.sum_sdiff (Finset.inter_subset_left :
      F v ∩ E₂ ⊆ F v), Finset.sdiff_inter_self_left]
    have e1 : ∑ w ∈ F v \ E₂, 2 * ramIdx s w = ∑ _w ∈ F v \ E₂, 2 * M v := by
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      have := hM v hv w (Finset.mem_sdiff.mp hw).1
      rw [hmult, ite_eq_right (Finset.mem_sdiff.mp hw).2, mul_one] at this
      rw [this]
    have e2 : ∑ w ∈ F v ∩ E₂, 2 * ramIdx s w = ∑ _w ∈ F v ∩ E₂, M v := by
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      have := hM v hv w (Finset.mem_inter.mp hw).1
      rw [hmult, ite_eq_left (Finset.mem_inter.mp hw).2] at this
      rw [← this, mul_comm]
    rw [e1, e2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    ring
  -- fibres are disjoint
  have hdisj : (V : Set K).PairwiseDisjoint F := by
    intro v _ v' _ hvv'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    exact hvv' (((hF v w).mp hw).symm.trans ((hF v' w).mp hw'))
  -- Riemann–Hurwitz
  have hcritsub : crit ⊆ V.biUnion F := by
    intro w hw
    exact Finset.mem_biUnion.mpr ⟨s.eval w, Finset.mem_image.mpr ⟨w,
      Finset.mem_union_right _ hw, rfl⟩, (hF _ w).mpr rfl⟩
  have hRH₀ : ∑ v ∈ V, ∑ w ∈ F v, (ramIdx s w - 1) = D - 1 := by
    rw [← Finset.sum_biUnion hdisj]
    simp_rw [ramIdx_sub_one]
    rw [← Finset.sum_subset hcritsub, sum_rootMultiplicity_derivative]
    intro w _ hw
    rw [rootMultiplicity_eq_zero]
    intro hr
    exact hw (Multiset.mem_toFinset.mpr ((mem_roots hderiv0).mpr hr))
  have hcardF : ∀ v, (F v).card = n v + a v := fun v ↦
    (Finset.card_sdiff_add_card_inter (F v) E₂).symm
  have hRH : ∑ v ∈ V, ((D : ℤ) - n v - a v) = D - 1 := by
    have h1 : ∀ v, (∑ w ∈ F v, (ramIdx s w - 1) : ℕ) = D - (F v).card := by
      intro v
      rw [← hsumF v, Finset.card_eq_sum_ones, ← Finset.sum_tsub_distrib]
      exact fun w hw ↦ ramIdx_pos hs w
    have h2 : ∀ v, ((D - (F v).card : ℕ) : ℤ) = D - n v - a v := by
      intro v
      have : (F v).card ≤ D := by
        rw [← hsumF v, Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun w _ ↦ ramIdx_pos hs w
      rw [Nat.cast_sub this, hcardF]; push_cast; ring
    have := congrArg (fun x : ℕ ↦ (x : ℤ)) hRH₀
    simp only [h1, Nat.cast_sum, h2] at this
    rw [this, Nat.cast_sub (by omega : 1 ≤ D)]; push_cast; ring
  have hA : ∑ v ∈ V, a v = 3 := by
    have hdisj' : (V : Set K).PairwiseDisjoint fun v ↦ F v ∩ E₂ := fun v hv v' hv' hvv' ↦
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdisj hv hv' hvv'))
    rw [← hE, ← Finset.card_biUnion hdisj']
    congr 1
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨_, _, _, hw⟩; exact hw
    · intro hw
      exact ⟨s.eval w, Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩,
        (hF _ w).mpr rfl, hw⟩
  -- the key identity
  set T : K → ℤ := fun v ↦ ((M v : ℤ) - 2) * (2 * n v + a v)
  have hT : ∀ v ∈ V, T v = 2 * D - 4 * n v - 2 * a v := by
    intro v hv
    have := hD v hv
    have h' : (2 * D : ℤ) = 2 * M v * n v + M v * a v := by exact_mod_cast this
    simp only [T]
    linear_combination -h'
  have hsumT : ∑ v ∈ V, T v = (4 - 2 * V.card) * D + 2 := by
    rw [Finset.sum_congr rfl hT]
    have hA' : ∑ v ∈ V, (a v : ℤ) = 3 := by exact_mod_cast hA
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hRH ⊢
    linear_combination 4 * hRH + 2 * hA'
  have hTnn : ∀ v ∈ V, 0 ≤ T v := fun v hv ↦
    mul_nonneg (by have := hM2 v hv; omega) (by positivity)
  have hFne : ∀ v ∈ V, 1 ≤ n v + a v := by
    intro v hv
    rw [← hcardF]
    exact Finset.card_pos.mpr ⟨w₀ v, (hF v _).mpr (hw₀v v hv)⟩
  have hpar : ∀ v ∈ V, 0 < a v → Even (M v) := by
    intro v hv ha
    obtain ⟨w, hw⟩ := Finset.card_pos.mp ha
    have := hM v hv w (Finset.mem_inter.mp hw).1
    rw [hmult, ite_eq_left (Finset.mem_inter.mp hw).2] at this
    exact ⟨ramIdx s w, by omega⟩
  rcases (by omega : D = 1 ∨ 2 ≤ D) with hD1 | hD2
  · exact Or.inl hD1
  right
  have hk : V.card ≤ 2 := by
    by_contra hk
    have h1 := Finset.sum_nonneg hTnn
    rw [hsumT] at h1
    have : (3 : ℤ) ≤ V.card := by exact_mod_cast (by omega : 3 ≤ V.card)
    nlinarith
  have hk0 : V.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at hA
    omega
  have hk1 : V.card ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    have hvV : v ∈ V := by rw [hv]; exact Finset.mem_singleton_self v
    rw [hv, Finset.sum_singleton] at hsumT
    rw [Finset.card_singleton] at hsumT
    have := hT v hvV
    have hn : (0 : ℤ) ≤ n v := by positivity
    have ha : (0 : ℤ) ≤ a v := by positivity
    push_cast at hsumT
    linarith
  obtain ⟨v₁, v₂, hne, hV12⟩ := Finset.card_eq_two.mp (by omega : V.card = 2)
  have hv₁ : v₁ ∈ V := by rw [hV12]; simp
  have hv₂ : v₂ ∈ V := by rw [hV12]; simp
  have hsum2 : T v₁ + T v₂ = 2 := by
    rw [hV12, Finset.sum_pair hne] at hsumT
    rw [hsumT, Finset.card_pair hne]; ring
  have hA2 : a v₁ + a v₂ = 3 := by rw [hV12, Finset.sum_pair hne] at hA; exact hA
  -- the value with `T = 2` and the value with `T = 0`
  have hT01 : ∀ v ∈ V, T v ≠ 1 := by
    intro v hv h1
    have hM := hM2 v hv
    have hf := hFne v hv
    simp only [T] at h1
    have hMle : M v ≤ 3 := by
      by_contra hc
      have : (2 : ℤ) ≤ (M v : ℤ) - 2 := by omega
      nlinarith
    interval_cases hMv : M v
    · norm_num at h1
    · have ha : a v = 1 := by push_cast at h1; omega
      obtain ⟨r, hr⟩ := hpar v hv (by omega)
      omega
  have hT2 : ∀ i ∈ V, T i = 2 →
      (M i = 3 ∧ n i = 1 ∧ a i = 0 ∧ D = 3) ∨ (M i = 4 ∧ n i = 0 ∧ a i = 1 ∧ D = 2) := by
    intro i hi h2
    have hM := hM2 i hi
    have hf := hFne i hi
    have hDi := hD i hi
    simp only [T] at h2
    have hMle : M i ≤ 4 := by
      by_contra hc
      have : (3 : ℤ) ≤ (M i : ℤ) - 2 := by omega
      nlinarith
    interval_cases hMi : M i
    · norm_num at h2
    · have hna : 2 * n i + a i = 2 := by push_cast at h2; omega
      rcases (by omega : (n i = 1 ∧ a i = 0) ∨ (n i = 0 ∧ a i = 2)) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
      · left; refine ⟨rfl, h1, h1', ?_⟩; rw [h1, h1'] at hDi; omega
      · obtain ⟨r, hr⟩ := hpar i hi (by omega); omega
    · have hna : 2 * n i + a i = 1 := by push_cast at h2; omega
      right; refine ⟨rfl, by omega, by omega, ?_⟩
      rw [(by omega : n i = 0), (by omega : a i = 1)] at hDi; omega
  have hT0 : ∀ j ∈ V, T j = 0 → M j = 2 := by
    intro j hj h0
    have hf := hFne j hj
    simp only [T] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · omega
    · have : (1 : ℤ) ≤ 2 * n j + a j := by omega
      linarith
  -- the extraction
  have hlc : ∀ v, (s - C v).natDegree = D := fun v ↦ natDegree_sub_C_of_pos s v
  have hsingle : ∀ i, ∀ c ∈ F i, (F i).card = 1 →
      s - C i = C (s - C i).leadingCoeff * (X - C c) ^ D := by
    intro i c hc hcard
    obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hcard
    have hcc : F i = {c} := by rw [hc'] at hc ⊢; rw [Finset.mem_singleton.mp hc]
    have he := hsumF i
    rw [hcc, Finset.sum_singleton, hram i c (by rw [hcc]; simp)] at he
    have := eq_C_mul_X_sub_C_pow (sub_C_ne_zero hs i) (c := c) (by rw [he, hlc])
    rwa [hlc] at this
  have finish : ∀ i j, i ∈ V → j ∈ V → i ≠ j → V = {i, j} → T i = 2 → T j = 0 →
      a i + a j = 3 → (D = 2 ∧ ∃ c, ∀ w ∈ E₂, 2 * c - w ∈ E₂) ∨
        (D = 3 ∧ ∃ c ρ, ∀ w ∈ E₂, (w - c) ^ 3 = ρ) := by
    intro i j hi hj hij hVij hTi hTj haij
    have hMj := hT0 j hj hTj
    have hDj := hD j hj
    rw [hMj] at hDj
    have hlc0 : (s - C i).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (sub_C_ne_zero hs i)
    rcases hT2 i hi hTi with ⟨hMi, hni, hai, hD3⟩ | ⟨hMi, hni, hai, hD2'⟩
    · -- `D = 3`
      right
      refine ⟨hD3, ?_⟩
      have haj : a j = 3 := by omega
      obtain ⟨c, hc⟩ : (F i).Nonempty := Finset.card_pos.mp (by rw [hcardF]; omega)
      have hs3 := hsingle i c hc (by rw [hcardF]; omega)
      have hE₂j : E₂ ⊆ F j := by
        have : F j ∩ E₂ = E₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          (by rw [hE]; exact haj.ge)
        rw [← this]; exact Finset.inter_subset_left
      refine ⟨c, (j - i) / (s - C i).leadingCoeff, fun w hw ↦ ?_⟩
      have h1 := congrArg (eval w) hs3
      rw [eval_sub, eval_C, (hF j w).mp (hE₂j hw), eval_mul, eval_C, eval_pow, eval_sub,
        eval_X, eval_C, hD3] at h1
      field_simp
      rw [h1]; ring
    · -- `D = 2`
      left
      refine ⟨hD2', ?_⟩
      have haj : a j = 2 := by omega
      have hnj : n j = 0 := by omega
      obtain ⟨c, hc⟩ : (F i ∩ E₂).Nonempty := Finset.card_pos.mp (by change 0 < a i; omega)
      have hcF := (Finset.mem_inter.mp hc).1
      have hcE := (Finset.mem_inter.mp hc).2
      have hs2 := hsingle i c hcF (by rw [hcardF]; omega)
      rw [hD2'] at hs2
      have hFjE : F j ⊆ E₂ := by
        intro w hw
        by_contra hwE
        have : 0 < n j := Finset.card_pos.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwE⟩⟩
        omega
      refine ⟨c, fun w hw ↦ ?_⟩
      have hwV : s.eval w ∈ V := Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
      rw [hVij, Finset.mem_insert, Finset.mem_singleton] at hwV
      rcases hwV with hwi | hwj
      · have hwF : w ∈ F i := (hF i w).mpr hwi
        have hcard : (F i).card = 1 := by rw [hcardF]; omega
        obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hcard
        rw [hc', Finset.mem_singleton] at hwF hcF
        rw [hwF, ← hcF, two_mul, add_sub_cancel_right]
        exact hcE
      · apply hFjE
        rw [hF]
        have h1 := congrArg (eval w) hs2
        have h2 := congrArg (eval (2 * c - w)) hs2
        simp only [eval_sub, eval_C, eval_mul, eval_pow, eval_X] at h1 h2
        linear_combination h2 - h1 + hwj
  rcases (by
    have h1 := hTnn v₁ hv₁; have h2 := hTnn v₂ hv₂
    have h3 := hT01 v₁ hv₁; have h4 := hT01 v₂ hv₂
    omega : (T v₁ = 2 ∧ T v₂ = 0) ∨ (T v₁ = 0 ∧ T v₂ = 2)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact finish v₁ v₂ hv₁ hv₂ hne hV12 h1 h2 hA2
  · exact finish v₂ v₁ hv₂ hv₁ hne.symm (by rw [hV12, Finset.pair_comm]) h2 h1
      (by rw [add_comm]; exact hA2)

/-- A quadratic polynomial vanishing at three distinct points is zero. -/
theorem quadratic_eq_zero {α β γ : K} {E : Finset K} (hE : E.card = 3)
    (h : ∀ w ∈ E, α * w ^ 2 + β * w + γ = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hE
  have hx := h x (by simp)
  have hy := h y (by simp)
  have hz := h z (by simp)
  have h1 : α * (x + y) + β = 0 := by
    have : (x - y) * (α * (x + y) + β) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hxy)
  have h2 : α * (x + z) + β = 0 := by
    have : (x - z) * (α * (x + z) + β) = 0 := by linear_combination hx - hz
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hxz)
  have hα : α = 0 := by
    have : (y - z) * α = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hyz)
  have hβ : β = 0 := by rw [hα] at h1; linear_combination h1
  refine ⟨hα, hβ, ?_⟩
  rw [hα, hβ] at hx; linear_combination hx

/-- If the roots of `4X³ - g₂X - g₃` are symmetric about a point, then `g₃ = 0`. -/
theorem g₃_eq_zero_of_symm [CharZero K] {g₂ g₃ : K} {E : Finset K}
    (hE : E.card = 3) (hroot : ∀ w ∈ E, 4 * w ^ 3 - g₂ * w - g₃ = 0) {c : K}
    (hsym : ∀ w ∈ E, 2 * c - w ∈ E) : g₃ = 0 := by
  obtain ⟨h1, -, h3⟩ := quadratic_eq_zero (α := 24 * c) (β := -48 * c ^ 2)
    (γ := 32 * c ^ 3 - 2 * g₂ * c - 2 * g₃) hE fun w hw ↦ by
      linear_combination hroot w hw + hroot _ (hsym w hw)
  have hc : c = 0 := by
    have : (24 : K) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h1).resolve_left this
  rw [hc] at h3
  linear_combination -h3 / 2

/-- If the roots of `4X³ - g₂X - g₃` are `c + ρ^{1/3} ζ` (cube roots), then `g₂ = 0`. -/
theorem g₂_eq_zero_of_cube [CharZero K] {g₂ g₃ : K} {E : Finset K}
    (hE : E.card = 3) (hroot : ∀ w ∈ E, 4 * w ^ 3 - g₂ * w - g₃ = 0) {c ρ : K}
    (hcube : ∀ w ∈ E, (w - c) ^ 3 = ρ) : g₂ = 0 := by
  obtain ⟨h1, h2, -⟩ := quadratic_eq_zero (α := 12 * c) (β := -12 * c ^ 2 - g₂)
    (γ := 4 * ρ + 4 * c ^ 3 - g₃) hE fun w hw ↦ by
      linear_combination hroot w hw - 4 * hcube w hw
  have hc : c = 0 := by
    have : (12 : K) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h1).resolve_left this
  rw [hc] at h2
  linear_combination -h2

end RatFuncPoly

end Uniformization
