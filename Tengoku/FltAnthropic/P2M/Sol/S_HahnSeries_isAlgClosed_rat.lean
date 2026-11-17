import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HahnSeries_isAlgClosed_rat.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HahnSeries_isAlgClosed_rat

set_option autoImplicit false

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace DorgePuiseux

variable {K : Type*} [Field K]

def newtonInitialForm (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : K[X] :=
  ∑ i ∈ Finset.range (f.natDegree + 1),
    Polynomial.C ((f.coeff i).coeff ((f.natDegree - i : ℕ) • γ)) * Polynomial.X ^ i

/--
@isnad1 id=eq.0h5v.s8.4de0fb824dd0 from=translated src=- shape=6937b4a8 vocab=15c4cc2f
-/
theorem coeff_eval_single (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) (g : ℚ) :
    (f.eval (HahnSeries.single γ c)).coeff g =
      ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).coeff (g - i • γ) * c ^ i := by
  rw [Polynomial.eval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [HahnSeries.single_pow, HahnSeries.coeff_mul_single]

def IsNewtonSlopeBound (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : Prop :=
  ∀ i ≤ f.natDegree, f.coeff i ≠ 0 → (f.natDegree - i : ℕ) • γ ≤ (f.coeff i).order

private def slopeSupport (f : (HahnSeries ℚ K)[X]) : Finset ℕ :=
  (Finset.range f.natDegree).filter (fun j => f.coeff j ≠ 0)

end DorgePuiseux

end

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace DorgePuiseux

variable {K : Type*} [Field K]

private def evalSlopeSupport (f : (HahnSeries ℚ K)[X]) : Finset ℕ :=
  (Finset.range (f.natDegree + 1)).filter (fun j => 1 ≤ j ∧ f.coeff j ≠ 0)

private theorem evalSlopeSupport_nonempty {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) : (evalSlopeSupport f).Nonempty :=
  ⟨f.natDegree, Finset.mem_filter.mpr
    ⟨Finset.self_mem_range_succ _, hdeg, by rw [hf.coeff_natDegree]; exact one_ne_zero⟩⟩

private theorem mem_evalSlopeSupport {f : (HahnSeries ℚ K)[X]} {j : ℕ} :
    j ∈ evalSlopeSupport f ↔ j ≤ f.natDegree ∧ 1 ≤ j ∧ f.coeff j ≠ 0 := by
  simp only [evalSlopeSupport, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/--
@isnad1 id=ex.2h2v.s9.555665f762b7 from=translated src=- shape=498e3cdb vocab=ebc4b75b
-/
theorem exists_evalNewtonSlope {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) :
    ∃ γ : ℚ,
      (∀ j, 1 ≤ j → j ≤ f.natDegree → f.coeff j ≠ 0 →
        (f.coeff 0).order ≤ (f.coeff j).order + j • γ) ∧
      ∃ j₀, 1 ≤ j₀ ∧ j₀ ≤ f.natDegree ∧ f.coeff j₀ ≠ 0 ∧
        (f.coeff 0).order = (f.coeff j₀).order + j₀ • γ := by
  classical
  set δ : ℚ := (f.coeff 0).order

  set ψ : ℕ → ℚ := fun j => (δ - (f.coeff j).order) / (j : ℚ)
  obtain ⟨j₀, hj₀mem, hj₀max⟩ :=
    Finset.exists_max_image (evalSlopeSupport f) ψ (evalSlopeSupport_nonempty hf hdeg)
  obtain ⟨hj₀le, hj₀1, hj₀ne⟩ := mem_evalSlopeSupport.mp hj₀mem
  set γ : ℚ := ψ j₀
  have hj₀pos : (0 : ℚ) < (j₀ : ℚ) := by exact_mod_cast hj₀1
  refine ⟨γ, ?_, j₀, hj₀1, hj₀le, hj₀ne, ?_⟩
  ·
    intro j hj1 hjle hjne
    have hjpos : (0 : ℚ) < (j : ℚ) := by exact_mod_cast hj1
    have hmem : j ∈ evalSlopeSupport f := mem_evalSlopeSupport.mpr ⟨hjle, hj1, hjne⟩
    have hle : ψ j ≤ γ := hj₀max j hmem

    rw [nsmul_eq_mul]
    have hmul : δ - (f.coeff j).order ≤ (j : ℚ) * γ := by
      rw [div_le_iff₀ hjpos] at hle; linarith [hle]
    linarith
  ·
    rw [nsmul_eq_mul]
    have heq : (j₀ : ℚ) * γ = δ - (f.coeff j₀).order := by
      simp only [γ, ψ]; field_simp
    linarith

def evalEdgeForm (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : K[X] :=
  ∑ j ∈ Finset.range (f.natDegree + 1),
    Polynomial.C ((f.coeff j).coeff ((f.coeff 0).order - j • γ)) * Polynomial.X ^ j

/--
@isnad1 id=eq.1h4v.s7.38d3678618d2 from=translated src=- shape=ad630f56 vocab=df423900
-/
theorem evalEdgeForm_coeff (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (k : ℕ) (hk : k ≤ f.natDegree) :
    (evalEdgeForm f γ).coeff k = (f.coeff k).coeff ((f.coeff 0).order - k • γ) := by
  unfold evalEdgeForm
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hj), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

/--
@isnad1 id=eq.0h3v.s6.3fcc75ca88e8 from=translated src=- shape=29cb67d1 vocab=a0c84910
-/
theorem evalEdgeForm_coeff_zero (f : (HahnSeries ℚ K)[X]) (γ : ℚ) :
    (evalEdgeForm f γ).coeff 0 = (f.coeff 0).leadingCoeff := by
  rw [evalEdgeForm_coeff f γ 0 (Nat.zero_le _), zero_smul, sub_zero,
    ← HahnSeries.leadingCoeff_eq]

/--
@isnad1 id=eq.2h4v.s8.f114133966b5 from=translated src=- shape=2a74eee0 vocab=13b537e4
-/
theorem evalEdgeForm_coeff_of_eq {f : (HahnSeries ℚ K)[X]} {γ : ℚ} {j₀ : ℕ}
    (hj₀le : j₀ ≤ f.natDegree) (heq : (f.coeff 0).order = (f.coeff j₀).order + j₀ • γ) :
    (evalEdgeForm f γ).coeff j₀ = (f.coeff j₀).leadingCoeff := by
  rw [evalEdgeForm_coeff f γ j₀ hj₀le, heq, add_sub_cancel_right, ← HahnSeries.leadingCoeff_eq]

/--
@isnad1 id=eq.0h4v.s8.198adff7722f from=translated src=- shape=4cb0c67d vocab=5e0276c4
-/
theorem coeff_eval_single_order_zero (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) :
    (f.eval (HahnSeries.single γ c)).coeff (f.coeff 0).order =
      (evalEdgeForm f γ).eval c := by
  rw [coeff_eval_single, evalEdgeForm, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/--
@isnad1 id=eq.2h5v.s9.1d5fc194df7a from=translated src=- shape=4436b812 vocab=9915f455
-/
theorem coeff_eval_single_of_lt_order_zero {f : (HahnSeries ℚ K)[X]} {γ : ℚ}
    (hslope : ∀ j, 1 ≤ j → j ≤ f.natDegree → f.coeff j ≠ 0 →
      (f.coeff 0).order ≤ (f.coeff j).order + j • γ)
    (c : K) {g : ℚ} (hg : g < (f.coeff 0).order) :
    (f.eval (HahnSeries.single γ c)).coeff g = 0 := by
  rw [coeff_eval_single]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjle : j ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rcases Nat.eq_zero_or_pos j with hzero | hpos
  ·
    subst hzero
    rw [zero_smul, sub_zero, HahnSeries.coeff_eq_zero_of_lt_order hg, zero_mul]
  ·
    rcases eq_or_ne (f.coeff j) 0 with hcoeff | hcoeff
    · simp [hcoeff]
    · have hbound : (f.coeff 0).order ≤ (f.coeff j).order + j • γ := hslope j hpos hjle hcoeff
      have hlt : g - j • γ < (f.coeff j).order := by linarith
      rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul]

variable {Γ : Type*} [LinearOrder Γ]

structure IsBallChain {ι : Type*} [LinearOrder ι]
    (r : ι → HahnSeries Γ K) (δ : ι → WithTop Γ) : Prop where

  δ_mono : Monotone δ

  mem_ball : ∀ ⦃i j : ι⦄, i ≤ j → δ i ≤ (r j - r i).orderTop

def pseudoLimitCoeff {ι : Type*} [LinearOrder ι]
    (r : ι → HahnSeries Γ K) (δ : ι → WithTop Γ) (g : Γ) : K :=
  if h : ∃ i, (g : WithTop Γ) < δ i then (r h.choose).coeff g else 0

/--
@isnad1 id=eq.3h8v.s7.bc732d1db2d6 from=translated src=- shape=b20f0245 vocab=a56eba8c
-/
theorem IsBallChain.coeff_eq_of_lt {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ)
    {i j : ι} {g : Γ} (hgi : (g : WithTop Γ) < δ i) (hgj : (g : WithTop Γ) < δ j) :
    (r i).coeff g = (r j).coeff g := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hgj hgi (le_of_not_ge hij)).symm

  have hdiff : (r j - r i).coeff g = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hgi (h.mem_ball hij))
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
  exact hdiff.symm

/--
@isnad1 id=eq.2h7v.s6.12257b1f679b from=translated src=- shape=b23e36d3 vocab=64ed6e48
-/
theorem IsBallChain.pseudoLimitCoeff_eq {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ)
    {g : Γ} {i : ι} (hgi : (g : WithTop Γ) < δ i) :
    pseudoLimitCoeff r δ g = (r i).coeff g := by
  unfold pseudoLimitCoeff
  rw [dite_eq_left ⟨i, hgi⟩]
  exact h.coeff_eq_of_lt (Exists.choose_spec (p := fun i => (g : WithTop Γ) < δ i) ⟨i, hgi⟩) hgi

/--
@isnad1 id=ispwo.1h5v.s6.2d439369ef5f from=translated src=- shape=97108f7d vocab=e716bf3a
-/
theorem IsBallChain.isPWO_support_pseudoLimitCoeff {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ) :
    (Function.support (pseudoLimitCoeff r δ)).IsPWO := by

  refine Set.IsWF.isPWO ?_
  rw [Set.isWF_iff_no_descending_seq]
  intro f hanti hf

  have hf0 : pseudoLimitCoeff r δ (f 0) ≠ 0 := hf 0
  have hex : ∃ i, ((f 0 : Γ) : WithTop Γ) < δ i := by
    by_contra hnone
    rw [pseudoLimitCoeff, dite_eq_right hnone] at hf0; exact hf0 rfl
  obtain ⟨i₀, hi₀⟩ := hex

  have hfk : ∀ k, f k ∈ (r i₀).support := by
    intro k
    have hfk0 : f k ≤ f 0 := hanti.antitone (Nat.zero_le k)
    have hfklt : ((f k : Γ) : WithTop Γ) < δ i₀ :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr hfk0) hi₀
    have heq := h.pseudoLimitCoeff_eq hfklt
    rw [HahnSeries.mem_support, ← heq]
    exact hf k

  have hWF := (r i₀).isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hWF
  exact hWF f hanti hfk

def IsBallChain.pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ) :
    HahnSeries Γ K where
  coeff := pseudoLimitCoeff r δ
  isPWO_support' := h.isPWO_support_pseudoLimitCoeff

/--
@isnad1 id=monic.1h3v.s10.df26e111dcab from=translated src=- shape=c3c58f24 vocab=53b50bef
-/
theorem monic_taylor {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (r : HahnSeries ℚ K) :
    (Polynomial.taylor r f).Monic := by
  rw [Polynomial.taylor_apply]
  exact hf.comp (Polynomial.monic_X_add_C r)
    (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero)

end DorgePuiseux

end

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace DorgePuiseux

variable {K : Type*} [Field K]

private theorem nsmul_top_withTop {j : ℕ} (hj : 1 ≤ j) : j • (⊤ : WithTop ℚ) = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [add_comm, succ_nsmul, add_top]

private theorem nsmul_coe_withTop (j : ℕ) (q : ℚ) :
    j • (q : WithTop ℚ) = ((j • q : ℚ) : WithTop ℚ) := by
  induction j with
  | zero => simp
  | succ k ih => rw [succ_nsmul, succ_nsmul, ih]; push_cast; ring_nf

private theorem nsmul_le_nsmul_iff_withTop {j : ℕ} (hj : 1 ≤ j) {a b : WithTop ℚ} :
    j • a ≤ j • b ↔ a ≤ b := by
  cases a with
  | top =>
    rw [nsmul_top_withTop hj]
    simp only [top_le_iff]
    cases b with
    | top => simp [nsmul_top_withTop hj]
    | coe q =>
      rw [nsmul_coe_withTop]
      exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h WithTop.coe_ne_top⟩
  | coe p =>
    cases b with
    | top => simp [nsmul_top_withTop hj, nsmul_coe_withTop]
    | coe q =>
      rw [nsmul_coe_withTop, nsmul_coe_withTop, WithTop.coe_le_coe, WithTop.coe_le_coe,
        nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_iff_of_pos_left (by exact_mod_cast hj)

private theorem withTop_add_lt_add_left {a : WithTop ℚ} (ha : a ≠ ⊤) {b c : WithTop ℚ}
    (h : a + b < a + c) : b < c := by
  cases a with
  | top => exact absurd rfl ha
  | coe p =>
    cases b with
    | top => simp only [add_top, ← not_le, le_top, not_true] at h
    | coe q =>
      cases c with
      | top => exact WithTop.coe_lt_top _
      | coe s =>
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe] at h
        exact WithTop.coe_lt_coe.mpr (lt_of_add_lt_add_left h)

/--
@isnad1 id=eq.0h4v.s10.a86c591db955 from=translated src=- shape=acc32d2f vocab=3ae791f2
-/
theorem eval_sub_eval_eq_sum_taylor (f : (HahnSeries ℚ K)[X]) (r h : HahnSeries ℚ K) :
    f.eval (r + h) - f.eval r =
      ∑ j ∈ Finset.range (f.natDegree + 1),
        (if j = 0 then 0 else (Polynomial.taylor r f).coeff j * h ^ j) := by
  have hnat : (Polynomial.taylor r f).natDegree = f.natDegree := Polynomial.natDegree_taylor f r
  rw [show r + h = h + r from add_comm r h, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range, hnat]
  rw [show f.eval r = (Polynomial.taylor r f).coeff 0 from (Polynomial.taylor_coeff_zero ..).symm]
  have h0mem : 0 ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  rw [← Finset.add_sum_erase _ (fun j => (Polynomial.taylor r f).coeff j * h ^ j) h0mem,
    ← Finset.add_sum_erase _
      (fun j => if j = 0 then 0 else (Polynomial.taylor r f).coeff j * h ^ j) h0mem]
  rw [pow_zero, mul_one, add_sub_cancel_left, ite_eq_left rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

def KaplanskySlope (f : (HahnSeries ℚ K)[X]) (r r' : HahnSeries ℚ K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ f.natDegree →
    HahnSeries.addVal ℚ K (f.eval r) ≤
      HahnSeries.addVal ℚ K ((Polynomial.taylor r f).coeff j) +
        j • HahnSeries.addVal ℚ K (r' - r)

/--
@isnad1 id=le.1h4v.s9.20977bf1181d from=translated src=- shape=6a9bf431 vocab=a1d634bc
-/
theorem KaplanskySlope.addVal_eval_le {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskySlope f r r') :
    HahnSeries.addVal ℚ K (f.eval r) ≤ HahnSeries.addVal ℚ K (f.eval r') := by
  have hsum : HahnSeries.addVal ℚ K (f.eval r) ≤
      HahnSeries.addVal ℚ K (f.eval r' - f.eval r) := by
    rw [show f.eval r' - f.eval r = f.eval (r + (r' - r)) - f.eval r by ring_nf,
      eval_sub_eval_eq_sum_taylor]
    refine (HahnSeries.addVal ℚ K).map_le_sum fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · rw [ite_eq_right hpos.ne', (HahnSeries.addVal ℚ K).map_mul, (HahnSeries.addVal ℚ K).map_pow]
      exact h j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  calc HahnSeries.addVal ℚ K (f.eval r)
      ≤ min (HahnSeries.addVal ℚ K (f.eval r)) (HahnSeries.addVal ℚ K (f.eval r' - f.eval r)) :=
        le_min le_rfl hsum
    _ ≤ HahnSeries.addVal ℚ K (f.eval r + (f.eval r' - f.eval r)) :=
        (HahnSeries.addVal ℚ K).map_add _ _
    _ = HahnSeries.addVal ℚ K (f.eval r') := by ring_nf

/--
@isnad1 id=kaplansk.2h5v.s9.cd25289e9082 from=translated src=- shape=4e5a3599 vocab=17be27b0
-/
theorem KaplanskySlope.mono {f : (HahnSeries ℚ K)[X]} {r r' r'' : HahnSeries ℚ K}
    (h : KaplanskySlope f r r')
    (hle : HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r)) :
    KaplanskySlope f r r'' := by
  intro j hj hjle
  exact (h j hj hjle).trans
    (add_le_add le_rfl ((nsmul_le_nsmul_iff_withTop hj).mpr hle))

/--
@isnad1 id=ex.1h4v.s11.944f5dbf9840 from=translated src=- shape=9d17b2ed vocab=d4a35f27
-/
theorem exists_addVal_taylor_coeff_of_addVal_eval_lt {f : (HahnSeries ℚ K)[X]}
    {r r' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r')) :
    ∃ j, 1 ≤ j ∧ j ≤ f.natDegree ∧
      HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j) +
        j • HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (f.eval r) := by

  by_contra habs
  push Not at habs

  have hsum : HahnSeries.addVal ℚ K (f.eval r) <
      HahnSeries.addVal ℚ K (f.eval (r' + (r - r'))) := by
    rw [show f.eval (r' + (r - r')) = f.eval r' + (f.eval (r' + (r - r')) - f.eval r') by ring,
      eval_sub_eval_eq_sum_taylor]
    refine (HahnSeries.addVal ℚ K).map_lt_add hlt ?_
    refine (HahnSeries.addVal ℚ K).map_lt_sum (ne_of_lt (lt_of_lt_of_le hlt le_top)) fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa using lt_of_lt_of_le hlt le_top
    · rw [ite_eq_right hpos.ne', (HahnSeries.addVal ℚ K).map_mul, (HahnSeries.addVal ℚ K).map_pow,
        show r - r' = -(r' - r) by ring, (HahnSeries.addVal ℚ K).map_neg]
      exact habs j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [show r' + (r - r') = r by ring] at hsum
  exact lt_irrefl _ hsum

def KaplanskyLE (f : (HahnSeries ℚ K)[X]) (r r' : HahnSeries ℚ K) : Prop :=
  r = r' ∨ (HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r') ∧
    KaplanskySlope f r r')

/--
@isnad1 id=kaplansk.0h3v.s5.db8024730464 from=translated src=- shape=de086fcc vocab=22d4ceab
-/
theorem KaplanskyLE.refl (f : (HahnSeries ℚ K)[X]) (r : HahnSeries ℚ K) :
    KaplanskyLE f r r := Or.inl rfl

scoped instance (f : (HahnSeries ℚ K)[X]) : Std.Refl (KaplanskyLE f) := ⟨KaplanskyLE.refl f⟩

/--
@isnad1 id=le.1h4v.s9.dcd0759e55f9 from=translated src=- shape=6a9bf431 vocab=99a3a7e0
-/
theorem KaplanskyLE.addVal_eval_le {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') :
    HahnSeries.addVal ℚ K (f.eval r) ≤ HahnSeries.addVal ℚ K (f.eval r') := by
  rcases h with rfl | ⟨hlt, _⟩
  · exact le_rfl
  · exact hlt.le

/--
@isnad1 id=kaplansk.3h5v.s9.718101717ccf from=translated src=- shape=d65c07f9 vocab=d1e7bbd1
-/
theorem KaplanskySlope.of_kaplanskyLE_of_lt {f : (HahnSeries ℚ K)[X]}
    {r r' r'' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r'))
    (hslope : KaplanskySlope f r r') (h' : KaplanskyLE f r' r'') :
    KaplanskySlope f r r'' := by
  rcases h' with rfl | ⟨_, hslope'⟩
  · exact hslope
  obtain ⟨j₀, hj₀1, hj₀le, hj₀⟩ := exists_addVal_taylor_coeff_of_addVal_eval_lt hlt
  have hj₀' := hslope' j₀ hj₀1 hj₀le
  have hlt'' : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) +
        j₀ • HahnSeries.addVal ℚ K (r' - r) <
      HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) +
        j₀ • HahnSeries.addVal ℚ K (r'' - r') :=
    lt_of_le_of_lt hj₀ (lt_of_lt_of_le hlt hj₀')
  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) ≠ ⊤ := by
    intro htop; rw [htop, top_add, top_add] at hlt''; exact lt_irrefl _ hlt''
  have hηle : HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r') :=
    (nsmul_le_nsmul_iff_withTop hj₀1).mp (withTop_add_lt_add_left hbne hlt'').le
  refine hslope.mono ?_
  calc HahnSeries.addVal ℚ K (r' - r)
      = min (HahnSeries.addVal ℚ K (r' - r)) (HahnSeries.addVal ℚ K (r'' - r')) :=
        (min_eq_left hηle).symm
    _ ≤ HahnSeries.addVal ℚ K ((r' - r) + (r'' - r')) := (HahnSeries.addVal ℚ K).map_add _ _
    _ = HahnSeries.addVal ℚ K (r'' - r) := by ring_nf

/--
@isnad1 id=kaplansk.2h5v.s6.fd20d6c9d536 from=translated src=- shape=6969316e vocab=22d4ceab
-/
theorem KaplanskyLE.trans {f : (HahnSeries ℚ K)[X]} {r r' r'' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') (h' : KaplanskyLE f r' r'') : KaplanskyLE f r r'' := by
  rcases h with rfl | ⟨hlt, hslope⟩
  · exact h'
  exact Or.inr ⟨lt_of_lt_of_le hlt h'.addVal_eval_le, hslope.of_kaplanskyLE_of_lt hlt h'⟩

/--
@isnad1 id=eq.2h4v.s6.a5e8cb14fe90 from=translated src=- shape=7c3ffe5b vocab=22d4ceab
-/
theorem KaplanskyLE.antisymm {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') (h' : KaplanskyLE f r' r) : r = r' := by
  rcases h with rfl | ⟨hlt, _⟩
  · rfl
  rcases h' with rfl | ⟨hlt', _⟩
  · rfl
  exact absurd hlt (not_lt.mpr hlt'.le)

/--
@isnad1 id=ex.3h3v.s8.da18c6bb2f67 from=translated src=- shape=bf0b8362 vocab=e260ac21
-/
theorem exists_kaplanskyLE_of_eval_ne_zero [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {r : HahnSeries ℚ K} (hr : f.eval r ≠ 0) :
    ∃ r', r ≠ r' ∧ KaplanskyLE f r r' := by
  set g := Polynomial.taylor r f with hg
  have hgmonic : g.Monic := monic_taylor hf r
  have hgdeg : 1 ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hdeg
  have hg0 : g.coeff 0 ≠ 0 := by rw [hg, Polynomial.taylor_coeff_zero]; exact hr
  obtain ⟨γ, hslope, j₀, hj₀1, hj₀le, hj₀ne, hj₀eq⟩ := exists_evalNewtonSlope hgmonic hgdeg

  have hconst : (evalEdgeForm g γ).coeff 0 ≠ 0 := by
    rw [evalEdgeForm_coeff_zero]; exact HahnSeries.leadingCoeff_ne_zero.mpr hg0
  have hj₀coeff : (evalEdgeForm g γ).coeff j₀ ≠ 0 := by
    rw [evalEdgeForm_coeff_of_eq hj₀le hj₀eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hj₀ne
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (evalEdgeForm g γ)
    ((Polynomial.natDegree_pos_iff_degree_pos.mp
      (le_trans hj₀1 (Polynomial.le_natDegree_of_ne_zero hj₀coeff))).ne')
  have hcne : c ≠ 0 := fun hc0 => by
    rw [Polynomial.IsRoot, hc0, ← Polynomial.coeff_zero_eq_eval_zero] at hc; exact hconst hc

  have hvanish : ∀ q ≤ (g.coeff 0).order, (g.eval (HahnSeries.single γ c)).coeff q = 0 := by
    intro q hq
    rcases lt_or_eq_of_le hq with hlt' | heq
    · exact coeff_eval_single_of_lt_order_zero hslope c hlt'
    · subst heq; rw [coeff_eval_single_order_zero]; exact hc
  have heval0 : f.eval r = g.coeff 0 := by
    rw [hg, Polynomial.taylor_coeff_zero]
  have hltγ : HahnSeries.addVal ℚ K (f.eval r) <
      HahnSeries.addVal ℚ K (g.eval (HahnSeries.single γ c)) := by
    rw [heval0, HahnSeries.addVal_apply_of_ne hg0, HahnSeries.addVal_apply]
    rcases eq_or_ne (g.eval (HahnSeries.single γ c)) 0 with heq | hne
    · rw [heq, HahnSeries.orderTop_zero]; exact WithTop.coe_lt_top _
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_lt_coe]
      by_contra hle
      have hkey := hvanish (g.eval (HahnSeries.single γ c)).order (not_lt.mp hle)
      rw [← HahnSeries.leadingCoeff_eq] at hkey
      exact (HahnSeries.leadingCoeff_ne_zero.mpr hne) hkey
  have hevals : g.eval (HahnSeries.single γ c) = f.eval (r + HahnSeries.single γ c) := by
    rw [hg, Polynomial.taylor_eval, add_comm]
  refine ⟨r + HahnSeries.single γ c, fun heq => hcne ?_, Or.inr ⟨hevals ▸ hltγ, ?_⟩⟩
  · have h0 : (HahnSeries.single γ c : HahnSeries ℚ K) = 0 := by
      have heq' : r + HahnSeries.single γ c = r + (0 : HahnSeries ℚ K) := by
        rw [add_zero]; exact heq.symm
      exact add_left_cancel heq'
    exact HahnSeries.single_eq_zero_iff.mp h0
  ·
    intro j hj hjle
    rw [add_sub_cancel_left, heval0, HahnSeries.addVal_apply_of_ne hg0]
    rcases eq_or_ne ((Polynomial.taylor r f).coeff j) 0 with hzero | hne
    · rw [hzero, AddValuation.map_zero, top_add]; exact le_top
    · have hjle' : j ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hjle
      rw [HahnSeries.addVal_apply_of_ne hne, HahnSeries.addVal_apply,
        HahnSeries.orderTop_single hcne, ← hg, nsmul_coe_withTop]
      exact_mod_cast hslope j hj hjle' hne

/--
@isnad1 id=eq.3h3v.s7.f1c69ee7c862 from=translated src=- shape=c4dcf3ca vocab=e260ac21
-/
theorem eval_eq_zero_of_kaplanskyLE_max [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {m : HahnSeries ℚ K} (hmax : ∀ r, KaplanskyLE f m r → KaplanskyLE f r m) :
    f.eval m = 0 := by
  by_contra hm
  obtain ⟨r', hne, hle⟩ := exists_kaplanskyLE_of_eval_ne_zero hf hdeg hm
  exact hne (KaplanskyLE.antisymm hle (hmax r' hle))

section ChainUpperBound

variable {f : (HahnSeries ℚ K)[X]}

/--
@isnad1 id=injon.1h3v.s8.97f172ff2d58 from=translated src=- shape=52201aa7 vocab=f54764f9
-/
theorem kaplanskyChain_addVal_injOn {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    Set.InjOn (fun a => HahnSeries.addVal ℚ K (f.eval a)) C := by
  intro a ha b hb hab
  rcases hC.total ha hb with h | h
  · rcases h with rfl | ⟨hlt, _⟩
    exacts [rfl, absurd hab hlt.ne]
  · rcases h with rfl | ⟨hlt, _⟩
    exacts [rfl, absurd hab.symm hlt.ne]

@[reducible] def kaplanskyChainOrder {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    LinearOrder ↥C :=
  LinearOrder.lift' (fun a => HahnSeries.addVal ℚ K (f.eval (a : HahnSeries ℚ K)))
    (fun a b hab => Subtype.ext (kaplanskyChain_addVal_injOn hC a.2 b.2 hab))

def KaplanskyBelowSlope (f : (HahnSeries ℚ K)[X]) (a : HahnSeries ℚ K) (g : ℚ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ f.natDegree ∧
    HahnSeries.addVal ℚ K ((Polynomial.taylor a f).coeff j) + ((j • g : ℚ) : WithTop ℚ) <
      HahnSeries.addVal ℚ K (f.eval a)

private theorem nsmul_lt_nsmul_iff_withTop {j : ℕ} (hj : 1 ≤ j) {a b : WithTop ℚ} :
    j • a < j • b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, nsmul_le_nsmul_iff_withTop hj,
    nsmul_le_nsmul_iff_withTop hj]

/--
@isnad1 id=lt.2h5v.s8.a39af613cf01 from=translated src=- shape=a186d522 vocab=e2662d13
-/
theorem KaplanskyBelowSlope.lt_addVal_sub {a b : HahnSeries ℚ K} {g : ℚ}
    (hbelow : KaplanskyBelowSlope f a g) (hslope : KaplanskySlope f a b) :
    (g : WithTop ℚ) < HahnSeries.addVal ℚ K (b - a) := by
  obtain ⟨j, hj1, hjle, hjlt⟩ := hbelow
  have hj := hslope j hj1 hjle

  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor a f).coeff j) ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hjlt; exact not_top_lt hjlt
  have hlt : ((j • g : ℚ) : WithTop ℚ) < j • HahnSeries.addVal ℚ K (b - a) :=
    withTop_add_lt_add_left hbne (lt_of_lt_of_le hjlt hj)
  rw [← nsmul_coe_withTop] at hlt
  exact (nsmul_lt_nsmul_iff_withTop hj1).mp hlt

/--
@isnad1 id=eq.5h6v.s8.da52a6906dce from=translated src=- shape=13d010bc vocab=f21ad03b
-/
theorem kaplanskyChain_coeff_eq {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a b : HahnSeries ℚ K} (ha : a ∈ C) (hb : b ∈ C)
    {g : ℚ} (hga : KaplanskyBelowSlope f a g) (hgb : KaplanskyBelowSlope f b g) :
    a.coeff g = b.coeff g := by
  rcases hC.total ha hb with hab | hab
  · rcases hab with rfl | ⟨_, hslope⟩
    · rfl
    have hlt := hga.lt_addVal_sub hslope
    rw [HahnSeries.addVal_apply] at hlt
    have hdiff := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
    rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
    exact hdiff.symm
  · rcases hab with rfl | ⟨_, hslope⟩
    · rfl
    have hlt := hgb.lt_addVal_sub hslope
    rw [HahnSeries.addVal_apply] at hlt
    have hdiff := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
    rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
    exact hdiff

def kaplanskyLimitCoeff (C : Set (HahnSeries ℚ K)) (g : ℚ) : K :=
  if h : ∃ a ∈ C, KaplanskyBelowSlope f a g then h.choose.coeff g else 0

/--
@isnad1 id=eq.3h5v.s7.519898e0b8f8 from=translated src=- shape=499b81f7 vocab=81714c46
-/
theorem kaplanskyLimitCoeff_eq {C : Set (HahnSeries ℚ K)} (hC : IsChain (KaplanskyLE f) C)
    {a : HahnSeries ℚ K} (ha : a ∈ C) {g : ℚ} (hga : KaplanskyBelowSlope f a g) :
    kaplanskyLimitCoeff (f := f) C g = a.coeff g := by
  unfold kaplanskyLimitCoeff
  rw [dite_eq_left ⟨a, ha, hga⟩]
  obtain ⟨hb, hgb⟩ := (⟨a, ha, hga⟩ : ∃ a ∈ C, KaplanskyBelowSlope f a g).choose_spec
  exact kaplanskyChain_coeff_eq hC hb ha hgb hga

/--
@isnad1 id=ispwo.1h3v.s6.6e1e6b65d4b8 from=translated src=- shape=c3d673d3 vocab=c82ae253
-/
theorem kaplanskyLimitCoeff_isPWO_support {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    (Function.support (kaplanskyLimitCoeff (f := f) C)).IsPWO := by
  refine Set.IsWF.isPWO ?_
  rw [Set.isWF_iff_no_descending_seq]
  intro s hanti hs
  have hf0 : kaplanskyLimitCoeff (f := f) C (s 0) ≠ 0 := hs 0
  have hex : ∃ a ∈ C, KaplanskyBelowSlope f a (s 0) := by
    by_contra hnone; rw [kaplanskyLimitCoeff, dite_eq_right hnone] at hf0; exact hf0 rfl
  obtain ⟨a₀, ha₀, hga₀⟩ := hex

  have hsk : ∀ k, s k ∈ a₀.support := by
    intro k
    have hsk0 : s k ≤ s 0 := hanti.antitone (Nat.zero_le k)

    obtain ⟨j, hj1, hjle, hjlt⟩ := hga₀
    have hgak : KaplanskyBelowSlope f a₀ (s k) := ⟨j, hj1, hjle, by
      refine lt_of_le_of_lt ?_ hjlt
      gcongr
      exact_mod_cast nsmul_le_nsmul_right hsk0 j⟩
    have heq := kaplanskyLimitCoeff_eq hC ha₀ hgak
    rw [HahnSeries.mem_support, ← heq]
    exact hs k
  have hWF := a₀.isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hWF
  exact hWF s hanti hsk

def kaplanskyLimit {C : Set (HahnSeries ℚ K)} (hC : IsChain (KaplanskyLE f) C) :
    HahnSeries ℚ K where
  coeff := kaplanskyLimitCoeff (f := f) C
  isPWO_support' := kaplanskyLimitCoeff_isPWO_support hC

/--
@isnad1 id=kaplansk.2h4v.s7.1a5c95c66680 from=translated src=- shape=cc82281f vocab=80c349d1
-/
theorem kaplanskySlope_kaplanskyLimit {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a : HahnSeries ℚ K} (ha : a ∈ C) :
    KaplanskySlope f a (kaplanskyLimit hC) := by
  intro j hj hjle

  by_contra hlt
  push Not at hlt

  have hne : kaplanskyLimit hC - a ≠ 0 := by
    intro heq
    rw [heq, AddValuation.map_zero, nsmul_top_withTop hj, add_top] at hlt
    exact not_top_lt hlt
  set q : ℚ := (kaplanskyLimit hC - a).order with hq
  have hqval : HahnSeries.addVal ℚ K (kaplanskyLimit hC - a) = (q : WithTop ℚ) := by
    rw [HahnSeries.addVal_apply_of_ne hne, hq]
  rw [hqval, nsmul_coe_withTop] at hlt

  have hbelow : KaplanskyBelowSlope f a q := ⟨j, hj, hjle, hlt⟩

  have hcoeff : (kaplanskyLimit hC - a).coeff q = 0 := by
    rw [HahnSeries.coeff_sub]
    show kaplanskyLimitCoeff (f := f) C q - a.coeff q = 0
    rw [kaplanskyLimitCoeff_eq hC ha hbelow, sub_self]

  rw [hq, ← HahnSeries.leadingCoeff_eq] at hcoeff
  exact (HahnSeries.leadingCoeff_ne_zero.mpr hne) hcoeff

/--
@isnad1 id=ex.1h3v.s7.2111123431c0 from=translated src=- shape=9b74ecba vocab=0dabf2c0
-/
theorem exists_kaplanskyLE_upperBound {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    ∃ ub, ∀ a ∈ C, KaplanskyLE f a ub := by

  by_cases hmax : ∃ m ∈ C, ∀ a ∈ C, KaplanskyLE f a m
  · obtain ⟨m, _, hm⟩ := hmax; exact ⟨m, hm⟩
  push Not at hmax

  have hnomax : ∀ a ∈ C, ∃ b ∈ C, KaplanskyLE f a b ∧ a ≠ b := by
    intro a ha
    obtain ⟨b, hb, hnle⟩ := hmax a ha
    rcases hC.total ha hb with hab | hab
    · exact ⟨b, hb, hab, fun heq => hnle (heq ▸ KaplanskyLE.refl f a)⟩
    · exact absurd hab hnle

  refine ⟨kaplanskyLimit hC, fun a ha => ?_⟩
  obtain ⟨b, hb, hab, hne⟩ := hnomax a ha
  have hltab : HahnSeries.addVal ℚ K (f.eval a) < HahnSeries.addVal ℚ K (f.eval b) := by
    rcases hab with rfl | ⟨hlt, _⟩
    · exact absurd rfl hne
    · exact hlt
  refine Or.inr ⟨?_, kaplanskySlope_kaplanskyLimit hC ha⟩
  exact lt_of_lt_of_le hltab (kaplanskySlope_kaplanskyLimit hC hb).addVal_eval_le

end ChainUpperBound

/--
@isnad1 id=ex.2h2v.s7.f7fc7155f550 from=translated src=- shape=0b507f02 vocab=93d32f26
-/
theorem exists_isRoot_hahnSeries [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    ∃ r : HahnSeries ℚ K, f.IsRoot r := by
  obtain ⟨m, hmax⟩ := exists_maximal_of_chains_bounded
    (r := KaplanskyLE f) (fun C hC => exists_kaplanskyLE_upperBound hC)
    (fun {a b c} => KaplanskyLE.trans)
  exact ⟨m, eval_eq_zero_of_kaplanskyLE_max hf hdeg hmax⟩

/--
@isnad1 id=isalgclo.0h1v.s5.bf68b58599c0 from=translated src=- shape=72288e2b vocab=ae2255a3
-/
theorem isAlgClosed_hahnSeries_rat [IsAlgClosed K] : IsAlgClosed (HahnSeries ℚ K) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  have hdeg : 1 ≤ f.natDegree := by
    by_contra hlt
    have h1 : f = 1 := hf.natDegree_eq_zero.mp (Nat.lt_one_iff.mp (not_le.mp hlt))
    exact hirr.not_isUnit (h1 ▸ isUnit_one)
  exact exists_isRoot_hahnSeries hf hdeg

end DorgePuiseux
open scoped _root_.P2MW.S_HahnSeries_isAlgClosed_rat.DorgePuiseux

end
open scoped _root_.P2MW.S_HahnSeries_isAlgClosed_rat.DorgePuiseux

/--
@isnad1 id=isalgclo.0h1v.s5.bf68b58599c0 from=translated src=- shape=72288e2b vocab=ae2255a3
-/
theorem solution {K : Type*} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) :=
  DorgePuiseux.isAlgClosed_hahnSeries_rat
