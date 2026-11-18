import Tengoku.TusnadyLean.Oscillation.Model
import Tengoku.TusnadyLean.Oscillation.Rademacher
import Tengoku.Seed.Order.Interval.Finset.Fin
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Oscillation
noncomputable section
open scoped BigOperators
open Finset

def halfDigit (d : ℕ) (_hd : 0 < d) (ξ : Bool) (s : Fin d) : Fin (2 * d) :=
  if ξ then ⟨s.val, by omega⟩ else ⟨d + s.val, by omega⟩

def rowMean (d : ℕ) (k : Fin (2 * d)) : ℝ := (k.val + 1 / 2 : ℝ) / (2 * d)

def halfGain (d : ℕ) (k : Fin (2 * d)) : ℝ := min (rowMean d k) (1 - rowMean d k)

/--
@isnad1 id=le.0h2v.s4.6e3df41d7d6d from=translated src=- shape=e06a2447 vocab=ad0faac7
-/
lemma rowMean_nonneg (d : ℕ) (k : Fin (2 * d)) : 0 ≤ rowMean d k := by
  unfold rowMean; positivity

/--
@isnad1 id=le.1h2v.s5.87f06ecd8e59 from=translated src=- shape=da5da6a4 vocab=1fe7363f
-/
lemma rowMean_le_one (d : ℕ) (hd : 0 < d) (k : Fin (2 * d)) : rowMean d k ≤ 1 := by
  have h : (k.val : ℝ) + 1 ≤ 2 * d := by exact_mod_cast k.isLt
  unfold rowMean
  apply (div_le_one (by positivity)).mpr
  linarith

/--
@isnad1 id=le.1h2v.s5.7df91cd592f6 from=translated src=- shape=c2dd8fdd vocab=62140f44
-/
lemma halfGain_nonneg (d : ℕ) (hd : 0 < d) (k : Fin (2 * d)) : 0 ≤ halfGain d k := by
  exact le_min (rowMean_nonneg d k) (sub_nonneg.mpr (rowMean_le_one d hd k))

/--
@isnad1 id=eq.2h2v.s5.399d4977a121 from=translated src=- shape=884bc7e5 vocab=11c6fa57
-/
lemma halfGain_left (d : ℕ) (hd : 0 < d) (k : Fin (2 * d)) (hk : k.val < d) :
    halfGain d k = rowMean d k := by
  unfold halfGain
  apply min_eq_left
  have h : (k.val : ℝ) + 1 ≤ d := by exact_mod_cast hk
  have hr : rowMean d k ≤ 1 / 2 := by
    unfold rowMean
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  linarith

/--
@isnad1 id=eq.2h2v.s6.bfa574bc3546 from=translated src=- shape=e5273513 vocab=0df656fa
-/
lemma halfGain_right (d : ℕ) (hd : 0 < d) (k : Fin (2 * d)) (hk : d ≤ k.val) :
    halfGain d k = 1 - rowMean d k := by
  unfold halfGain
  apply min_eq_right
  have h : (d : ℝ) ≤ k.val := by exact_mod_cast hk
  have hr : 1 / 2 ≤ rowMean d k := by
    unfold rowMean
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  linarith

/--
@isnad1 id=eq.0h2v.s5.4ef58585c81c from=translated src=- shape=ae0874a5 vocab=ad317639
-/
lemma sum_endpointWeight_inside {d : ℕ} (k : Fin d) :
    (∑ r : Fin d, endpointWeight r.val k.val) = k.val + (1 / 2 : ℝ) := by
  have hs : (∑ r : Fin d, if r.val < k.val then (1 : ℝ) else 0) = k.val := by
    have hset : Finset.univ.filter (fun r : Fin d ↦ r.val < k.val) = Finset.Iio k := by
      ext r; simp
    simp only [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one, hset, Fin.card_Iio]
  have he : (∑ r : Fin d, if r.val = k.val then (1 / 2 : ℝ) else 0) = 1 / 2 := by
    simp only [Fin.val_inj]
    simp
  simp only [endpointWeight, sum_add_distrib, hs, he]

/--
@isnad1 id=eq.1h3v.s6.27df7e9d2538 from=translated src=- shape=ea43ac5d vocab=2d5c53ff
-/
lemma halfDigit_mean (d : ℕ) (hd : 0 < d) (ξ : Bool) (k : Fin (2 * d)) :
    finAvg (fun s : Fin d ↦ endpointWeight (halfDigit d hd ξ s).val k.val) =
      rowMean d k + halfGain d k * boolSign ξ := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_cases hk : k.val < d
  · rw [halfGain_left d hd k hk]
    cases ξ
    · have hzero : (fun s : Fin d ↦ endpointWeight (halfDigit d hd false s).val k.val) =
          (fun _ ↦ (0 : ℝ)) := by
        funext s
        have hlt : ¬d + s.val < k.val := by omega
        have heq : d + s.val ≠ k.val := by omega
        simp [halfDigit, endpointWeight, hlt, heq]
      rw [hzero, finAvg_const]
      simp [boolSign]
    · change finAvg (fun s : Fin d ↦ endpointWeight s.val k.val) = _
      unfold finAvg
      rw [sum_endpointWeight_inside (⟨k.val, hk⟩ : Fin d)]
      simp only [Fintype.card_fin, boolSign, ↓reduceIte, mul_one, rowMean]
      field_simp
      ring
  · have hk' : d ≤ k.val := by omega
    rw [halfGain_right d hd k hk']
    cases ξ
    · have hv : ∀ s : Fin d,
          endpointWeight (halfDigit d hd false s).val k.val = endpointWeight s.val (k.val - d) := by
        intro s
        have hlt : d + s.val < k.val ↔ s.val < k.val - d := by omega
        have heq : d + s.val = k.val ↔ s.val = k.val - d := by omega
        simp [halfDigit, endpointWeight, hlt, heq]
      simp_rw [hv]
      unfold finAvg
      rw [sum_endpointWeight_inside (⟨k.val - d, by omega⟩ : Fin d)]
      simp only [Fintype.card_fin, boolSign, Bool.false_eq_true, ↓reduceIte, rowMean]
      rw [Nat.cast_sub hk']
      field_simp
      ring
    · have hone : (fun s : Fin d ↦ endpointWeight (halfDigit d hd true s).val k.val) =
          (fun _ ↦ (1 : ℝ)) := by
        funext s
        have hlt : s.val < k.val := by omega
        have heq : s.val ≠ k.val := by omega
        simp [halfDigit, endpointWeight, hlt, heq]
      rw [hone, finAvg_const]
      simp [boolSign]

def halfDigitEquiv (d : ℕ) (hd : 0 < d) : Bool × Fin d ≃ Fin (2 * d) where
  toFun x := halfDigit d hd x.1 x.2
  invFun k := if hk : k.val < d then (true, ⟨k.val, hk⟩)
    else (false, ⟨k.val - d, by omega⟩)
  left_inv := by
    intro x
    rcases x with ⟨ξ, s⟩
    cases ξ <;> simp [halfDigit, s.isLt]
  right_inv := by
    intro k
    dsimp only
    split_ifs with h
    · simp [halfDigit]
    · simp only [halfDigit, Bool.false_eq_true, ↓reduceIte]
      apply Fin.ext; dsimp; omega

/--
@isnad1 id=eq.1h3v.s7.50ff27d7a6d3 from=translated src=- shape=98e9ca70 vocab=83c57549
-/
lemma halfDigits_finAvg {n : ℕ} (d : ℕ) (hd : 0 < d)
    (F : (Fin n → Fin (2 * d)) → ℝ) :
    finAvg F = finAvg (fun ξ : Fin n → Bool ↦ finAvg (fun ρ : Fin n → Fin d ↦
      F (fun i ↦ halfDigit d hd (ξ i) (ρ i)))) := by
  let e := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ Bool) (fun _ ↦ Fin d)).symm.trans
    (Equiv.piCongrRight (fun _ ↦ halfDigitEquiv d hd))
  rw [← finAvg_equiv e F, finAvg_prod]
  rfl

/--
@isnad1 id=eq.0h4v.s5.be531aecf36a from=translated src=- shape=528e93d9 vocab=8d708198
-/
lemma finAvg_eval {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → ℝ) : finAvg (fun x : ι → α ↦ f (x i)) = finAvg f := by
  classical
  let e := (Equiv.funSplitAt i α).symm
  rw [← finAvg_equiv e (fun x : ι → α ↦ f (x i)), finAvg_prod]
  simp [e, Equiv.funSplitAt, Equiv.piSplitAt]

/--
@isnad1 id=eq.1h1v.s6.3186cf2e8310 from=translated src=- shape=cae46dab vocab=1ee14a72
-/
lemma sum_halfGain (d : ℕ) (hd : 0 < d) :
    (∑ k : Fin (2 * d), halfGain d k) = (2 * d : ℕ) / (4 : ℝ) := by
  have he := (halfDigitEquiv d hd).sum_comp (halfGain d)
  rw [← he, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, halfDigitEquiv, Equiv.coe_fn_mk]
  rw [← Finset.sum_add_distrib]
  have hp : ∀ s : Fin d,
      halfGain d (halfDigit d hd true s) + halfGain d (halfDigit d hd false s) = 1 / 2 := by
    intro s
    rw [halfGain_right d hd (halfDigit d hd false s) (by simp [halfDigit]),
      halfGain_left d hd (halfDigit d hd true s) (by simp [halfDigit])]
    simp only [rowMean, halfDigit, Bool.false_eq_true, ↓reduceIte, Nat.cast_add]
    field_simp
    ring
  simp_rw [hp]
  simp
  ring

/--
@isnad1 id=eq.1h1v.s7.28d927ef5a9d from=translated src=- shape=78d4992e vocab=684aa78e
-/
lemma matrix_double_mean (d : ℕ) (hd : 0 < d) :
    finAvg (fun k : Fin (2 * d) ↦ finAvg
      (fun r : Fin (2 * d) ↦ endpointWeight r.val k.val)) = 1 / 2 := by
  let : Nonempty (Fin (2 * d)) := ⟨⟨0, by omega⟩⟩
  have hsym (k r : Fin (2 * d)) : endpointWeight r.val k.val + endpointWeight k.val r.val = 1 := by
    unfold endpointWeight
    split_ifs <;> norm_num at * <;> omega
  have hcomm : finAvg (fun k : Fin (2 * d) ↦ finAvg (fun r : Fin (2 * d) ↦ endpointWeight k.val r.val)) =
      finAvg (fun k : Fin (2 * d) ↦ finAvg (fun r : Fin (2 * d) ↦ endpointWeight r.val k.val)) := by
    unfold finAvg
    simp only [← Finset.sum_div]
    rw [Finset.sum_comm]
  have he : finAvg (fun k : Fin (2 * d) ↦ finAvg (fun r : Fin (2 * d) ↦
      endpointWeight r.val k.val + endpointWeight k.val r.val)) = 1 := by
    simp_rw [hsym, finAvg_const]
  simp_rw [finAvg_add] at he
  rw [hcomm] at he
  linarith

end
end Oscillation
