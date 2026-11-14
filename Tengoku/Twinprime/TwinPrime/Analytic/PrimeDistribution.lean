import Tengoku.Twinprime.TwinPrime.Analytic.Decomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite progression errors and a named distribution obligation

`progressionPsi t q a` sums von Mangoldt over positive integers at most `t`
in the residue class `a mod q`. Endpoints are natural numbers. The finite
maximal error includes every integer endpoint from zero to its stated bound
and every canonical reduced residue class. `MaximalBombieriVinogradov` is a
named hypothesis, not a proved theorem or an axiom.

The finite interval identities hold for all moduli. The error estimates used
for the main term are explicitly restricted to odd moduli, where the residue
class of two is reduced. Even-modulus contributions require separate bounds.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- The positive-integer von Mangoldt sum in one arithmetic progression.-/
def progressionPsi (t q a : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 t with Nat.ModEq q m a, vonMangoldt m

/-- Error from the reduced-residue main term, with all divisions in `ℝ`.-/
def progressionError (t q a : ℕ) : ℝ :=
  progressionPsi t q a - (t : ℝ) / Nat.totient q

/-- The finite maximal error up to endpoint `T`. The extra index `a=q`
contributes zero, making the maximum nonempty even for the unused modulus zero.-/
def progressionMaxError (T q : ℕ) : ℝ :=
  ((range (T + 1)).product (range (q + 1))).sup'
    (by exact ⟨(0, 0), mem_product.mpr ⟨mem_range.mpr (Nat.succ_pos T),
      mem_range.mpr (Nat.succ_pos q)⟩⟩)
    (fun ta => if ta.2 < q ∧ Nat.Coprime ta.2 q then
      |progressionError ta.1 q ta.2| else 0)

/-- Integer-endpoint maximal Bombieri–Vinogradov input. This proposition is
unproved here. The real exponents, constants, threshold, and admissible integer
modulus limits are all quantified explicitly.-/
def MaximalBombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ B →
      (∑ q ∈ Icc 1 Q, progressionMaxError (2 * X + 2) q) ≤
        K * X / (Real.log X) ^ A

theorem progressionMaxError_nonneg (T q : ℕ) : 0 ≤ progressionMaxError T q := by
  have hmem : (0, q) ∈ (range (T + 1)).product (range (q + 1)) :=
    mem_product.mpr ⟨mem_range.mpr (Nat.succ_pos T), mem_range.mpr (Nat.lt_succ_self q)⟩
  have h := Finset.le_sup' (f := fun ta : ℕ × ℕ =>
    if ta.2 < q ∧ Nat.Coprime ta.2 q then |progressionError ta.1 q ta.2| else 0) hmem
  simpa only [lt_irrefl, false_and, ite_false, progressionMaxError] using h

theorem abs_progressionError_le_max {t T q a : ℕ} (ht : t ≤ T) (ha : a < q)
    (hcop : Nat.Coprime a q) : |progressionError t q a| ≤ progressionMaxError T q := by
  have hmem : (t, a) ∈ (range (T + 1)).product (range (q + 1)) :=
    mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩
  have h := Finset.le_sup' (f := fun ta : ℕ × ℕ =>
    if ta.2 < q ∧ Nat.Coprime ta.2 q then |progressionError ta.1 q ta.2| else 0) hmem
  change (if a < q ∧ Nat.Coprime a q then |progressionError t q a| else 0) ≤ _ at h
  rw [ite_eq_left ⟨ha, hcop⟩] at h
  exact h

/-- Ordinary cumulative endpoint subtraction, including endpoint zero.-/
theorem progressionPsi_sub (l h q a : ℕ) (hlh : l ≤ h) :
    progressionPsi h q a - progressionPsi l q a =
      ∑ m ∈ Ioc l h with Nat.ModEq q m a, vonMangoldt m := by
  have hsub : (Ioc 0 l).filter (fun m => Nat.ModEq q m a) ⊆
      (Ioc 0 h).filter (fun m => Nat.ModEq q m a) := by
    intro m hm
    obtain ⟨hmI, hma⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hmI).1,
      (mem_Ioc.mp hmI).2.trans hlh⟩, hma⟩
  have hset : (Ioc 0 h).filter (fun m => Nat.ModEq q m a) \
      (Ioc 0 l).filter (fun m => Nat.ModEq q m a) =
      (Ioc l h).filter (fun m => Nat.ModEq q m a) := by
    apply Finset.ext
    intro m
    simp only [Finset.mem_sdiff, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hm0, hmh⟩, hma⟩, hnot⟩
      refine ⟨⟨?_, hmh⟩, hma⟩
      by_contra hml
      exact hnot ⟨⟨hm0, by omega⟩, hma⟩
    · rintro ⟨⟨hlm, hmh⟩, hma⟩
      refine ⟨⟨⟨by omega, hmh⟩, hma⟩, ?_⟩
      rintro ⟨⟨_, hml⟩, _⟩
      omega
  unfold progressionPsi
  rw [← sum_sdiff hsub, hset, add_sub_cancel_right]

/-- Exact shifted interval conversion; both endpoints use the same residue class.-/
theorem shiftedProgression_eq_psi_sub (X q : ℕ) :
    (∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)) =
      progressionPsi (2 * X + 2) q 2 - progressionPsi (X + 2) q 2 := by
  rw [progressionPsi_sub _ _ _ _ (by omega)]
  apply sum_bij (fun n _ => n + 2)
  · intro n hn
    obtain ⟨hnI, hqn⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨?_, Nat.add_modEq_right_iff.mpr hqn⟩
    simp only [mem_Ioc] at hnI ⊢
    omega
  · intro n _ m _ h
    omega
  · intro m hm
    obtain ⟨hmI, hmcong⟩ := mem_filter.mp hm
    have hm := mem_Ioc.mp hmI
    have heq : m - 2 + 2 = m := by omega
    refine ⟨m - 2, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩, heq⟩
    have hcong : Nat.ModEq q (m - 2 + 2) 2 := by simpa only [heq] using hmcong
    exact Nat.add_modEq_right_iff.mp hcong
  · intro n _
    rfl

/-- The exact error after subtracting the dyadic main term.-/
theorem shiftedProgression_sub_main_eq_errors (X q : ℕ) :
    (∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)) -
        (X : ℝ) / Nat.totient q =
      progressionError (2 * X + 2) q 2 - progressionError (X + 2) q 2 := by
  rw [shiftedProgression_eq_psi_sub]
  unfold progressionError
  push_cast
  ring

end TwinPrime.Analytic
