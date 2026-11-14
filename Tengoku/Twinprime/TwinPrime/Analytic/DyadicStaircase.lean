import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact finite dyadic staircase identity

A nonincreasing natural boundary defines a finite staircase. Its weighted
sum equals a common rectangular baseline plus the rectangular corrections
at the internal nodes of a binary interval tree. Every boundary is retained
exactly; no approximation to a product cutoff is used.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- Rectangular corrections at all internal nodes of the dyadic interval
`[M,M+2^k)`. The last two arguments are the starting point and depth.-/
def dyadicStaircaseDetail (a b : ℕ → ℂ) (F : ℕ → ℕ) (M : ℕ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => dyadicStaircaseDetail a b F M k +
      dyadicStaircaseDetail a b F (M + 2 ^ k) k +
      (∑ m ∈ Ico M (M + 2 ^ k), a m) *
        (∑ n ∈ Ico (F (M + 2 ^ (k + 1) - 1)) (F (M + 2 ^ k - 1)), b n)

/-- The staircase identity for an arbitrary nonincreasing natural boundary.
All sums are finite, and a constant boundary makes every correction empty.-/
theorem sum_dyadic_staircase_eq (a b : ℕ → ℂ) (F : ℕ → ℕ) (M N k : ℕ)
    (hN : ∀ m ∈ Ico M (M + 2 ^ k), N ≤ F m)
    (hF : AntitoneOn F (Set.Ico M (M + 2 ^ k))) :
    (∑ m ∈ Ico M (M + 2 ^ k), a m * (∑ n ∈ Ico N (F m), b n)) =
      (∑ m ∈ Ico M (M + 2 ^ k), a m) *
        (∑ n ∈ Ico N (F (M + 2 ^ k - 1)), b n) +
          dyadicStaircaseDetail a b F M k := by
  induction k generalizing M with
  | zero => simp [dyadicStaircaseDetail]
  | succ k ih =>
      have hp : 0 < 2 ^ k := by positivity
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hend : (M + 2 ^ k) + 2 ^ k = M + 2 ^ (k + 1) := by omega
      have hNL : ∀ m ∈ Ico M (M + 2 ^ k), N ≤ F m := by
        intro m hm
        exact hN m (mem_Ico.mpr ⟨(mem_Ico.mp hm).1, by
          have := (mem_Ico.mp hm).2
          omega⟩)
      have hNR : ∀ m ∈ Ico (M + 2 ^ k) ((M + 2 ^ k) + 2 ^ k), N ≤ F m := by
        intro m hm
        exact hN m (mem_Ico.mpr ⟨by have := (mem_Ico.mp hm).1; omega,
          by have := (mem_Ico.mp hm).2; omega⟩)
      have hFL : AntitoneOn F (Set.Ico M (M + 2 ^ k)) := by
        apply hF.mono
        intro m hm
        exact ⟨hm.1, by have := hm.2; omega⟩
      have hFR : AntitoneOn F (Set.Ico (M + 2 ^ k) ((M + 2 ^ k) + 2 ^ k)) := by
        apply hF.mono
        intro m hm
        exact ⟨by have := hm.1; omega, by have := hm.2; omega⟩
      have hleft := ih M hNL hFL
      have hright := ih (M + 2 ^ k) hNR hFR
      rw [hend] at hright
      have hNlast : N ≤ F (M + 2 ^ (k + 1) - 1) :=
        hN _ (mem_Ico.mpr ⟨by omega, by omega⟩)
      have hboundary : F (M + 2 ^ (k + 1) - 1) ≤ F (M + 2 ^ k - 1) :=
        hF (show M + 2 ^ k - 1 ∈ Set.Ico M (M + 2 ^ (k + 1)) from
          ⟨by omega, by omega⟩)
          (show M + 2 ^ (k + 1) - 1 ∈ Set.Ico M (M + 2 ^ (k + 1)) from
            ⟨by omega, by omega⟩) (by omega)
      have hprefix := sum_Ico_consecutive b hNlast hboundary
      have hsplit := sum_Ico_consecutive
        (fun m => a m * (∑ n ∈ Ico N (F m), b n))
        (show M ≤ M + 2 ^ k by omega)
        (show M + 2 ^ k ≤ M + 2 ^ (k + 1) by omega)
      have hasplit := sum_Ico_consecutive a
        (show M ≤ M + 2 ^ k by omega)
        (show M + 2 ^ k ≤ M + 2 ^ (k + 1) by omega)
      rw [← hsplit, hleft, hright, ← hasplit, dyadicStaircaseDetail, ← hprefix]
      ring

@[simp] theorem dyadicStaircaseDetail_const (a b : ℕ → ℂ) (c M k : ℕ) :
    dyadicStaircaseDetail a b (fun _ => c) M k = 0 := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih => simp [dyadicStaircaseDetail, ih]

/-- The exact half-open boundary of `m*n ≤ T` inside `[N,N+K)`.-/
def productCutoffBoundary (T N K m : ℕ) : ℕ :=
  min (N + K) (max N (T / m + 1))

theorem le_productCutoffBoundary (T N K m : ℕ) :
    N ≤ productCutoffBoundary T N K m :=
  le_min (Nat.le_add_right N K) (le_max_left _ _)

theorem productCutoffBoundary_le (T N K m : ℕ) :
    productCutoffBoundary T N K m ≤ N + K := min_le_left _ _

/-- Increasing a positive first factor decreases the clamped boundary.-/
theorem productCutoffBoundary_antitone (T N K m r : ℕ) (hm : 0 < m) (hmr : m ≤ r) :
    productCutoffBoundary T N K r ≤ productCutoffBoundary T N K m := by
  have hdiv : T / r ≤ T / m := by
    apply (Nat.le_div_iff_mul_le hm).mpr
    exact (Nat.mul_le_mul_left (T / r) hmr).trans (Nat.div_mul_le_self T r)
  exact min_le_min le_rfl (max_le_max le_rfl (Nat.add_le_add_right hdiv 1))

theorem productCutoffBoundary_antitoneOn (T N K M R : ℕ) (hM : 0 < M) :
    AntitoneOn (productCutoffBoundary T N K) (Set.Ico M R) := by
  intro m hm r _ hmr
  exact productCutoffBoundary_antitone T N K m r (hM.trans_le hm.1) hmr

/-- Membership below the boundary retains the exact integer product cutoff.
The second factor may be zero; no positivity of T or N is needed.-/
theorem lt_productCutoffBoundary_iff (T N K m n : ℕ) (hm : 0 < m)
    (hn : n ∈ Ico N (N + K)) :
    n < productCutoffBoundary T N K m ↔ m * n ≤ T := by
  have hlt : n < productCutoffBoundary T N K m ↔ n ≤ T / m := by
    simp only [productCutoffBoundary, lt_min_iff, lt_max_iff]
    have := (mem_Ico.mp hn).1
    have := (mem_Ico.mp hn).2
    omega
  exact hlt.trans (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm))

/-- The filtered row of a product cutoff is exactly a natural interval.-/
theorem filter_Ico_productCutoff_eq (T N K m : ℕ) (hm : 0 < m) :
    (Ico N (N + K)).filter (fun n => m * n ≤ T) =
      Ico N (productCutoffBoundary T N K m) := by
  ext n
  simp only [mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨hnN, hnK⟩, hprod⟩
    exact ⟨hnN, (lt_productCutoffBoundary_iff T N K m n hm
      (mem_Ico.mpr ⟨hnN, hnK⟩)).mpr hprod⟩
  · rintro ⟨hnN, hnF⟩
    have hnK : n < N + K := hnF.trans_le (productCutoffBoundary_le T N K m)
    exact ⟨⟨hnN, hnK⟩, (lt_productCutoffBoundary_iff T N K m n hm
      (mem_Ico.mpr ⟨hnN, hnK⟩)).mp hnF⟩

/-- Exact product-cutoff specialization of the dyadic staircase identity.
It includes endpoint T=0 and empty second-factor intervals.-/
theorem sum_dyadic_productCutoff_eq (a b : ℕ → ℂ) (T M N K k : ℕ) (hM : 0 < M) :
    (∑ m ∈ Ico M (M + 2 ^ k),
      ∑ n ∈ Ico N (N + K) with m * n ≤ T, a m * b n) =
      (∑ m ∈ Ico M (M + 2 ^ k), a m) *
        (∑ n ∈ Ico N (productCutoffBoundary T N K (M + 2 ^ k - 1)), b n) +
          dyadicStaircaseDetail a b (productCutoffBoundary T N K) M k := by
  calc
    _ = ∑ m ∈ Ico M (M + 2 ^ k),
        a m * (∑ n ∈ Ico N (productCutoffBoundary T N K m), b n) := by
      apply sum_congr rfl
      intro m hm
      rw [filter_Ico_productCutoff_eq T N K m (hM.trans_le (mem_Ico.mp hm).1), mul_sum]
    _ = _ := sum_dyadic_staircase_eq a b (productCutoffBoundary T N K) M N k
      (fun m _ => le_productCutoffBoundary T N K m)
      (productCutoffBoundary_antitoneOn T N K M (M + 2 ^ k) hM)

end TwinPrime.Analytic
