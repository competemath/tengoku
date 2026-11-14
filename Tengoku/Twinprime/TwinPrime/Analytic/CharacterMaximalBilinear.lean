import Tengoku.Twinprime.TwinPrime.Analytic.DyadicStaircaseFirstMoment
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterMaximalLargeSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal product-cutoff primitive-character bilinear sums

The exact clamped staircase identity and the proved fixed-interval large
sieve give a bilinear first moment on a dyadic box. Every character may
select its own natural product cutoff. Selecting actual finite maximizers
then puts the maximum inside the primitive-character sum.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- A character-twisted bilinear sum on a dyadic box with the exact product cutoff.-/
def characterProductCutoffSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (M N k j t : ℕ) : ℂ :=
  ∑ m ∈ Ico M (M + 2 ^ k),
    ∑ n ∈ Ico N (N + 2 ^ j) with m * n ≤ t, a m * b n * χ (m * n)

/-- Multiplicativity and the exact filtered-row identity give a staircase.
Only the first coordinate's starting point needs to be positive.
@isnad1 id=eq.1h9v.s7.00c208e6dd2c from=translated src=- shape=0674778b vocab=197b07d1
-/
theorem characterProductCutoffSum_eq_staircase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (M N k j t : ℕ) (hM : 0 < M) :
    characterProductCutoffSum χ a b M N k j t =
      ∑ m ∈ Ico M (M + 2 ^ k), (a m * χ m) *
        ∑ n ∈ Ico N (productCutoffBoundary t N (2 ^ j) m), b n * χ n := by
  unfold characterProductCutoffSum
  apply sum_congr rfl
  intro m hm
  rw [filter_Ico_productCutoff_eq t N (2 ^ j) m (hM.trans_le (mem_Ico.mp hm).1), mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [map_mul]
  ring

/-- The full baseline and internal-node decomposition of the twisted sum.
@isnad1 id=eq.1h9v.s8.64384b8fb804 from=translated src=- shape=4a531bdf vocab=ce47b0e7
-/
theorem characterProductCutoffSum_eq_baseline_add_detail {q : ℕ}
    (χ : DirichletCharacter ℂ q) (a b : ℕ → ℂ) (M N k j t : ℕ) (hM : 0 < M) :
    characterProductCutoffSum χ a b M N k j t =
      (∑ m ∈ Ico M (M + 2 ^ k), a m * χ m) *
        (∑ n ∈ Ico N (productCutoffBoundary t N (2 ^ j) (M + 2 ^ k - 1)), b n * χ n) +
          dyadicStaircaseDetail (fun m => a m * χ m) (fun n => b n * χ n)
            (productCutoffBoundary t N (2 ^ j)) M k := by
  rw [characterProductCutoffSum_eq_staircase χ a b M N k j t hM]
  exact sum_dyadic_staircase_eq (fun m => a m * χ m) (fun n => b n * χ n)
    (productCutoffBoundary t N (2 ^ j)) M N k
    (fun m _ => le_productCutoffBoundary t N (2 ^ j) m)
    (productCutoffBoundary_antitoneOn t N (2 ^ j) M (M + 2 ^ k) hM)

/-- The maximum norm over the finite endpoint set `0 ≤ t ≤ T`.-/
def characterProductCutoffMax {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (M N k j T : ℕ) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterProductCutoffSum χ a b M N k j t‖)

end TwinPrime.Analytic
