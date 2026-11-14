import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.BrunHooleySieve
import Tengoku.Twinprime.TwinPrime.Sieve.Rankin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Brun–Hooley sieve: main term and remainder

Starting from `siftedSum_ge_brunHooley`, we bound

* the block main sums: `|S_j − V_j| ≤ tail_j` and `0 ≤ T_j ≤ tail_j`, where
  `S_j = ∑_{d ∣ P_j} μ_{2k_j}(d) ν(d)`, `T_j = ∑_{d ∣ P_j, ω d = 2k_j+1} ν(d)`,
  `V_j = ∏_{p ∣ P_j} (1 − ν p)`, `tail_j = ∑_{d ∣ P_j, ω d ≥ 2k_j+1} ν(d)`;
* the elementary inequality `∏ S_j − ∑_j T_j ∏_{i≠j} S_i ≥ (∏ V_j)/2` when `tail_j ≤ ε_j V_j`
  and `∑ ε_j ≤ 1/8` (`main_term_ge`);
* the remainder, by `|R_d| ≤ ρ(d)` for a multiplicative `ρ`, giving
  `(r + 1) ∏_j ∑_{d ∣ P_j, ω d ≤ 2k_j+1} ρ(d)`.

The result is the **general Brun–Hooley lower bound** `siftedSum_ge_of_blocks`:

  `siftedSum ≥ X · (∏_j V_j) / 2 − (r + 1) ∏_j ∑_{d ∣ P_j, ω d ≤ 2k_j+1} ρ(d)`.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### Block main sums -/

/--
@isnad1 id=le.0h1v.s5.a8486b80afb2 from=translated src=- shape=24c36ad6 vocab=0625ec87
-/
theorem abs_moebius_le_one' (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, abs_moebius]
  split_ifs <;> norm_num

/-- `|S_j − V_j| ≤ tail_j`.
@isnad1 id=le.3h3v.s7.f518fb4da7d1 from=translated src=- shape=2f3f7930 vocab=d3265dfa
-/
theorem abs_sum_truncMoebius_mul_sub_prod_le (ν : ArithmeticFunction ℝ) (hν : ν.IsMultiplicative)
    (hν0 : ∀ d, 0 ≤ ν d) {Pj : ℕ} (hPj : Squarefree Pj) (m : ℕ) :
    |∑ d ∈ Pj.divisors, truncMoebius m d * ν d - ∏ p ∈ Pj.primeFactors, (1 - ν p)| ≤
      ∑ d ∈ Pj.divisors with m + 1 ≤ ω d, ν d := by
  rw [IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree ν hν hPj]
  have key : ∑ d ∈ Pj.divisors, truncMoebius m d * ν d - ∑ d ∈ Pj.divisors, (μ d : ℝ) * ν d =
      -∑ d ∈ Pj.divisors with m + 1 ≤ ω d, (μ d : ℝ) * ν d := by
    rw [← sum_sub_distrib, ← sum_filter_add_sum_filter_not Pj.divisors (fun d => ω d ≤ m)]
    have h1 : ∑ d ∈ Pj.divisors with ω d ≤ m, (truncMoebius m d * ν d - μ d * ν d) = 0 := by
      apply sum_eq_zero
      intro d hd
      rw [mem_filter] at hd
      unfold truncMoebius
      rw [ite_eq_left hd.2]
      ring
    have hset : (Pj.divisors.filter fun d => ¬ ω d ≤ m) =
        Pj.divisors.filter fun d => m + 1 ≤ ω d := by
      apply Finset.filter_congr
      intro d _
      omega
    rw [h1, zero_add, hset, ← sum_neg_distrib]
    apply sum_congr rfl
    intro d hd
    rw [mem_filter] at hd
    unfold truncMoebius
    rw [ite_eq_right (by omega)]
    ring
  rw [key, abs_neg]
  calc |∑ d ∈ Pj.divisors with m + 1 ≤ ω d, (μ d : ℝ) * ν d|
      ≤ ∑ d ∈ Pj.divisors with m + 1 ≤ ω d, |(μ d : ℝ) * ν d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Pj.divisors with m + 1 ≤ ω d, ν d := by
        apply sum_le_sum
        intro d _
        rw [abs_mul, abs_of_nonneg (hν0 d)]
        have := abs_moebius_le_one' d
        nlinarith [hν0 d, abs_nonneg ((μ d : ℝ))]

/-- The defective block sum is `∑_{d ∣ P_j, ω d = 2k+1} ν d`, hence between `0` and `tail_j`.
@isnad1 id=and.2h3v.s8.c398025516a9 from=translated src=- shape=334a47e0 vocab=173ddb71
-/
theorem sum_defect_mul_nu_bounds (ν : ArithmeticFunction ℝ) (hν0 : ∀ d, 0 ≤ ν d) {Pj : ℕ}
    (hPj : Squarefree Pj) (k : ℕ) :
    0 ≤ ∑ d ∈ Pj.divisors, (truncMoebius (2 * k) d - truncMoebius (2 * k + 1) d) * ν d ∧
    ∑ d ∈ Pj.divisors, (truncMoebius (2 * k) d - truncMoebius (2 * k + 1) d) * ν d ≤
      ∑ d ∈ Pj.divisors with 2 * k + 1 ≤ ω d, ν d := by
  have hterm : ∀ d ∈ Pj.divisors,
      (truncMoebius (2 * k) d - truncMoebius (2 * k + 1) d) * ν d =
        if ω d = 2 * k + 1 then ν d else 0 := by
    intro d hd
    have hdsq : Squarefree d := hPj.squarefree_of_dvd (dvd_of_mem_divisors hd)
    unfold truncMoebius
    by_cases h : ω d = 2 * k + 1
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h]
      have hμ : (μ d : ℝ) = -1 := by
        rw [moebius_apply_of_squarefree hdsq,
          ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hdsq.ne_zero).mpr hdsq, h]
        push_cast
        rw [pow_succ, pow_mul]
        simp
      rw [hμ]
      ring
    · rw [ite_eq_right h]
      by_cases h2 : ω d ≤ 2 * k
      · rw [ite_eq_left h2, ite_eq_left (by omega)]; ring
      · rw [ite_eq_right h2, ite_eq_right (by omega)]; ring
  rw [sum_congr rfl hterm, ← sum_filter]
  constructor
  · exact sum_nonneg fun d _ => hν0 d
  · apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [mem_filter] at hd ⊢
      exact ⟨hd.1, by omega⟩
    · intro d _ _
      exact hν0 d

/-! ### The main-term inequality -/

/-- Weierstrass: `1 − ∑ ε ≤ ∏ (1 − ε)` for `0 ≤ ε ≤ 1`.
@isnad1 id=le.2h3v.s6.ffe3238ce153 from=translated src=- shape=77868c6c vocab=ae5e4e6e
-/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (ε : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ ε i) (h1 : ∀ i ∈ s, ε i ≤ 1) :
    1 - ∑ i ∈ s, ε i ≤ ∏ i ∈ s, (1 - ε i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have ha0 := h0 a (mem_insert_self a s)
    have ha1 := h1 a (mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, ε i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 - ε a),
      mul_nonneg ha0 hs0]

/-- If `|S_j − V_j| ≤ ε_j V_j`, `0 ≤ T_j ≤ ε_j V_j`, `V_j > 0`, `ε_j ≥ 0` and `∑ ε_j ≤ 1/8`, then
`∏ S_j − ∑_j T_j ∏_{i ≠ j} S_i ≥ (∏ V_j) / 2`.
@isnad1 id=le.6h5v.s8.2bfe61a7df66 from=translated src=- shape=fc3082fb vocab=005abab1
-/
theorem main_term_ge {r : ℕ} (S T V ε : Fin r → ℝ) (hV : ∀ j, 0 < V j) (hε : ∀ j, 0 ≤ ε j)
    (hS : ∀ j, |S j - V j| ≤ ε j * V j) (_hT0 : ∀ j, 0 ≤ T j) (hT : ∀ j, T j ≤ ε j * V j)
    (hsum : ∑ j, ε j ≤ 1 / 8) :
    (∏ j, V j) / 2 ≤ ∏ j, S j - ∑ j, T j * ∏ i ∈ Finset.univ.erase j, S i := by
  classical
  have hV0 : ∀ j, 0 ≤ V j := fun j => (hV j).le
  have hε1 : ∀ j, ε j ≤ 1 := by
    intro j
    have := Finset.single_le_sum (fun i _ => hε i) (mem_univ j)
    linarith
  have hSlow : ∀ j, V j * (1 - ε j) ≤ S j := by
    intro j
    have := (abs_le.mp (hS j)).1
    nlinarith
  have hSup : ∀ j, S j ≤ V j * (1 + ε j) := by
    intro j
    have := (abs_le.mp (hS j)).2
    nlinarith
  have hSnn : ∀ j, 0 ≤ S j := fun j =>
    le_trans (mul_nonneg (hV0 j) (by linarith [hε1 j])) (hSlow j)
  have hprodV : 0 ≤ ∏ j, V j := prod_nonneg fun j _ => hV0 j
  have hsum0 : 0 ≤ ∑ j, ε j := sum_nonneg fun j _ => hε j
  have hprodS : (∏ j, V j) * (1 - ∑ j, ε j) ≤ ∏ j, S j := by
    calc (∏ j, V j) * (1 - ∑ j, ε j) ≤ (∏ j, V j) * ∏ j, (1 - ε j) :=
          mul_le_mul_of_nonneg_left
            (one_sub_sum_le_prod_one_sub _ _ (fun j _ => hε j) (fun j _ => hε1 j)) hprodV
      _ = ∏ j, V j * (1 - ε j) := by rw [prod_mul_distrib]
      _ ≤ ∏ j, S j := prod_le_prod (fun j _ => mul_nonneg (hV0 j) (by linarith [hε1 j]))
            (fun j _ => hSlow j)
  have hsumT : ∑ j, T j * ∏ i ∈ Finset.univ.erase j, S i ≤
      (∏ j, V j) * (∑ j, ε j) * Real.exp (∑ j, ε j) := by
    calc ∑ j, T j * ∏ i ∈ Finset.univ.erase j, S i
        ≤ ∑ j, (ε j * V j) * ∏ i ∈ Finset.univ.erase j, (V i * (1 + ε i)) := by
          apply sum_le_sum
          intro j _
          apply mul_le_mul (hT j) (prod_le_prod (fun i _ => hSnn i) (fun i _ => hSup i))
            (prod_nonneg fun i _ => hSnn i) (mul_nonneg (hε j) (hV0 j))
      _ = ∑ j, (∏ i, V i) * (ε j * ∏ i ∈ Finset.univ.erase j, (1 + ε i)) := by
          apply sum_congr rfl
          intro j _
          rw [prod_mul_distrib, ← Finset.mul_prod_erase Finset.univ V (mem_univ j)]
          ring
      _ ≤ ∑ j, (∏ i, V i) * (ε j * Real.exp (∑ i, ε i)) := by
          apply sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ hprodV
          apply mul_le_mul_of_nonneg_left _ (hε j)
          calc ∏ i ∈ Finset.univ.erase j, (1 + ε i)
              ≤ Real.exp (∑ i ∈ Finset.univ.erase j, ε i) :=
                prod_one_add_le_exp_sum _ _ (fun i _ => hε i)
            _ ≤ Real.exp (∑ i, ε i) := Real.exp_le_exp.mpr
                (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _ => hε i))
      _ = (∏ j, V j) * (∑ j, ε j) * Real.exp (∑ j, ε j) := by
          rw [← mul_sum, ← sum_mul]
          ring
  have hexp : Real.exp (∑ j, ε j) ≤ 3 := by
    calc Real.exp (∑ j, ε j) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have h1 : (∏ j, V j) * (7 / 8) ≤ (∏ j, V j) * (1 - ∑ j, ε j) :=
    mul_le_mul_of_nonneg_left (by linarith) hprodV
  have h2 : (∏ j, V j) * (∑ j, ε j) * Real.exp (∑ j, ε j) ≤ (∏ j, V j) * (1 / 8) * 3 := by
    apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left hsum hprodV
  linarith

/-! ### The remainder -/

/-- Factorisation of `∑_D (∏_j f_j(D_j)) h(∏ D)` for multiplicative `h`.
@isnad1 id=eq.1h5v.s7.2998499278f8 from=translated src=- shape=45ae9c27 vocab=de14033b
-/
theorem sum_prod_mul_mult {P r : ℕ} (B : Blocks P r) (f : Fin r → ℕ → ℝ)
    (h : ArithmeticFunction ℝ) (hh : h.IsMultiplicative) :
    ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ j, f j (D j)) * h (∏ j, D j) =
      ∏ j, ∑ d ∈ (B.block j).divisors, f j d * h d := by
  classical
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro D hD
  rw [Fintype.mem_piFinset] at hD
  have hcop := B.pairwise_coprime_of_dvd D (fun j => dvd_of_mem_divisors (hD j))
  rw [IsMultiplicative.map_prod D hh Finset.univ (hcop.set_pairwise _), ← prod_mul_distrib]

/-- `|truncMoebius m d| ≤ [ω d ≤ m]`.
@isnad1 id=le.0h2v.s6.2fc6a9e6f08c from=translated src=- shape=d79acc2e vocab=2effe2f4
-/
theorem abs_truncMoebius_le_indicator (m d : ℕ) :
    |truncMoebius m d| ≤ if ω d ≤ m then 1 else 0 := by
  unfold truncMoebius
  split_ifs
  · exact abs_moebius_le_one' d
  · simp

/-- `|defect k j i d| ≤ [ω d ≤ 2 k i + 1]`.
@isnad1 id=le.0h5v.s7.b2d7a4c3730c from=translated src=- shape=c296d1b8 vocab=3ea58cea
-/
theorem abs_defect_le_indicator {r : ℕ} (k : Fin r → ℕ) (j i : Fin r) (d : ℕ) :
    |defect k j i d| ≤ if ω d ≤ 2 * k i + 1 then 1 else 0 := by
  unfold defect
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    unfold truncMoebius
    by_cases h1 : ω d ≤ 2 * k i
    · have h1' : ω d ≤ 2 * k i + 1 := by omega
      rw [ite_eq_left h1, ite_eq_left h1']
      simp [h1']
    · by_cases h2 : ω d ≤ 2 * k i + 1
      · rw [ite_eq_right h1, ite_eq_left h2]
        simp [h2, abs_moebius_le_one' d]
      · rw [ite_eq_right h1, ite_eq_right h2]
        simp [h2]
  · rw [ite_eq_right hij]
    refine le_trans (abs_truncMoebius_le_indicator _ _) ?_
    split_ifs <;> first | exact le_rfl | (exfalso; omega) | norm_num

/-- Remainder bound for a weight family bounded by indicators `[ω d ≤ m i]`.
@isnad1 id=le.4h6v.s8.8f42218ee4d2 from=translated src=- shape=753fdc41 vocab=f852f561
-/
theorem abs_sum_prod_mul_rem_le {r : ℕ} (s : BoundingSieve) (B : Blocks s.prodPrimes r)
    (f : Fin r → ℕ → ℝ) (m : Fin r → ℕ) (hf : ∀ i d, |f i d| ≤ if ω d ≤ m i then 1 else 0)
    (ρ : ArithmeticFunction ℝ) (hρ : ρ.IsMultiplicative) (_hρ0 : ∀ d, 0 ≤ ρ d)
    (hrem : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ ρ d) :
    |∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ j, f j (D j)) * s.rem (∏ j, D j)| ≤
      ∏ j, ∑ d ∈ (B.block j).divisors with ω d ≤ m j, ρ d := by
  classical
  have hind : ∀ j, ∑ d ∈ (B.block j).divisors with ω d ≤ m j, ρ d =
      ∑ d ∈ (B.block j).divisors, (if ω d ≤ m j then (1 : ℝ) else 0) * ρ d := by
    intro j
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp
  simp_rw [hind]
  rw [← sum_prod_mul_mult B (fun j d => if ω d ≤ m j then (1 : ℝ) else 0) ρ hρ]
  calc |∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
          (∏ j, f j (D j)) * s.rem (∏ j, D j)|
      ≤ ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
          |(∏ j, f j (D j)) * s.rem (∏ j, D j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
          (∏ j, if ω (D j) ≤ m j then (1 : ℝ) else 0) * ρ (∏ j, D j) := by
        apply sum_le_sum
        intro D hD
        rw [Fintype.mem_piFinset] at hD
        rw [abs_mul, Finset.abs_prod]
        have hdvd : ∏ j, D j ∣ s.prodPrimes := by
          calc ∏ j, D j ∣ ∏ j, B.block j :=
                Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => dvd_of_mem_divisors (hD j))
            _ = s.prodPrimes := B.prod_block
        apply mul_le_mul (prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hf j (D j)))
          (hrem _ hdvd) (abs_nonneg _) (prod_nonneg fun j _ => by split_ifs <;> norm_num)

/-- **The general Brun–Hooley lower bound.**  With `V_j = ∏_{p ∣ P_j} (1 − ν p)`, if the tails
satisfy `∑_{d ∣ P_j, ω d ≥ 2k_j+1} ν d ≤ ε_j V_j` with `∑ ε_j ≤ 1/8`, and `|R_d| ≤ ρ(d)` for a
multiplicative `ρ ≥ 0`, then
`siftedSum ≥ X (∏ V_j)/2 − (r+1) ∏_j ∑_{d ∣ P_j, ω d ≤ 2k_j+1} ρ(d)`.
@isnad1 id=le.8h6v.s9.ae1a072eccd4 from=translated src=- shape=7c17f4b5 vocab=4d76e632
-/
theorem siftedSum_ge_of_blocks {r : ℕ} (s : BoundingSieve) (B : Blocks s.prodPrimes r)
    (k : Fin r → ℕ) (hX : 0 ≤ s.totalMass) (hν0 : ∀ d, 0 ≤ s.nu d)
    (ρ : ArithmeticFunction ℝ) (hρ : ρ.IsMultiplicative) (hρ0 : ∀ d, 0 ≤ ρ d)
    (hrem : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ ρ d)
    (ε : Fin r → ℝ) (hε : ∀ j, 0 ≤ ε j) (hsum : ∑ j, ε j ≤ 1 / 8)
    (htail : ∀ j, ∑ d ∈ (B.block j).divisors with 2 * k j + 1 ≤ ω d, s.nu d ≤
      ε j * ∏ p ∈ (B.block j).primeFactors, (1 - s.nu p)) :
    s.totalMass * (∏ j, ∏ p ∈ (B.block j).primeFactors, (1 - s.nu p)) / 2 -
      ((r : ℝ) + 1) * ∏ j, ∑ d ∈ (B.block j).divisors with ω d ≤ 2 * k j + 1, ρ d ≤
        s.siftedSum := by
  classical
  refine le_trans ?_ (siftedSum_ge_brunHooley s B k)
  set V : Fin r → ℝ := fun j => ∏ p ∈ (B.block j).primeFactors, (1 - s.nu p) with hVdef
  set S : Fin r → ℝ := fun j => ∑ d ∈ (B.block j).divisors, truncMoebius (2 * k j) d * s.nu d
    with hSdef
  set T : Fin r → ℝ := fun j => ∑ d ∈ (B.block j).divisors,
    (truncMoebius (2 * k j) d - truncMoebius (2 * k j + 1) d) * s.nu d with hTdef
  set Rb : ℝ := ∏ j, ∑ d ∈ (B.block j).divisors with ω d ≤ 2 * k j + 1, ρ d with hRb
  have hVpos : ∀ j, 0 < V j := fun j => prod_pos fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := s.nu_lt_one_of_prime p hpp ((Nat.dvd_of_mem_primeFactors hp).trans (B.block_dvd j))
    linarith
  have hmainS : ∀ j, |S j - V j| ≤ ε j * V j := fun j =>
    le_trans (abs_sum_truncMoebius_mul_sub_prod_le s.nu s.nu_mult hν0 (B.block_squarefree j) _)
      (htail j)
  have hT0 : ∀ j, 0 ≤ T j := fun j =>
    (sum_defect_mul_nu_bounds s.nu hν0 (B.block_squarefree j) (k j)).1
  have hTle : ∀ j, T j ≤ ε j * V j := fun j =>
    le_trans (sum_defect_mul_nu_bounds s.nu hν0 (B.block_squarefree j) (k j)).2 (htail j)
  have hmain := main_term_ge S T V ε hVpos hε hmainS hT0 hTle hsum
  -- split `A_d = ν d X + R_d`
  have hsplit : ∀ (f : Fin r → ℕ → ℝ),
      ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ j, f j (D j)) * s.multSum (∏ j, D j) =
      s.totalMass * (∏ j, ∑ d ∈ (B.block j).divisors, f j d * s.nu d) +
        ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
          (∏ j, f j (D j)) * s.rem (∏ j, D j) := by
    intro f
    rw [← sum_prod_mul_nu s B f, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro D _
    rw [multSum_eq_main_err]
    ring
  simp_rw [hsplit]
  -- the defect main sums factor as `T j * ∏_{i ≠ j} S i`
  have hdef : ∀ j, ∏ i, ∑ d ∈ (B.block i).divisors, defect k j i d * s.nu d =
      T j * ∏ i ∈ Finset.univ.erase j, S i := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ j)]
    congr 1
    · simp only [hTdef, defect, ite_true]
    · apply prod_congr rfl
      intro i hi
      have hij : i ≠ j := (mem_erase.mp hi).1
      simp only [hSdef, defect, ite_eq_right hij]
  simp_rw [hdef]
  -- remainders
  have hrem1 := abs_sum_prod_mul_rem_le s B (fun j => truncMoebius (2 * k j)) (fun j => 2 * k j + 1)
    (fun j d => le_trans (abs_truncMoebius_le_indicator _ _)
      (by split_ifs <;> first | exact le_rfl | (exfalso; omega) | norm_num)) ρ hρ hρ0 hrem
  have hrem2 : ∀ j, |∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
      (∏ i, defect k j i (D i)) * s.rem (∏ i, D i)| ≤ Rb := fun j =>
    abs_sum_prod_mul_rem_le s B (defect k j) (fun i => 2 * k i + 1)
      (fun i d => abs_defect_le_indicator k j i d) ρ hρ hρ0 hrem
  have hRsum : ∑ j, ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
      (∏ i, defect k j i (D i)) * s.rem (∏ i, D i) ≤ (r : ℝ) * Rb := by
    calc ∑ j, ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
          (∏ i, defect k j i (D i)) * s.rem (∏ i, D i)
        ≤ ∑ j, |∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
          (∏ i, defect k j i (D i)) * s.rem (∏ i, D i)| := sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ _j : Fin r, Rb := sum_le_sum fun j _ => hrem2 j
      _ = (r : ℝ) * Rb := by rw [sum_const, Finset.card_fin, nsmul_eq_mul]
  have hR0 : -Rb ≤ ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
      (∏ j, truncMoebius (2 * k j) (D j)) * s.rem (∏ j, D j) := by
    have := neg_abs_le (∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
      (∏ j, truncMoebius (2 * k j) (D j)) * s.rem (∏ j, D j))
    linarith
  rw [sum_add_distrib, ← mul_sum]
  have hXmain := mul_le_mul_of_nonneg_left hmain hX
  have hprodS : ∏ j, S j = ∏ j, ∑ d ∈ (B.block j).divisors, truncMoebius (2 * k j) d * s.nu d :=
    rfl
  have hprodV : ∏ j, V j = ∏ j, ∏ p ∈ (B.block j).primeFactors, (1 - s.nu p) := rfl
  rw [← hprodS, ← hprodV]
  nlinarith [hXmain, hR0, hRsum]

end TwinPrime.Sieve
