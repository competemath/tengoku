import Tengoku.OpenaiMath.OAI.Analysis.Littlewood.Gaussian

namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A Boolean encoding of a real sign. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> norm_num [boolSign]

/-- Elementary Rademacher MGF bound for one bounded coefficient. -/
theorem bool_exp_sum_le {a : ℝ} (ha : |a| ≤ 1) (t : ℝ) :
    (∑ b : Bool, Real.exp (t * a * boolSign b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
  simp only [Fintype.sum_bool, boolSign, ite_true, Bool.false_eq_true,
    ite_false, mul_one, mul_neg_one]
  calc
    Real.exp (t * a) + Real.exp (-(t * a)) = 2 * Real.cosh (t * a) := by
      rw [Real.cosh_eq]; ring
    _ ≤ 2 * Real.exp ((t * a) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
    _ ≤ 2 * Real.exp (t ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ha2)]

/-- A pointwise bound for the cost of quantizing a row sum. -/
theorem round_abs_le_exp_pair {x d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    |(round (x / d) : ℝ)| ≤
      Real.exp (t * x - t * d / 4) + Real.exp (-t * x - t * d / 4) := by
  by_cases hq : round (x / d) = 0
  · rw [hq, Int.cast_zero, abs_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ |(round (x / d) : ℝ)| := by
    have hi : (1 : ℤ) ≤ |round (x / d)| := by
      have := abs_pos.mpr hq
      omega
    exact_mod_cast hi
  have hbound : |(round (x / d) : ℝ)| ≤ |x| / d + 1 / 2 := by
    calc
      _ ≤ |x / d| + |x / d - (round (x / d) : ℝ)| := by
        have h := abs_add_le (x / d) (-(x / d - (round (x / d) : ℝ)))
        simp only [abs_neg] at h
        convert h using 1; congr 1; ring
      _ ≤ _ := by
        rw [abs_div, abs_of_pos hd]
        gcongr
        exact abs_sub_round (x / d)
  have hxd : (|(round (x / d) : ℝ)| - 1 / 2) * d ≤ |x| := by
    have := (le_div_iff₀ hd).mp (by linarith :
      |(round (x / d) : ℝ)| - 1 / 2 ≤ |x| / d)
    exact this
  have hcost : |(round (x / d) : ℝ)| ≤ t * |x| - t * d / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hxd ht
    have hprod := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr htd)
    nlinarith
  have hxexp : |(round (x / d) : ℝ)| ≤ Real.exp (t * |x| - t * d / 4) := by
    nlinarith [Real.add_one_le_exp (t * |x| - t * d / 4)]
  apply hxexp.trans
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The geometric partition function for integer quantization labels. -/
theorem int_geometric_sum_le (S : Finset ℤ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) :
    (∑ z ∈ S, q ^ z.natAbs) ≤ Real.exp (4 * q) := by
  have hq1 : q < 1 := by linarith
  have hnat : HasSum (fun n : ℕ ↦ q ^ (n : ℤ).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hneg : HasSum (fun n : ℕ ↦ q ^ (-(n : ℤ)).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hfull := HasSum.of_nat_of_neg (f := fun z : ℤ ↦ q ^ z.natAbs) hnat hneg
  have hsum : (∑ z ∈ S, q ^ z.natAbs) ≤ (1 - q)⁻¹ + (1 - q)⁻¹ - 1 := by
    simpa using (hfull.summable.sum_le_tsum S (fun z hz ↦ pow_nonneg hq _)).trans_eq
      hfull.tsum_eq
  have hden : 0 < 1 - q := by linarith
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hid : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 = 1 + 2 * q * (1 - q)⁻¹ := by
    field_simp [ne_of_gt hden]
    ring
  have hrat : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 ≤ 1 + 4 * q := by
    rw [hid]
    have := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * q by positivity)
    nlinarith
  exact hsum.trans (hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (4 * q)))

/-- Each integer code has exponentially decaying weight. -/
theorem int_exp_sum_le (S : Finset ℤ) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ z ∈ S, Real.exp (-a * |(z : ℝ)|)) ≤ Real.exp (4 * Real.exp (-a)) := by
  have heq (z : ℤ) : Real.exp (-a * |(z : ℝ)|) = Real.exp (-a) ^ z.natAbs := by
    have hc : (z.natAbs : ℝ) = |(z : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [← hc, mul_comm, Real.exp_nat_mul]
  simp_rw [heq]
  exact int_geometric_sum_le S (Real.exp_pos _).le ha

/-- Partition function of Hamming distance on the Boolean cube. -/
theorem hamming_exp_sum {α : Type u} [Fintype α] [DecidableEq α]
    (x : α → Bool) (a : ℝ) :
    (∑ y : α → Bool, Real.exp (-a * hammingDist x y)) =
      (1 + Real.exp (-a)) ^ Fintype.card α := by
  classical
  have hcast (y : α → Bool) : (hammingDist x y : ℝ) =
      ∑ k : α, if x k ≠ y k then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole (fun k ↦ x k ≠ y k) Finset.univ).symm
  simp_rw [hcast, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun k b ↦ Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0))]
  have hstep (k : α) : (∑ b : Bool, Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0)) =
      1 + Real.exp (-a) := by
    cases x k <;> simp [add_comm]
  simp_rw [hstep]
  simp

/-- A small Hamming ball occupies exponentially less than the whole cube. -/
theorem hamming_small_family_card {α : Type u} [Fintype α] [DecidableEq α]
    (G : Finset (α → Bool)) (x : α → Bool)
    (hG : ∀ y ∈ G, (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16) :
    (G.card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
  have he2 : Real.exp (-2) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have h2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this; exact this
    have hh := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) h2
    rw [← Real.exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have hsum : (∑ y : α → Bool, Real.exp (-2 * hammingDist x y)) ≤
      Real.exp (Fintype.card α / 4) := by
    rw [hamming_exp_sum]
    calc
      _ ≤ Real.exp (1 / 4) ^ Fintype.card α := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (1 / 4)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlow : (G.card : ℝ) * Real.exp (-(Fintype.card α : ℝ) / 8) ≤
      ∑ y : α → Bool, Real.exp (-2 * hammingDist x y) := by
    calc
      _ = ∑ _y ∈ G, Real.exp (-(Fintype.card α : ℝ) / 8) := by simp
      _ ≤ ∑ y ∈ G, Real.exp (-2 * hammingDist x y) := by
        apply Finset.sum_le_sum
        intro y hy
        apply Real.exp_le_exp.mpr
        have := hG y hy
        linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_left (hlow.trans hsum)
    (Real.exp_pos ((Fintype.card α : ℝ) / 8)).le
  have heq : (Fintype.card α : ℝ) / 8 + -(Fintype.card α : ℝ) / 8 = 0 := by ring
  rw [← mul_assoc, mul_comm (Real.exp _) (G.card : ℝ), mul_assoc, ← Real.exp_add,
    heq, Real.exp_zero, mul_one, ← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

/-- A nonnegative cost with small average is small on at least half a finite set. -/
theorem card_good_cost {γ : Type w} [Fintype γ] [DecidableEq γ]
    (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) {M : ℝ} (hM : 0 < M)
    (hsum : (∑ x, f x) ≤ (Fintype.card γ : ℝ) * M / 2) :
    (Fintype.card γ : ℝ) / 2 ≤ ((Finset.univ.filter fun x ↦ f x ≤ M).card : ℝ) := by
  classical
  let G := Finset.univ.filter fun x ↦ f x ≤ M
  let B := Finset.univ.filter fun x ↦ ¬ f x ≤ M
  have hcard : G.card + B.card = Fintype.card γ := by
    exact Finset.card_filter_add_card_filter_not _
  have hlow : (B.card : ℝ) * M ≤ ∑ x, f x := by
    calc
      _ = ∑ _x ∈ B, M := by simp
      _ ≤ ∑ x ∈ B, f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ ↦ hf x)
  have hc : (G.card : ℝ) + (B.card : ℝ) = Fintype.card γ := by exact_mod_cast hcard
  change _ ≤ (G.card : ℝ)
  nlinarith

/-- Numerical entropy estimates, with fixed generous absolute constants. -/
theorem entropy_log_parameters {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    let L := Real.log (16 * R / s)
    1 / 2 ≤ L ∧ Real.exp (-4 * L) ≤ 1 / 2 ∧
      2 * R * Real.exp (-128 * L) ≤ s / (512 * L) ∧
      4 * R * Real.exp (-4 * L) ≤ s / 64 := by
  dsimp only
  let L := Real.log (16 * R / s)
  change 1 / 2 ≤ L ∧ _
  have hR : 0 < R := hs.trans_le hsR
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hratio0 : 0 < 16 * R / s := by positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hL : (1 / 2 : ℝ) ≤ L := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hL0 : 0 < L := by linarith
  have heq : Real.exp (-L) = s / (16 * R) := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log hratio0, inv_div]
  have he : Real.exp (-L) ≤ 1 / 16 := by
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 16 * R)).mpr
    nlinarith
  have hbase : R * Real.exp (-L) = s / 16 := by
    rw [heq]
    field_simp

  have hfour : Real.exp (-4 * L) = Real.exp (-L) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdecay : Real.exp (-4 * L) ≤ 1 / 2 := by
    rw [hfour]
    calc
      _ ≤ (1 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
      _ ≤ _ := by norm_num
  have hpart : 4 * R * Real.exp (-4 * L) ≤ s / 64 := by
    have hp : Real.exp (-L) ^ 3 ≤ 1 / 16 := by
      calc
        _ ≤ (1 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
        _ ≤ _ := by norm_num
    calc
      _ = 4 * (R * Real.exp (-L)) * Real.exp (-L) ^ 3 := by rw [hfour]; ring
      _ = s / 4 * Real.exp (-L) ^ 3 := by rw [hbase]; ring
      _ ≤ s / 4 * (1 / 16) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hexp : 64 * L ≤ Real.exp (127 * L) := by
    nlinarith [Real.add_one_le_exp (127 * L)]
  have hmul : Real.exp (-128 * L) * (64 * L) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (-128 * L) * Real.exp (127 * L) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmean : 2 * R * Real.exp (-128 * L) ≤ s / (512 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 512 * L)).mpr
    calc
      _ = 16 * R * (Real.exp (-128 * L) * (64 * L)) := by ring
      _ ≤ 16 * R * Real.exp (-L) := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = s := by nlinarith [hbase]
  exact ⟨hL, hdecay, hmean, hpart⟩

/-- The Boolean cube is larger than the entropy bounds used above. -/
theorem exp_small_lt_half_cube {n : ℕ} (hn : 32 ≤ n) :
    Real.exp (13 * n / 32) < (2 : ℝ) ^ n / 2 := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hu : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : 13 * (n : ℝ) / 32 < n * Real.log 2 - Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  calc
    _ < Real.exp (n * Real.log 2 - Real.log 2) := Real.exp_lt_exp.mpr hlt
    _ = _ := by rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The logarithmic discrepancy potential contracts on shortening the remaining columns. -/
theorem discrepancy_potential_contract {s u R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hu0 : 0 ≤ u) (hu : u ≤ (15 / 16) * s) :
    Real.sqrt (u * Real.log (16 * R / u)) ≤
      (63 / 64) * Real.sqrt (s * Real.log (16 * R / s)) := by
  by_cases hu_eq : u = 0
  · rw [hu_eq]
    simp only [zero_mul, Real.sqrt_zero]
    positivity
  have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_eq)
  have hR : 0 < R := hs.trans_le hsR
  let L := Real.log (16 * R / s)
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hL : 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hratio
    rw [hlog16] at hh
    change _ ≤ L at hh
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log (16 * R / u) = L + Real.log (s / u) := by
    have hid : 16 * R / u = (16 * R / s) * (s / u) := by field_simp
    rw [hid, Real.log_mul (by positivity : 16 * R / s ≠ 0) (by positivity : s / u ≠ 0)]
  have hsmall : u * Real.log (s / u) ≤ s - u := by
    calc
      _ ≤ u * (s / u - 1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu0
      _ = _ := by field_simp
  have hsq : u * Real.log (16 * R / u) ≤ (31 / 32) * (s * L) := by
    rw [hlog, mul_add]
    have hprod := mul_le_mul_of_nonneg_right hu (show 0 ≤ L - 1 by linarith)
    have hLs := mul_le_mul_of_nonneg_left hL hs.le
    nlinarith
  apply (Real.sqrt_le_left (by positivity : 0 ≤ (63 / 64) * Real.sqrt (s * L))).mpr
  have hsqrt := Real.sq_sqrt (mul_nonneg hs.le hL0)
  change u * Real.log (16 * R / u) ≤ ((63 / 64) * Real.sqrt (s * L)) ^ 2
  nlinarith [mul_nonneg hs.le hL0]

/-- The small mass controls the discrepancy potential at every dyadic scale. -/
theorem dyadic_potential_bound {s μ R : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ R)
    (hs : 0 ≤ s) (j : ℕ) (hsmass : s ≤ 2 ^ j * μ) :
    Real.sqrt (s * Real.log (2 * R / s)) / 2 ^ j ≤
      (3 / 4) ^ j * Real.sqrt (μ * Real.log (2 * R / μ)) := by
  have hR : 0 < R := by linarith
  have hratio : (4 : ℝ) ≤ 2 * R / μ := (le_div_iff₀ hμ).mpr (by linarith)
  let L := Real.log (2 * R / μ)
  have hL : 1 ≤ L := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
    norm_num at h2 h4
    dsimp [L]
    linarith
  have hφ : 0 ≤ μ * L := mul_nonneg hμ.le (by linarith)
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hf : s * Real.log (2 * R / s) ≤ 2 ^ j * (μ * L) := by
    by_cases hz : s = 0
    · rw [hz, zero_mul]
      positivity
    have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hid : 2 * R / s = (2 * R / μ) * (μ / s) := by field_simp
    rw [hid, Real.log_mul (by positivity : 2 * R / μ ≠ 0)
      (by positivity : μ / s ≠ 0), mul_add]
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < μ / s by positivity)) hs
    have heq : s * (μ / s - 1) = μ - s := by field_simp
    rw [heq] at hlog
    have hmult := mul_le_mul_of_nonneg_right hsmass (show 0 ≤ L - 1 by linarith)
    change s * L + s * Real.log (μ / s) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hpow hμ.le]
  have hscale : (2 : ℝ) ^ j ≤ ((3 / 4) ^ j * 2 ^ j) ^ 2 := by
    calc
      (2 : ℝ) ^ j ≤ (9 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ = _ := by rw [← mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hroot := Real.sq_sqrt hφ
  change s * Real.log (2 * R / s) ≤ ((3 / 4) ^ j * Real.sqrt (μ * L) * 2 ^ j) ^ 2
  calc
    _ ≤ 2 ^ j * (μ * L) := hf
    _ ≤ (((3 / 4) ^ j * 2 ^ j) ^ 2) * (μ * L) := mul_le_mul_of_nonneg_right hscale hφ
    _ = _ := by calc
      _ = ((3 / 4) ^ j * 2 ^ j) ^ 2 * (Real.sqrt (μ * L)) ^ 2 := by rw [hroot]
      _ = _ := by ring

open scoped ComplexConjugate
open Finset

/-- Orthogonality of the exact full root-of-unity grid. -/
theorem grid_power_orthogonality {M a b : ℕ} [NeZero M] (ha : a < M) (hb : b < M) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ a * conj (ZMod.stdAddChar j ^ b)) =
      if a = b then (M : ℂ) else 0 := by
  have hpow (n : ℕ) (j : ZMod M) : ZMod.stdAddChar j ^ n =
      ZMod.stdAddChar ((n : ZMod M) * j) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hconj (j : ZMod M) : conj (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
    exact (Circle.coe_inv_eq_conj (ZMod.toCircle j)).symm
  simp_rw [hpow, hconj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  have hzero : ((a : ZMod M) - b = 0) ↔ a = b := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M (mt hzero.mp hab))

/-- Mean square of a translated Dirichlet kernel on an oversampling grid. -/
theorem grid_dirichlet_square {M n : ℕ} [NeZero M] (hn : n ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ‖∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))‖ ^ 2) =
      (M : ℝ) * n := by
  have hcomplex : (∑ j : ZMod M,
      (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
      conj (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ)))) =
      (M : ℂ) * n := by
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Eq.trans ?_ (show (∑ a : Fin n, (M : ℂ)) = (M : ℂ) * n by simp [mul_comm])
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    calc
      (∑ b : Fin n, ∑ j : ZMod M,
          z ^ (b : ℕ) * conj (ZMod.stdAddChar j ^ (b : ℕ)) *
            (conj (z ^ (a : ℕ)) * ZMod.stdAddChar j ^ (a : ℕ))) =
        ∑ b : Fin n, (z ^ (b : ℕ) * conj (z ^ (a : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ (a : ℕ) *
            conj (ZMod.stdAddChar j ^ (b : ℕ))) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = ∑ b : Fin n, if b = a then (z ^ (a : ℕ) * conj (z ^ (a : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [grid_power_orthogonality (a.isLt.trans_le hn) (b.isLt.trans_le hn)]
        by_cases heq : b = a
        · subst b
          simp
        · have hval : (b : ℕ) ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h)
          simp [heq, Ne.symm hval]
      _ = (M : ℂ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hz]
        simp
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using hreal

/-- A rotated, finite Dirichlet kernel on the root grid. -/
def gridDirichlet {M : ℕ} [NeZero M] (n : ℕ) (z : ℂ) (j : ZMod M) : ℂ :=
  ∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))

/-- The cross-Dirichlet kernel reproduces each required nonnegative frequency. -/
theorem grid_reproduce_monomial {M N : ℕ} [NeZero M] (hNM : 2 * N ≤ M)
    (k : Fin N) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
      conj (gridDirichlet N z j)) = (M : ℂ) * N * z ^ (k : ℕ) := by
  have hb (b : Fin N) : (∑ j : ZMod M,
      ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
        (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
      (M : ℂ) * z ^ (k : ℕ) := by
    have hkb : (k : ℕ) + b < 2 * N := by omega
    let a₀ : Fin (2 * N) := ⟨(k : ℕ) + b, hkb⟩
    simp only [gridDirichlet, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ a : Fin (2 * N), ∑ j : ZMod M,
          ZMod.stdAddChar j ^ (k : ℕ) *
            (z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
              (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
        ∑ a : Fin (2 * N), (z ^ (a : ℕ) * conj (z ^ (b : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ ((k : ℕ) + b) *
            conj (ZMod.stdAddChar j ^ (a : ℕ))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
      _ = ∑ a : Fin (2 * N), if a = a₀ then
          (z ^ ((k : ℕ) + b) * conj (z ^ (b : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [grid_power_orthogonality (hkb.trans_le hNM) (a.isLt.trans_le hNM)]
        by_cases heq : a = a₀
        · subst a
          simp [a₀]
        · have hval : (k : ℕ) + b ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h.symm)
          simp [heq, hval]
      _ = (M : ℂ) * z ^ (k : ℕ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [pow_add, mul_assoc (z ^ (k : ℕ)) (z ^ (b : ℕ)) (conj (z ^ (b : ℕ))),
          Complex.mul_conj, Complex.normSq_eq_norm_sq,
          norm_pow, hz]
        simp [mul_comm]
  calc
    _ = ∑ j : ZMod M, ∑ b : Fin N,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [gridDirichlet, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    _ = ∑ b : Fin N, ∑ j : ZMod M,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := Finset.sum_comm
    _ = ∑ _b : Fin N, (M : ℂ) * z ^ (k : ℕ) := Finset.sum_congr rfl (fun b _ ↦ hb b)
    _ = _ := by simp; ring

/-- No logarithmic loss: an oversampled analytic polynomial is controlled on the whole circle. -/
theorem polynomial_grid_bound {N M : ℕ} [NeZero M] (hN : 0 < N) (hNM : 2 * N ≤ M)
    (c : Fin N → ℂ) {G : ℝ} (hG : 0 ≤ G)
    (hgrid : ∀ j : ZMod M, ‖∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ G)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤ 2 * G := by
  have hid : (M : ℂ) * N * (∑ k : Fin N, c k * z ^ (k : ℕ)) =
      ∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j) := by
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ((M : ℂ) * N * z ^ (k : ℕ)) := by ring
      _ = c k * (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)) := by
        rw [grid_reproduce_monomial hNM k hz]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have h2N := grid_dirichlet_square (n := 2 * N) hNM hz
  have hN' := grid_dirichlet_square (n := N) (by omega : N ≤ M) hz
  change (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ ^ 2) = _ at h2N
  change (∑ j : ZMod M, ‖gridDirichlet N z j‖ ^ 2) = _ at hN'
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod M))
    (fun j ↦ ‖gridDirichlet (2 * N) z j‖) (fun j ↦ ‖gridDirichlet N z j‖)
  rw [h2N, hN'] at hcs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkernel : (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
      ‖gridDirichlet N z j‖) ≤ 2 * M * N := by
    push_cast at hcs
    nlinarith [mul_pos hMpos hNpos]
  have hnorm : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ =
      ‖∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := by
    rw [← hid, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hbound : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤
      G * (2 * M * N) := by
    rw [hnorm]
    calc
      _ ≤ ∑ j : ZMod M, ‖(∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod M, G * (‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := Finset.sum_le_sum fun j _ ↦ by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        nlinarith [mul_le_mul_of_nonneg_right (hgrid j)
          (mul_nonneg (norm_nonneg (gridDirichlet (2 * N) z j)) (norm_nonneg (gridDirichlet N z j)))]
      _ = G * (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hG
  nlinarith [mul_pos hMpos hNpos]

def defectMass {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ k : Fin N, (1 - |X k|)) / 2

end

end AsymptoticallyMinimalLittlewood

end OAI
