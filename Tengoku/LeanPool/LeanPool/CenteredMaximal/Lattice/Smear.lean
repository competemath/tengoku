/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.LeanPool.LeanPool.CenteredMaximal.Basic
public import Tengoku.LeanPool.LeanPool.CenteredMaximal.Lattice.Witness
public import Tengoku

/-!
# Smearing the lattice into an integrable function

For `ε > 0`, truncate the measure to `atomBox N`. Replace each atom of mass `m` at `p`
by `m ε⁻²` times the indicator of the closed square of side `ε` centred at `p`.
`smeared N ε` is integrable; its L¹ norm equals the total mass of the kept atoms.

If `(L, A)` witnesses level one at `z` and every atom of `A` is kept, the square of side `L + ε`
centred at `z` contains the smeared mass of every atom of `A`, so the maximal function at `z` is at
least `L² / (L + ε)² ≥ (1 + ε)⁻² > 1 - 2ε` (`lt_maximalFunction_smeared`). This is the device of
Aldaz (2000, Lemma 1.1), adapted to weighted atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Finset
open scoped ENNReal

namespace LeanPool.CenteredMaximal.Lattice

/-- The position `(c · hgap, r · vgap)` of the atom with index `(c, r)`. -/
def atom (p : ℤ × ℤ) : Fin 2 → ℝ := ![p.1 * hgap, p.2 * vgap]

/-- The atoms kept at scale `N`: columns `-2N-2, …, 2N+2` and rows `-N-1, …, N+1`. -/
def atomBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-2 * (N : ℤ) - 2) (2 * N + 2) ×ˢ Icc (-(N : ℤ) - 1) (N + 1)

/-- The truncated lattice with each atom smeared over the closed square of side `ε`. -/
def smeared (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  ∑ p ∈ atomBox N, colWeight p.1 / ε ^ 2 * (closedBall (atom p) (ε / 2)).indicator 1 z

/--
@isnad1 id=lt.0h1v.s3.3e51e619363d from=translated src=- shape=b9369acb vocab=2f247585
-/
theorem colWeight_pos (c : ℤ) : 0 < colWeight c := by
  unfold colWeight
  split_ifs
  exacts [one_pos, heavy_pos]

/--
@isnad1 id=le.0h3v.s4.619f210325d7 from=translated src=- shape=99a5e74a vocab=5eef1ba0
-/
theorem smeared_nonneg (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) : 0 ≤ smeared N ε z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (div_nonneg (colWeight_pos _).le (sq_nonneg _))
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/--
@isnad1 id=integrab.0h2v.s6.689ac533098f from=translated src=- shape=6734836d vocab=76602367
-/
theorem integrable_smeared (N : ℕ) (ε : ℝ) : Integrable (smeared N ε) := by
  refine integrable_finsetSum _ fun p _ => Integrable.const_mul ?_ _
  exact (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)

/-- Consecutive columns `0, …, 2m` carry mass `(m + 1) + m · heavy`: the `m + 1` even columns
have mass `1` and the `m` odd columns have mass `heavy`.
@isnad1 id=eq.0h1v.s6.2b51302de81b from=translated src=- shape=c330340c vocab=3b4bbcc9
-/
theorem sum_range_colWeight (m : ℕ) :
    ∑ n ∈ Finset.range (2 * m + 1), colWeight n = (m + 1) + m * heavy := by
  -- each step adds the odd column `2m + 1` (mass `heavy`) and the even column `2m + 2` (mass `1`)
  induction m <;> grind [colWeight, Finset.sum_range_succ, Finset.sum_range_zero]

/-- The columns `-2N - 2, …, 2N + 2` of `atomBox N` carry total mass `(2N + 3) + (2N + 2) · heavy`:
the `2N + 3` even columns have mass `1` and the `2N + 2` odd columns have mass `heavy`.
@isnad1 id=eq.0h1v.s7.1c88500ac409 from=translated src=- shape=acc48b0c vocab=e03bef77
-/
theorem sum_colWeight_Icc (N : ℕ) :
    ∑ c ∈ Icc (-2 * (N : ℤ) - 2) (2 * N + 2), colWeight c = (2 * N + 3) + (2 * N + 2) * heavy := by
  -- `colWeight` is even, so the sum is twice the sum over `0, …, 2N + 2` minus the middle column
  convert Finset.sum_Icc_of_even_eq_range colWeight_neg (2 * (N + 1)) using 3 <;>
    grind [colWeight, sum_range_colWeight (N + 1)]

/-- The atoms of `atomBox N` carry total mass `(2N + 3) · ((2N + 3) + (2N + 2) · heavy)`: each of
its `2N + 3` rows carries the column mass of `sum_colWeight_Icc`. See `sum_colWeight_atomBox_le`
for the cruder bound `(2N + 3)² · (1 + heavy)`.
@isnad1 id=eq.0h1v.s7.f6c2d264d549 from=translated src=- shape=3449cb4b vocab=590a07c6
-/
theorem sum_colWeight_atomBox (N : ℕ) :
    ∑ p ∈ atomBox N, colWeight p.1 = (2 * N + 3) * ((2 * N + 3) + (2 * N + 2) * heavy) := by
  -- sum each row over the columns (`sum_colWeight_Icc`), then over the `2N + 3` rows
  have hcard : #(Icc (-(N : ℤ) - 1) (N + 1)) = 2 * N + 3 := by grind [Int.card_Icc]
  simp only [atomBox, sum_product_right, sum_colWeight_Icc, sum_const, hcard, nsmul_eq_mul]
  norm_cast

/--
@isnad1 id=le.0h1v.s6.093905c499f6 from=translated src=- shape=b69f97ad vocab=738a6e47
-/
theorem sum_colWeight_atomBox_le (N : ℕ) :
    ∑ p ∈ atomBox N, colWeight p.1 ≤ (2 * N + 3) ^ 2 * (1 + heavy) := by
  rw [sum_colWeight_atomBox]
  nlinarith [heavy_pos, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/--
@isnad1 id=eq.0h3v.s6.1c0167afdb3b from=translated src=- shape=5c859588 vocab=273ea13e
-/
theorem ofReal_mul_indicator_one {s : Set (Fin 2 → ℝ)} (a : ℝ) (z : Fin 2 → ℝ) :
    ENNReal.ofReal (a * s.indicator 1 z) = s.indicator (fun _ => ENNReal.ofReal a) z := by
  by_cases hz : z ∈ s <;> simp [hz]

/--
@isnad1 id=eq.0h3v.s7.6542d4d61395 from=translated src=- shape=495b933f vocab=422bfb1e
-/
theorem enorm_smeared (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) :
    ‖smeared N ε z‖ₑ = ∑ p ∈ atomBox N, (closedBall (atom p) (ε / 2)).indicator
      (fun _ => ENNReal.ofReal (colWeight p.1 / ε ^ 2)) z := by
  rw [Real.enorm_eq_ofReal (smeared_nonneg N ε z), smeared, ENNReal.ofReal_sum_of_nonneg]
  · simp_rw [ofReal_mul_indicator_one]
  · exact fun _ _ => mul_nonneg (div_nonneg (colWeight_pos _).le (sq_nonneg _))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- A smeared atom has integral equal to its mass.
@isnad1 id=eq.1h2v.s8.bd6217b01cee from=translated src=- shape=4f1db873 vocab=e0ae7833
-/
theorem ofReal_div_sq_mul_volume {ε : ℝ} (hε : 0 < ε) (p : ℤ × ℤ) :
    ENNReal.ofReal (colWeight p.1 / ε ^ 2) * volume (closedBall (atom p) (ε / 2)) =
      ENNReal.ofReal (colWeight p.1) := by
  rw [volume_closedBall_eq _ (by positivity), ← ENNReal.ofReal_mul
    (div_nonneg (colWeight_pos _).le (sq_nonneg _))]
  congr 1
  field_simp

/--
@isnad1 id=eq.1h2v.s7.8b020e8e00e8 from=translated src=- shape=fba8e2d3 vocab=505926a5
-/
theorem lintegral_smeared (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ‖smeared N ε z‖ₑ = ENNReal.ofReal (∑ p ∈ atomBox N, colWeight p.1) := by
  simp_rw [enorm_smeared]
  rw [lintegral_finsetSum _ fun _ _ => measurable_const.indicator measurableSet_closedBall,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => (colWeight_pos _).le]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lintegral_indicator_const measurableSet_closedBall, ofReal_div_sq_mul_volume hε]

private theorem IsWitness.closedBall_atom_subset_closedBall {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hw : IsWitness (z 0) (z 1) L A) (ε : ℝ) {p : ℤ × ℤ} (hp : p ∈ A) :
    closedBall (atom p) (ε / 2) ⊆ closedBall z ((L + ε) / 2) := by
  -- every atom of a witness lies within `L / 2` of `z` in the sup metric
  have : dist (atom p) z ≤ L / 2 := by
    rw [dist_pi_le_iff', Fin.forall_fin_two]
    simpa [atom, Real.dist_eq] using hw.2.2 p hp
  exact closedBall_subset_closedBall' (by linarith)

/-- If `(L, A)` witnesses level one at `z` and `atomBox N` keeps every atom of `A`, then the closed
square of side `L + ε` centred at `z` (a `closedBall` in the sup metric) carries smeared mass at
least `L ^ 2`. Unlike `lintegral_smeared`, which integrates over the whole plane, this bounds the
mass inside a single square, as `lt_maximalFunction_smeared` needs.
@isnad1 id=le.3h5v.s8.f3a7032585cb from=translated src=- shape=d4c4944f vocab=7fa00ba4
-/
theorem ofReal_sq_le_setLIntegral_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ atomBox N) (hw : IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (L ^ 2) ≤ ∫⁻ y in closedBall z ((L + ε) / 2), ‖smeared N ε y‖ₑ :=
  calc ENNReal.ofReal (L ^ 2) ≤ ∑ p ∈ A, ENNReal.ofReal (colWeight p.1) :=
        (ENNReal.ofReal_le_ofReal hw.2.1).trans_eq
          (ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ (colWeight_pos _).le)
    _ = ∫⁻ y in closedBall z ((L + ε) / 2), ∑ p ∈ A, (closedBall (atom p) (ε / 2)).indicator
          (fun _ ↦ ENNReal.ofReal (colWeight p.1 / ε ^ 2)) y := by
        -- each smeared atom of `A` lies inside the square, so it contributes its whole mass
        rw [lintegral_finsetSum _ fun _ _ ↦ measurable_const.indicator measurableSet_closedBall]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_eq_self _ (hw.closedBall_atom_subset_closedBall ε hp),
          ofReal_div_sq_mul_volume hε]
    _ ≤ _ := lintegral_mono fun y ↦ (sum_le_sum_of_subset hA).trans_eq (enorm_smeared N ε y).symm

/-- If `(L, A)` witnesses level one at `z` and `atomBox N` keeps every atom of `A`, then the maximal
function of `smeared N ε` at `z` exceeds `1 - 2ε`. The bound is uniform in `N` and in the witness,
so it holds at every point that has some witness inside `atomBox N`. Compare
`ofReal_sq_le_setLIntegral_smeared`, which bounds the mass of the square of side `L + ε` rather than
the maximal function.
@isnad1 id=lt.3h5v.s7.527d79ca0bae from=translated src=- shape=85dbba88 vocab=3beb7756
-/
theorem lt_maximalFunction_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ atomBox N) (hw : IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z := by
  have hL : 1 ≤ L := hw.1
  have hr : 0 < (L + ε) / 2 := by positivity
  refine lt_of_lt_of_le ?_ (le_maximalFunction _ z hr)
  rw [volume_closedBall_eq z hr.le]
  calc ENNReal.ofReal (1 - 2 * ε) < ENNReal.ofReal (L ^ 2 / (L + ε) ^ 2) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ (by positivity)]
        -- `L² - (1 - 2ε)(L + ε)² = 2εL(L - 1) + ε²(4L - 1) + 2ε³` is positive since `1 ≤ L`
        nlinarith [pow_pos hε 3, mul_nonneg hε.le (sub_nonneg.2 hL)]
    _ = (ENNReal.ofReal ((2 * ((L + ε) / 2)) ^ 2))⁻¹ * ENNReal.ofReal (L ^ 2) := by
        rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_div_of_pos (by positivity),
          ENNReal.div_eq_inv_mul]
    _ ≤ _ := mul_le_mul_right (ofReal_sq_le_setLIntegral_smeared hε hA hw) _

end LeanPool.CenteredMaximal.Lattice
