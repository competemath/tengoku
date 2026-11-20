import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/KitaKen1/erdos176-nksqrtk-polynomial-bound-lean@19b2ad31c812, `Erdos176Lean/Basic.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


/-!
# Erdős problem 176: Lean checks for the reported proof attempt

AI usage:
This Lean development and accompanying explanations were prepared with
assistance from Codex 5.5 using xhigh reasoning, and ChatGPT 5.5 Pro.

The local `176.html` proof attempt reduces the claimed polynomial bound to two
average estimates for cyclic arithmetic progressions.  This file starts by
checking the algebraic part of that reduction.

The theorem `upper_lt_lower_of_threshold` says that the numerical threshold in
the report is exactly strong enough: once

`2 * ((k^2 - 1) * (k - 1) * (2*k + 1)) / (k - 3) < N`,

the proposed wrap-error upper bound is strictly below the Fejér lower bound
specialized at `D = 2*k`.
-/

namespace Erdos176Lean

open scoped BigOperators

section CyclicAP

variable {N : ℕ} [NeZero N]

/-- The cyclic index `a + j*d` modulo `N`.-/
def cyclicIndex (a : Fin N) (j d : ℕ) : Fin N :=
  ⟨(a.val + j * d) % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩

/-- The sum of a cyclic `k`-term arithmetic progression.-/
def cyclicAPSum (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, f (cyclicIndex a j d)

/-- The cyclic progression has wrapped around the end of `[0,N)`.-/
def wraps (k : ℕ) (a : Fin N) (d : ℕ) : Prop :=
  N ≤ a.val + (k - 1) * d

/-- The ordinary, non-wrapping AP sum, available only with a non-wrap proof.-/
def ordinaryAPSum
    (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ)
    (hnowrap : ¬ wraps (N := N) k a d) : ℤ :=
  ∑ j : Fin k, f
    ⟨a.val + j.val * d, by
      have hbound : a.val + (k - 1) * d < N := Nat.lt_of_not_ge hnowrap
      have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
      exact lt_of_le_of_lt
        (Nat.add_le_add_left (Nat.mul_le_mul_right d hjle) a.val) hbound⟩

theorem cyclicAPSum_eq_ordinaryAPSum
    (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ)
    (hnowrap : ¬ wraps (N := N) k a d) :
    cyclicAPSum f k a d = ordinaryAPSum f k a d hnowrap := by
  unfold cyclicAPSum ordinaryAPSum
  rw [← Fin.sum_univ_eq_sum_range (fun j => f (cyclicIndex a j d)) k]
  refine Finset.sum_congr rfl ?_
  intro j hj
  apply congrArg f
  apply Fin.ext
  have hbound : a.val + (k - 1) * d < N := Nat.lt_of_not_ge hnowrap
  have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
  have hlt : a.val + j.val * d < N :=
    lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.mul_le_mul_right d hjle) a.val) hbound
  simp [cyclicIndex, Nat.mod_eq_of_lt hlt]

theorem abs_cyclicAPSum_le
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    (k : ℕ) (a : Fin N) (d : ℕ) :
    |cyclicAPSum f k a d| ≤ (k : ℤ) := by
  unfold cyclicAPSum
  calc
    |∑ j ∈ Finset.range k, f (cyclicIndex a j d)|
        ≤ ∑ j ∈ Finset.range k, |f (cyclicIndex a j d)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, (1 : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          rcases hpm (cyclicIndex a j d) with h | h <;> simp [h]
    _ = (k : ℤ) := by simp

/--
For a fixed excess length `m`, at most `m` starting points `a : Fin N` satisfy
`N ≤ a + m`.  This is the finite counting ingredient behind the report's
wrap estimate.-/
theorem card_wrapStarts_le (N m : ℕ) [NeZero N] :
    ((Finset.univ : Finset (Fin N)).filter fun a => N ≤ a.val + m).card ≤ m := by
  by_cases hm : m = 0
  · subst hm
    simp [Nat.not_le_of_gt]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let wrapToFin : {a : Fin N // N ≤ a.val + m} → Fin m := fun a =>
      ⟨a.val.val + m - N, by
        have hlt : a.val.val < N := a.val.isLt
        have hwrap : N ≤ a.val.val + m := a.property
        omega⟩
    have hinj : Function.Injective wrapToFin := by
      intro a b hab
      apply Subtype.ext
      apply Fin.ext
      have hwrapa : N ≤ a.val.val + m := a.property
      have hwrapb : N ≤ b.val.val + m := b.property
      have hvals : a.val.val + m - N = b.val.val + m - N :=
        congrArg Fin.val hab
      omega
    have hcard := Fintype.card_le_of_injective wrapToFin hinj
    simpa [Fintype.card_subtype] using hcard

theorem sum_range_succ_nat (D : ℕ) :
    (∑ i ∈ Finset.range D, (i + 1)) = D * (D + 1) / 2 := by
  have h := (Finset.sum_range_succ' (fun i : ℕ => i) D).symm
  calc
    (∑ i ∈ Finset.range D, (i + 1))
        = ∑ i ∈ Finset.range (D + 1), i := by simpa using h
    _ = D * (D + 1) / 2 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using Finset.sum_range_id (D + 1)

theorem sum_range_succ_int (D : ℕ) :
    (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℤ)))
      = ((D * (D + 1) / 2 : ℕ) : ℤ) := by
  exact_mod_cast sum_range_succ_nat D

end CyclicAP

section FourierSetup

variable {N : ℕ}

/-- A cyclic AP sum written on `ZMod N`, the natural domain for finite Fourier analysis.-/
noncomputable def zmodAPSum (f : ZMod N → ℂ) (k : ℕ) (a d : ZMod N) : ℂ :=
  ∑ j ∈ Finset.range k, f (a + j • d)

/-- The scalar geometric power sum that appears after diagonalizing by characters.-/
noncomputable def geomPowerSum (z : ℂ) (k d : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, z ^ (j * d)

/-- The scalar energy whose lower bound is the Cassels/Turán power-sum input.-/
noncomputable def geomPowerEnergy (z : ℂ) (k D : ℕ) : ℝ :=
  ∑ i ∈ Finset.range D, ‖geomPowerSum z k (i + 1)‖ ^ 2

/-- The right-hand side of the scalar Cassels/Turán power-sum lower bound.-/
noncomputable def casselsRhs (k D : ℕ) : ℝ :=
  ((k : ℝ) * (D + 1 : ℝ) - (k : ℝ) ^ 2) / 2

/--
The Fejér-pair term used in the standard proof of the Cassels/Turán power-sum
inequality.  It is a normalized squared Dirichlet sum, hence nonnegative.-/
noncomputable def fejerPairTerm (z : ℂ) (D p q : ℕ) : ℝ :=
  (D + 1 : ℝ)⁻¹ *
    ‖∑ r ∈ Finset.range (D + 1), (z ^ p * starRingEnd ℂ (z ^ q)) ^ r‖ ^ 2

/--
The Fejér-pair energy before expanding the square and collecting by
differences.  The diagonal terms alone already give a useful lower bound.-/
noncomputable def fejerPairEnergy (z : ℂ) (k D : ℕ) : ℝ :=
  ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k, fejerPairTerm z D p q

theorem fejerPair_diag_base_one {z : ℂ} (hz : ‖z‖ = 1) (p : ℕ) :
    z ^ p * starRingEnd ℂ (z ^ p) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [norm_pow, hz]

theorem fejerPair_diag_term {z : ℂ} (hz : ‖z‖ = 1) (p D : ℕ) :
    fejerPairTerm z D p p = (D + 1 : ℝ) := by
  unfold fejerPairTerm
  rw [fejerPair_diag_base_one hz p]
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_one]
  rw [norm_natCast]
  have hpos : (0 : ℝ) < D + 1 := by positivity
  field_simp [ne_of_gt hpos]
  norm_num [Nat.cast_add, Nat.cast_one]

theorem fejerPairTerm_nonneg (z : ℂ) (D p q : ℕ) :
    0 ≤ fejerPairTerm z D p q := by
  unfold fejerPairTerm
  positivity

theorem ofReal_norm_sq_eq_mul_conj (w : ℂ) :
    ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem star_sum_powers (w : ℂ) (D : ℕ) :
    starRingEnd ℂ (∑ r ∈ Finset.range (D + 1), w ^ r) =
      ∑ r ∈ Finset.range (D + 1), starRingEnd ℂ (w ^ r) := by
  simp [map_sum]

theorem ofReal_fejerPairTerm_eq_mul_conj (z : ℂ) (D p q : ℕ) :
    ((fejerPairTerm z D p q : ℝ) : ℂ) =
      ((D + 1 : ℝ)⁻¹ : ℂ) *
        ((∑ r ∈ Finset.range (D + 1), (z ^ p * starRingEnd ℂ (z ^ q)) ^ r) *
          starRingEnd ℂ (∑ r ∈ Finset.range (D + 1),
            (z ^ p * starRingEnd ℂ (z ^ q)) ^ r)) := by
  unfold fejerPairTerm
  rw [Complex.ofReal_mul, Complex.ofReal_inv]
  congr 1
  rw [ofReal_norm_sq_eq_mul_conj]

theorem ofReal_fejerPairTerm_eq_double_sum (z : ℂ) (D p q : ℕ) :
    ((fejerPairTerm z D p q : ℝ) : ℂ) =
      ((D + 1 : ℝ)⁻¹ : ℂ) *
        ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
          (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
            starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
  rw [ofReal_fejerPairTerm_eq_mul_conj]
  let w : ℂ := z ^ p * starRingEnd ℂ (z ^ q)
  have hmul :
      (∑ r ∈ Finset.range (D + 1), w ^ r) *
          (∑ s ∈ Finset.range (D + 1), starRingEnd ℂ (w ^ s)) =
        ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
          w ^ r * starRingEnd ℂ (w ^ s) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Finset.mul_sum]
  change ((D + 1 : ℝ)⁻¹ : ℂ) *
      ((∑ r ∈ Finset.range (D + 1), w ^ r) *
        starRingEnd ℂ (∑ r ∈ Finset.range (D + 1), w ^ r)) =
    ((D + 1 : ℝ)⁻¹ : ℂ) *
      ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
        w ^ r * starRingEnd ℂ (w ^ s)
  rw [star_sum_powers, hmul]

theorem pow_mul_conj_pow_eq_pow_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    {s r : ℕ} (h : s ≤ r) :
    z ^ r * starRingEnd ℂ (z ^ s) = z ^ (r - s) := by
  conv_lhs =>
    rw [← Nat.sub_add_cancel h]
    rw [pow_add]
  calc
    z ^ (r - s) * z ^ s * starRingEnd ℂ (z ^ s)
        = z ^ (r - s) * (z ^ s * starRingEnd ℂ (z ^ s)) := by ring
    _ = z ^ (r - s) := by
          rw [fejerPair_diag_base_one hz s]
          ring

theorem pow_mul_conj_pow_eq_conj_pow_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    {r s : ℕ} (h : r ≤ s) :
    z ^ r * starRingEnd ℂ (z ^ s) = starRingEnd ℂ (z ^ (s - r)) := by
  conv_lhs =>
    rw [← Nat.sub_add_cancel h]
    rw [pow_add]
    rw [map_mul]
  calc
    z ^ r * (starRingEnd ℂ (z ^ (s - r)) * starRingEnd ℂ (z ^ r))
        = starRingEnd ℂ (z ^ (s - r)) * (z ^ r * starRingEnd ℂ (z ^ r)) := by ring
    _ = starRingEnd ℂ (z ^ (s - r)) := by
          rw [fejerPair_diag_base_one hz r]
          ring

theorem geomPowerSum_base_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {s r : ℕ} (h : s ≤ r) :
    (∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p) =
      geomPowerSum z k (r - s) := by
  unfold geomPowerSum
  rw [pow_mul_conj_pow_eq_pow_sub_of_le hz h]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [← pow_mul]
  ring_nf

theorem norm_geomPowerSum_base_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {s r : ℕ} (h : s ≤ r) :
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ =
      ‖geomPowerSum z k (r - s)‖ := by
  rw [geomPowerSum_base_sub_of_le hz k h]

theorem geomPowerSum_base_conj_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {r s : ℕ} (h : r ≤ s) :
    (∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p) =
      starRingEnd ℂ (geomPowerSum z k (s - r)) := by
  unfold geomPowerSum
  rw [pow_mul_conj_pow_eq_conj_pow_sub_of_le hz h]
  simp_rw [map_sum, map_pow]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [← pow_mul]
  ring_nf

theorem norm_geomPowerSum_base_conj_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {r s : ℕ} (h : r ≤ s) :
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ =
      ‖geomPowerSum z k (s - r)‖ := by
  rw [geomPowerSum_base_conj_sub_of_le hz k h]
  rw [Complex.norm_conj]

theorem fejer_cross_term_reindex (z : ℂ) (p q r s : ℕ) :
    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
        starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) =
      (z ^ r * starRingEnd ℂ (z ^ s)) ^ p *
        starRingEnd ℂ ((z ^ r * starRingEnd ℂ (z ^ s)) ^ q) := by
  simp [map_mul, map_pow]
  ring

theorem fejer_pq_sum_eq_norm_sq (z : ℂ) (k r s : ℕ) :
    (∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
      (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
        starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s)) =
      ((‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2 : ℝ) : ℂ) := by
  rw [ofReal_norm_sq_eq_mul_conj]
  simp_rw [map_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [fejer_cross_term_reindex]

theorem fejerPairEnergy_eq_average_fejerBaseNormSum (z : ℂ) (k D : ℕ) :
    fejerPairEnergy z k D =
      (D + 1 : ℝ)⁻¹ *
        (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2) := by
  apply Complex.ofReal_injective
  calc
    ((fejerPairEnergy z k D : ℝ) : ℂ)
        = ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
            ((fejerPairTerm z D p q : ℝ) : ℂ) := by
          unfold fejerPairEnergy
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Complex.ofReal_sum]
    _ = ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
          ((D + 1 : ℝ)⁻¹ : ℂ) *
            ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
              (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          refine Finset.sum_congr rfl ?_
          intro q hq
          rw [ofReal_fejerPairTerm_eq_double_sum]
    _ = ((D + 1 : ℝ)⁻¹ : ℂ) *
          (∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
            ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
              (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.mul_sum]
    _ = ((D + 1 : ℝ)⁻¹ : ℂ) *
          (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
            ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
              (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s)) := by
          congr 1
          calc
            (∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
              ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
                (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                  starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s))
                = ∑ p ∈ Finset.range k, ∑ r ∈ Finset.range (D + 1),
                    ∑ q ∈ Finset.range k, ∑ s ∈ Finset.range (D + 1),
                      (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                        starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  rw [Finset.sum_comm]
            _ = ∑ p ∈ Finset.range k, ∑ r ∈ Finset.range (D + 1),
                  ∑ s ∈ Finset.range (D + 1), ∑ q ∈ Finset.range k,
                    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                      starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  rw [Finset.sum_comm]
            _ = ∑ r ∈ Finset.range (D + 1), ∑ p ∈ Finset.range k,
                  ∑ s ∈ Finset.range (D + 1), ∑ q ∈ Finset.range k,
                    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                      starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  rw [Finset.sum_comm]
            _ = ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
                  ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
                    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                      starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  rw [Finset.sum_comm]
    _ = ((D + 1 : ℝ)⁻¹ : ℂ) *
          (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
            ((‖∑ p ∈ Finset.range k,
              (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2 : ℝ) : ℂ)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro r hr
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [fejer_pq_sum_eq_norm_sq]
    _ = (((D + 1 : ℝ)⁻¹ *
          (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
            ‖∑ p ∈ Finset.range k,
              (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul, Complex.ofReal_inv]
          congr 1
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [Complex.ofReal_sum]

theorem sum_Ico_one_succ_eq_sum_range_succ (F : ℕ → ℝ) (D : ℕ) :
    (∑ d ∈ Finset.Ico 1 (D + 1), F d) =
      ∑ i ∈ Finset.range D, F (i + 1) := by
  simpa [Nat.Ico_zero_eq_range] using
    (Finset.sum_Ico_add' F 0 D 1).symm

theorem square_sum_eq_lower_diag_upper (F : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, F r s) =
      (∑ r ∈ Finset.range n, ∑ s ∈ Finset.range r, F r s)
        + (∑ r ∈ Finset.range n, F r r)
        + (∑ s ∈ Finset.range n, ∑ r ∈ Finset.range s, F r s) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Finset.sum_range_succ, ih, Finset.sum_add_distrib]
      ring

theorem sum_Ico_one_succ_le_sum_range_succ
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) {r D : ℕ} (hr : r ≤ D) :
    (∑ d ∈ Finset.Ico 1 (r + 1), F d) ≤
      ∑ i ∈ Finset.range D, F (i + 1) := by
  calc
    (∑ d ∈ Finset.Ico 1 (r + 1), F d)
        ≤ ∑ d ∈ Finset.Ico 1 (D + 1), F d := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            simp only [Finset.mem_Ico] at hd ⊢
            omega
          · intro d hdD hnot
            exact hF d
    _ = ∑ i ∈ Finset.range D, F (i + 1) := by
          rw [sum_Ico_one_succ_eq_sum_range_succ]

theorem lowerTriangle_row_sum_le_sum_range_succ
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) {r D : ℕ} (hr : r ≤ D) :
    (∑ s ∈ Finset.range r, F (r - s)) ≤
      ∑ i ∈ Finset.range D, F (i + 1) := by
  have hreflect :
      (∑ s ∈ Finset.range r, F (r - s)) =
        ∑ d ∈ Finset.Ico 1 (r + 1), F d := by
    simpa [Nat.Ico_zero_eq_range] using
      (Finset.sum_Ico_reflect F 0 (m := r) (n := r) (by omega))
  rw [hreflect]
  exact sum_Ico_one_succ_le_sum_range_succ F hF hr

theorem lowerTriangle_sum_le_mul_sum_range_succ
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) (D : ℕ) :
    (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, F (r - s)) ≤
      (D + 1 : ℝ) * (∑ i ∈ Finset.range D, F (i + 1)) := by
  calc
    (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, F (r - s))
        ≤ ∑ _r ∈ Finset.range (D + 1),
            (∑ i ∈ Finset.range D, F (i + 1)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact lowerTriangle_row_sum_le_sum_range_succ F hF (by
            simp only [Finset.mem_range] at hr
            omega)
    _ = (D + 1 : ℝ) * (∑ i ∈ Finset.range D, F (i + 1)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem lowerTriangle_geomPowerEnergy_le_mul
    (z : ℂ) (k D : ℕ) :
    (∑ r ∈ Finset.range (D + 1),
        ∑ s ∈ Finset.range r, ‖geomPowerSum z k (r - s)‖ ^ 2)
      ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
  simpa [geomPowerEnergy] using
    lowerTriangle_sum_le_mul_sum_range_succ
      (fun d => ‖geomPowerSum z k d‖ ^ 2)
      (fun d => sq_nonneg ‖geomPowerSum z k d‖) D

theorem lowerTriangle_fejerBaseNorm_le_mul
    {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (∑ r ∈ Finset.range (D + 1),
        ∑ s ∈ Finset.range r,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
      ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
  calc
    (∑ r ∈ Finset.range (D + 1),
        ∑ s ∈ Finset.range r,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
        = ∑ r ∈ Finset.range (D + 1),
            ∑ s ∈ Finset.range r, ‖geomPowerSum z k (r - s)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hsr : s ≤ r := by
            simp only [Finset.mem_range] at hs
            omega
          rw [norm_geomPowerSum_base_sub_of_le hz k hsr]
    _ ≤ (D + 1 : ℝ) * geomPowerEnergy z k D :=
          lowerTriangle_geomPowerEnergy_le_mul z k D

theorem upperTriangle_fejerBaseNorm_le_mul
    {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (∑ s ∈ Finset.range (D + 1),
        ∑ r ∈ Finset.range s,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
      ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
  calc
    (∑ s ∈ Finset.range (D + 1),
        ∑ r ∈ Finset.range s,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
        = ∑ s ∈ Finset.range (D + 1),
            ∑ r ∈ Finset.range s, ‖geomPowerSum z k (s - r)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hrs : r ≤ s := by
            simp only [Finset.mem_range] at hr
            omega
          rw [norm_geomPowerSum_base_conj_sub_of_le hz k hrs]
    _ ≤ (D + 1 : ℝ) * geomPowerEnergy z k D :=
          lowerTriangle_geomPowerEnergy_le_mul z k D

theorem fejerBase_diag_norm_sq {z : ℂ} (hz : ‖z‖ = 1) (k r : ℕ) :
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ r)) ^ p‖ ^ 2 =
      (k : ℝ) ^ 2 := by
  rw [fejerPair_diag_base_one hz r]
  simp

theorem diagonal_fejerBaseNorm_sum {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (∑ r ∈ Finset.range (D + 1),
        ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ r)) ^ p‖ ^ 2)
      = (D + 1 : ℝ) * (k : ℝ) ^ 2 := by
  calc
    (∑ r ∈ Finset.range (D + 1),
        ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ r)) ^ p‖ ^ 2)
        = ∑ _r ∈ Finset.range (D + 1), (k : ℝ) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact fejerBase_diag_norm_sq hz k r
    _ = (D + 1 : ℝ) * (k : ℝ) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem fejerPairEnergy_le_sq_add_two_energy
    {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    fejerPairEnergy z k D ≤ (k : ℝ) ^ 2 + 2 * geomPowerEnergy z k D := by
  let B : ℕ → ℕ → ℝ := fun r s =>
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2
  let S : ℝ := ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1), B r s
  have hsplit :
      S =
        (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, B r s)
          + (∑ r ∈ Finset.range (D + 1), B r r)
          + (∑ s ∈ Finset.range (D + 1), ∑ r ∈ Finset.range s, B r s) := by
    simpa [S, B] using square_sum_eq_lower_diag_upper B (D + 1)
  have hlower :
      (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, B r s)
        ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
    simpa [B] using lowerTriangle_fejerBaseNorm_le_mul hz k D
  have hupper :
      (∑ s ∈ Finset.range (D + 1), ∑ r ∈ Finset.range s, B r s)
        ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
    simpa [B] using upperTriangle_fejerBaseNorm_le_mul hz k D
  have hdiag :
      (∑ r ∈ Finset.range (D + 1), B r r) =
        (D + 1 : ℝ) * (k : ℝ) ^ 2 := by
    simpa [B] using diagonal_fejerBaseNorm_sum hz k D
  have hSle :
      S ≤ (D + 1 : ℝ) * (k : ℝ) ^ 2
          + (D + 1 : ℝ) * geomPowerEnergy z k D
          + (D + 1 : ℝ) * geomPowerEnergy z k D := by
    rw [hsplit, hdiag]
    nlinarith
  rw [fejerPairEnergy_eq_average_fejerBaseNormSum]
  change (D + 1 : ℝ)⁻¹ * S ≤ (k : ℝ) ^ 2 + 2 * geomPowerEnergy z k D
  calc
    (D + 1 : ℝ)⁻¹ * S
        ≤ (D + 1 : ℝ)⁻¹ *
            ((D + 1 : ℝ) * (k : ℝ) ^ 2
              + (D + 1 : ℝ) * geomPowerEnergy z k D
              + (D + 1 : ℝ) * geomPowerEnergy z k D) := by
          exact mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = (k : ℝ) ^ 2 + 2 * geomPowerEnergy z k D := by
          have hpos : (0 : ℝ) < D + 1 := by positivity
          field_simp [ne_of_gt hpos]
          ring

theorem fejerPairEnergy_diag_lower {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (k : ℝ) * (D + 1 : ℝ) ≤ fejerPairEnergy z k D := by
  unfold fejerPairEnergy
  calc
    (k : ℝ) * (D + 1 : ℝ)
        = ∑ p ∈ Finset.range k, (D + 1 : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k, fejerPairTerm z D p q := by
          refine Finset.sum_le_sum ?_
          intro p hp
          rw [← fejerPair_diag_term hz p D]
          exact Finset.single_le_sum (fun q hq => fejerPairTerm_nonneg z D p q) hp

/--
The remaining scalar power-sum claim behind the report's Fejér lower bound.

For `D = 2*k`, this says `geomPowerEnergy z k (2*k) >= k*(k+1)/2` for every
unit complex number `z`.-/
def casselsGeomLowerClaim (k D : ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → casselsRhs k D ≤ geomPowerEnergy z k D

theorem casselsGeomLowerClaim_true (k D : ℕ) :
    casselsGeomLowerClaim k D := by
  intro z hz
  have hlo := fejerPairEnergy_diag_lower (z := z) hz k D
  have hhi := fejerPairEnergy_le_sq_add_two_energy (z := z) hz k D
  unfold casselsRhs
  nlinarith

variable [NeZero N]

/-- Fourier coefficient with respect to Mathlib's character basis on `ZMod N`.-/
noncomputable def fourierCoeff
    (f : ZMod N → ℂ) (ψ : AddChar (ZMod N) ℂ) : ℂ :=
  (AddChar.complexBasis (ZMod N)).repr f ψ

/-- Pointwise expansion of a function in the character basis.-/
theorem fourier_expansion
    (f : ZMod N → ℂ) (x : ZMod N) :
    f x = ∑ ψ : AddChar (ZMod N) ℂ, fourierCoeff f ψ * ψ x := by
  have h := congrFun ((AddChar.complexBasis (ZMod N)).sum_repr f) x
  simpa [fourierCoeff, AddChar.complexBasis_apply] using h.symm

/-- Orthogonality of characters, unfolded as a normalized finite sum.-/
theorem addChar_expect_mul_conj_eq_boole
    (ψ χ : AddChar (ZMod N) ℂ) :
    (Finset.univ.expect fun a : ZMod N => ψ a * starRingEnd ℂ (χ a))
      = if χ = ψ then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  rw [RCLike.wInner_cWeight_eq_expect] at h
  simpa [RCLike.inner_apply] using h

/-- A finite linear combination of characters.-/
noncomputable def charCombination
    (c : AddChar (ZMod N) ℂ → ℂ) (a : ZMod N) : ℂ :=
  ∑ ψ : AddChar (ZMod N) ℂ, c ψ * ψ a

/--
Normalized Parseval for finite character combinations.

This is the algebraic core needed to pass from a general coloring to its character
components in the Fejér lower-bound argument.-/
theorem expect_charCombination_mul_conj
    (c b : AddChar (ZMod N) ℂ → ℂ) :
    (Finset.univ.expect fun a : ZMod N =>
        charCombination c a * starRingEnd ℂ (charCombination b a))
      = ∑ ψ : AddChar (ZMod N) ℂ, c ψ * starRingEnd ℂ (b ψ) := by
  classical
  unfold charCombination
  simp_rw [map_sum, map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  refine Finset.sum_congr rfl ?_
  intro ψ hψ
  rw [Finset.expect_sum_comm]
  calc
    (∑ χ : AddChar (ZMod N) ℂ,
        Finset.univ.expect fun a : ZMod N =>
          c ψ * ψ a * (starRingEnd ℂ (b χ) * starRingEnd ℂ (χ a)))
        = ∑ χ : AddChar (ZMod N) ℂ,
            c ψ * starRingEnd ℂ (b χ) *
              (Finset.univ.expect fun a : ZMod N => ψ a * starRingEnd ℂ (χ a)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          calc
            (Finset.univ.expect fun a : ZMod N =>
                c ψ * ψ a * (starRingEnd ℂ (b χ) * starRingEnd ℂ (χ a)))
                = Finset.univ.expect fun a : ZMod N =>
                    (c ψ * starRingEnd ℂ (b χ)) * (ψ a * starRingEnd ℂ (χ a)) := by
                    refine Finset.expect_congr rfl ?_
                    intro a ha
                    ring
            _ = c ψ * starRingEnd ℂ (b χ) *
                  (Finset.univ.expect fun a : ZMod N => ψ a * starRingEnd ℂ (χ a)) := by
                    rw [← Finset.mul_expect]
    _ = c ψ * starRingEnd ℂ (b ψ) := by
          simp_rw [addChar_expect_mul_conj_eq_boole]
          simp

/-- The Fourier expansion restated using `charCombination`.-/
theorem charCombination_fourierCoeff
    (f : ZMod N → ℂ) (a : ZMod N) :
    charCombination (fourierCoeff f) a = f a := by
  simpa [charCombination] using (fourier_expansion f a).symm

/-- The Fourier coefficient of the AP-sum function for a fixed difference.-/
noncomputable def apFourierCoeff
    (f : ZMod N → ℂ) (k : ℕ) (d : ZMod N)
    (ψ : AddChar (ZMod N) ℂ) : ℂ :=
  fourierCoeff f ψ * ∑ j ∈ Finset.range k, ψ (j • d)

end FourierSetup

section FinZModBridge

variable {N : ℕ} [NeZero N]

/-- The canonical equivalence between residues represented as `Fin N` and `ZMod N`.-/
def finZModEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun a := (a.val : ZMod N)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv a := by
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt a.isLt]
  right_inv x := by
    exact ZMod.natCast_zmod_val x

/-- Move an integer `±1` coloring on `Fin N` to a complex-valued coloring on `ZMod N`.-/
noncomputable def zmodColoringOfFin (f : Fin N → ℤ) (x : ZMod N) : ℂ :=
  ((f ((finZModEquiv N).symm x) : ℤ) : ℂ)

theorem zmodColoringOfFin_unit
    (f : Fin N → ℤ) (hpm : ∀ x, f x = -1 ∨ f x = 1) :
    ∀ x : ZMod N, ‖zmodColoringOfFin f x‖ = 1 := by
  intro x
  unfold zmodColoringOfFin
  rcases hpm ((finZModEquiv N).symm x) with h | h <;> simp [h]

end FinZModBridge

/-- Real-valued version of the report's wrap-error term after setting `D = 2*k`.-/
noncomputable def wrapUpperReal (k N : ℝ) : ℝ :=
  1 + ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (2 * N)

/-- Real-valued Fejér lower bound after setting `D = 2*k`.-/
noncomputable def fejerLowerDTwoKReal (k : ℝ) : ℝ :=
  (k + 1) / 4

section FinalSynthesis

variable {N : ℕ} [NeZero N]

theorem int_two_mul_succ_div_two_real (k : ℕ) :
    ((((2 * k : ℤ) * (2 * k + 1 : ℤ)) / 2 : ℤ) : ℝ)
      = (k : ℝ) * (2 * k + 1 : ℝ) := by
  have hZ :
      (((2 * k : ℤ) * (2 * k + 1 : ℤ)) / 2 : ℤ)
        = (k : ℤ) * (2 * k + 1 : ℤ) := by
    rw [show (2 * k : ℤ) * (2 * k + 1 : ℤ) =
        ((k : ℤ) * (2 * k + 1 : ℤ)) * 2 by ring]
    exact Int.mul_ediv_cancel ((k : ℤ) * (2 * k + 1 : ℤ)) (by norm_num : (2 : ℤ) ≠ 0)
  rw [hZ]
  norm_num

end FinalSynthesis

/-- The real threshold appearing in the HTML report.-/
noncomputable def htmlThresholdReal (k : ℕ) : ℝ :=
  2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
    / ((k : ℝ) - 3)

/-- The report's displayed integer upper bound, `floor(threshold) + 1`.-/
noncomputable def htmlBoundNat (k : ℕ) : ℕ :=
  Nat.floor (htmlThresholdReal k) + 1

theorem htmlBoundNat_pos (k : ℕ) :
    0 < htmlBoundNat k := by
  simp [htmlBoundNat]

/--
For a fixed coloring on `[0, N)`, there is a non-wrapping ordinary `k`-term
AP with discrepancy at least `2`.-/
def hasLargeOrdinaryAPAt
    (k N : ℕ) (hNpos : 0 < N) (f : Fin N → ℤ) : Prop :=
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  ∃ d : ℕ, 0 < d ∧ ∃ a : Fin N,
    ∃ hnowrap : ¬ wraps (N := N) k a d,
      2 ≤ |ordinaryAPSum f k a d hnowrap|

/--
The formalized `N(k,2)` property used here: every `±1` coloring of `[0, N)`
has a non-wrapping ordinary `k`-term AP whose sum has absolute value at least
`2`.-/
def erdos176Good (k N : ℕ) : Prop :=
  ∃ hNpos : 0 < N,
    ∀ f : Fin N → ℤ,
      (∀ x, f x = -1 ∨ f x = 1) →
        hasLargeOrdinaryAPAt k N hNpos f

/-- Public-facing name for the report's displayed bound.-/
noncomputable abbrev reportBound (k : ℕ) : ℕ :=
  htmlBoundNat k

/-- The report's wrap-error term after setting `D = 2*k`.-/
noncomputable def wrapUpper (k N : ℚ) : ℚ :=
  1 + ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (2 * N)

/-- The Fejér lower bound from the report after setting `D = 2*k`.-/
noncomputable def fejerLowerDTwoK (k : ℚ) : ℚ :=
  (k + 1) / 4

end Erdos176Lean
