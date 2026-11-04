import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Parts.UnitPairCount
import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Parts.CoprimeSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Duffin–Schaeffer — Part 9: the overlap estimate (KM Lemma 5.3, Pollington–Vaughan)

For `q ≠ r`:
`λ(A_q ∩ A_r) ≪ w(q) w(r) ∏_{p | qr/gcd², p > M(q,r)/gcd(q,r)} (1 + 1/p)`.
No restriction `ψ ≤ 1/2` is needed (KM assume it only because they cite PV).
Proof: union bound over arcs, `λ(I_a ∩ J_b) ≤ 2 min(ψ(q)/q, ψ(r)/r)`, nonzero only if
`h = a r' - b q'` has `0 < |h| < (rψ(q) + qψ(r))/g ≤ 2M/g`; count with `card_unit_pairs_le`
and sum over `h` with `sieve_weighted_coprime`; primes `p ≤ (M/g)` cancel against `m/φ(m)`.
-/

open MeasureTheory Finset

namespace DuffinSchaeffer

/-- Two balls in `ℝ/ℤ` intersect in measure at most `2 min(δ, ε)`.
@isnad1 id=le.2h4v.s7.c8acc9d1bf14 from=translated src=- shape=6efe882d vocab=785cae89
-/
theorem ovl_ball_inter_le (x y : UnitAddCircle) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume.real (Metric.ball x δ ∩ Metric.ball y ε) ≤ 2 * min δ ε := by
  have key : ∀ (z : UnitAddCircle) (η : ℝ), 0 ≤ η → volume.real (Metric.ball z η) ≤ 2 * η := by
    intro z η hη
    calc volume.real (Metric.ball z η) ≤ volume.real (Metric.closedBall z η) :=
          measureReal_mono Metric.ball_subset_closedBall
      _ = min 1 (2 * η) := by
          rw [measureReal_def, AddCircle.volume_closedBall,
            ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]
      _ ≤ 2 * η := min_le_right _ _
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  exact le_min ((measureReal_mono Set.inter_subset_left).trans (key x δ hδ))
    ((measureReal_mono Set.inter_subset_right).trans (key y ε hε))

/-- `A_q ∩ A_r` is covered by the intersections of arcs around `a/q`, `b/r` whose centres are
at distance `< ψ(q)/q + ψ(r)/r`.
@isnad1 id=le.2h3v.s11.8864ecd2b0e3 from=translated src=- shape=54dc1e1c vocab=1fe1b070
-/
theorem ovl_cover (ψ : ℕ → ℝ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    Aq ψ q ∩ Aq ψ r ⊆ ⋃ ab ∈ ((range q ×ˢ range r).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        dist (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) <
          ψ q / q + ψ r / r)),
      Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (ψ q / q) ∩
        Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) (ψ r / r) := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨b1, hb1, hxb1⟩ := mem_approx_add_orderOf_iff.1 hx1
  obtain ⟨b2, hb2, hxb2⟩ := mem_approx_add_orderOf_iff.1 hx2
  obtain ⟨a, ha, hag, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hq).1 hb1
  obtain ⟨b, hb, hbg, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hr).1 hb2
  simp only [mul_one] at hxb1 hxb2
  refine Set.mem_biUnion (x := (a, b)) ?_ ⟨hxb1, hxb2⟩
  refine mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 ha, mem_range.2 hb⟩, hag, hbg, ?_⟩
  rw [Metric.mem_ball] at hxb1 hxb2
  calc dist _ _ ≤ dist (((a : ℝ) / q : ℝ) : UnitAddCircle) x +
        dist x (((b : ℝ) / r : ℝ) : UnitAddCircle) := dist_triangle _ _ _
    _ < _ := add_lt_add (by rw [dist_comm]; exact hxb1) hxb2

/-- `a/q - b/r = (a r' - b q') / lcm(q,r)`.
@isnad1 id=eq.2h4v.s7.260d5ad021dc from=translated src=- shape=56a5b03a vocab=3903d383
-/
theorem ovl_arith (q r a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (a : ℝ) / q - b / r =
      (((a : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (b : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) : ℤ) : ℝ) /
        (Nat.lcm q r : ℝ) := by
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have h1 : ((Nat.gcd q r : ℕ) : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) = q := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have h2 : ((Nat.gcd q r : ℕ) : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) = r := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have h3 : ((Nat.gcd q r : ℕ) : ℝ) * (Nat.lcm q r : ℝ) = q * r := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  have hgR : ((Nat.gcd q r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hL : (Nat.lcm q r : ℝ) = q * r / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h3
  have hq' : ((q / Nat.gcd q r : ℕ) : ℝ) = q / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h1
  have hr' : ((r / Nat.gcd q r : ℕ) : ℝ) = r / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h2
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    Int.cast_natCast, Int.cast_natCast, hq', hr', hL]
  field_simp

/-- Telescoping: `∏_{n=2}^{N} (1 - 1/n²) = (N+1)/(2N)`.
@isnad1 id=eq.1h1v.s6.5309877137c5 from=translated src=- shape=4e050403 vocab=3d03b61d
-/
theorem ovl_prod_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∏ n ∈ Icc 2 N, (1 - 1 / (n : ℝ) ^ 2) = ((N : ℝ) + 1) / (2 * (N : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by norm_num)]; norm_num
  | succ N hN ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have : (0:ℝ) < N := by exact_mod_cast hN
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

end DuffinSchaeffer
