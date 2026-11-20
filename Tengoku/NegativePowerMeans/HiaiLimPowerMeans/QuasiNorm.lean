import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.MainTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Schatten quasi-norm consequence

This file derives the Schatten `q`-(quasi-)norm inequality from the paper's
weak log-majorization theorem.  It contains the two scalar ingredients needed
for that deduction: positive moment monotonicity under weak log-majorization
and superadditivity of negative scalar power means.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- Every positive moment is monotone under weak log-majorization.-/
theorem WeakLogMajorized.sum_rpow_le_sum_rpow
    {n : ℕ} {x y : Fin n → ℝ} (h : WeakLogMajorized x y)
    {q : ℝ} (hq : 0 < q) :
    (∑ i, (x i) ^ q) ≤ ∑ i, (y i) ^ q := by
  rcases h with ⟨⟨hx0, hx⟩, ⟨hy0, hy⟩, hprod⟩
  have hlogx : Antitone (fun i ↦ Real.log (x i)) := by
    intro i j hij
    exact Real.strictMonoOn_log.monotoneOn (by simpa using hx0 j)
      (by simpa using hx0 i) (hx hij)
  have hlogy : Antitone (fun i ↦ Real.log (y i)) := by
    intro i j hij
    exact Real.strictMonoOn_log.monotoneOn (by simpa using hy0 j)
      (by simpa using hy0 i) (hy hij)
  have hprefix : ∀ (k : ℕ) (hk : k ≤ n),
      (∑ i : Fin k, Real.log (x (Fin.castLE hk i))) ≤
        ∑ i : Fin k, Real.log (y (Fin.castLE hk i)) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hp := hprod k hkpos hk
    change (∏ i : Fin k, x (Fin.castLE hk i)) ≤
      ∏ i : Fin k, y (Fin.castLE hk i) at hp
    have hxprod : 0 < ∏ i : Fin k, x (Fin.castLE hk i) :=
      Finset.prod_pos fun i _ ↦ hx0 _
    have hyprod : 0 < ∏ i : Fin k, y (Fin.castLE hk i) :=
      Finset.prod_pos fun i _ ↦ hy0 _
    rw [← Real.log_prod (fun i _ ↦ (hx0 _).ne'),
      ← Real.log_prod (fun i _ ↦ (hy0 _).ne')]
    exact Real.strictMonoOn_log.monotoneOn (by simpa using hxprod)
      (by simpa using hyprod) hp
  have hexp := sum_exp_le_sum_exp_of_fin_prefix hlogx hlogy hprefix hq
  calc
    (∑ i, (x i) ^ q) = ∑ i, Real.exp (q * Real.log (x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_def_of_pos (hx0 i)]
      congr 1
      ring
    _ ≤ ∑ i, Real.exp (q * Real.log (y i)) := hexp
    _ = ∑ i, (y i) ^ q := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_def_of_pos (hy0 i)]
      congr 1
      ring

/-- Weighted Jensen inequality for a negative real power.  It is proved from
weighted AM--GM, so no analytic concavity result is assumed.-/
private theorem weighted_rpow_neg_le
    {n : ℕ} [NeZero n] {a z : Fin n → ℝ} {s : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1)
    (hz : ∀ i, 0 < z i) (hs : s < 0) :
    (∑ i, a i * z i) ^ s ≤ ∑ i, a i * (z i) ^ s := by
  have hgm := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin n)) a z
    (by simpa using ha) (by simpa using hasum)
    (by simpa using fun i ↦ (hz i).le)
  have hprodpos : 0 < ∏ i, (z i) ^ (a i) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hz i) _
  have hsumpos : 0 < ∑ i, a i * z i := lt_of_lt_of_le hprodpos hgm
  have hreverse :
      (∑ i, a i * z i) ^ s ≤ (∏ i, (z i) ^ (a i)) ^ s :=
    (Real.rpow_le_rpow_iff_of_neg hsumpos hprodpos hs).2 hgm
  have hreorder :
      (∏ i, (z i) ^ (a i)) ^ s = ∏ i, ((z i) ^ s) ^ (a i) := by
    rw [← Real.finsetProd_rpow Finset.univ (fun i ↦ (z i) ^ (a i))
      (fun i _ ↦ Real.rpow_nonneg (hz i).le _) s]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_mul (hz i).le, ← Real.rpow_mul (hz i).le]
    congr 1
    ring
  have hgmPower := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin n)) a (fun i ↦ (z i) ^ s)
    (by simpa using ha) (by simpa using hasum)
    (by simpa using fun i ↦ (Real.rpow_pos_of_pos (hz i) s).le)
  calc
    (∑ i, a i * z i) ^ s ≤ (∏ i, (z i) ^ (a i)) ^ s := hreverse
    _ = ∏ i, ((z i) ^ s) ^ (a i) := hreorder
    _ ≤ ∑ i, a i * (z i) ^ s := by simpa using hgmPower

/-- A negative scalar power mean is superadditive on positive vectors.-/
theorem sum_powerCoordinate_le
    {n m : ℕ} [NeZero n] [NeZero m]
    {w : Fin m → ℝ} {x : Fin n → Fin m → ℝ} {s : ℝ}
    (hw : ∀ j, 0 < w j)
    (hx : ∀ i j, 0 < x i j) (hs : s < 0) :
    (∑ i, powerCoordinate w (x i) s) ≤
      powerCoordinate w (fun j ↦ ∑ i, x i j) s := by
  let u : Fin n → ℝ := fun i ↦ powerCoordinate w (x i) s
  let U : ℝ := ∑ i, u i
  let a : Fin n → ℝ := fun i ↦ u i / U
  have hu : ∀ i, 0 < u i := fun i ↦ powerCoordinate_pos hw (hx i)
  have hU : 0 < U := Finset.sum_pos
    (fun i _ ↦ hu i) Finset.univ_nonempty
  have ha : ∀ i, 0 ≤ a i := fun i ↦ div_nonneg (hu i).le hU.le
  have hasum : ∑ i, a i = 1 := by
    rw [show (∑ i, a i) = U / U by simp [a, U, Finset.sum_div]]
    exact div_self hU.ne'
  have hjensen : ∀ j,
      (∑ i, a i * (x i j / u i)) ^ s ≤
        ∑ i, a i * (x i j / u i) ^ s := by
    intro j
    exact weighted_rpow_neg_le ha hasum
      (fun i ↦ div_pos (hx i j) (hu i)) hs
  have hweighted := Finset.sum_le_sum fun j (_hj : j ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (hjensen j) (hw j).le
  have hleft :
      (∑ j, w j * (∑ i, a i * (x i j / u i)) ^ s) =
        ∑ j, w j * ((∑ i, x i j) / U) ^ s := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    congr 1
    calc
      (∑ i, a i * (x i j / u i)) = ∑ i, x i j / U := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [a]
        field_simp [hU.ne', (hu i).ne']
      _ = (∑ i, x i j) / U := by rw [Finset.sum_div]
  have hright :
      (∑ j, w j * ∑ i, a i * (x i j / u i) ^ s) = 1 := by
    calc
      (∑ j, w j * ∑ i, a i * (x i j / u i) ^ s) =
          ∑ j, ∑ i, w j * (a i * (x i j / u i) ^ s) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, w j * (a i * (x i j / u i) ^ s) :=
        Finset.sum_comm
      _ = ∑ i, a i * ∑ j, w j * (x i j / u i) ^ s := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, a i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← powerCoordinate_div_rpow_of_ne hw (hx i) (hu i) hs.ne]
        change a i * (u i / u i) ^ s = a i
        rw [div_self (hu i).ne']
        simp
      _ = 1 := hasum
  rw [hleft, hright] at hweighted
  let v : ℝ := powerCoordinate w (fun j ↦ ∑ i, x i j) s
  have hxsum : ∀ j, 0 < ∑ i, x i j := fun j ↦
    Finset.sum_pos (fun i _ ↦ hx i j) Finset.univ_nonempty
  have hv : 0 < v := powerCoordinate_pos hw hxsum
  have hratioPower : (v / U) ^ s ≤ 1 := by
    rw [powerCoordinate_div_rpow_of_ne hw hxsum hU hs.ne]
    exact hweighted
  have honeRatio : 1 ≤ v / U :=
    (Real.rpow_le_rpow_iff_of_neg (div_pos hv hU) zero_lt_one hs).1
      (by simpa using hratioPower)
  exact (one_le_div hU).1 honeRatio

/-- The Schatten `q`-quantity of a positive-definite matrix, defined from its
ordered eigenvalues.  It is a norm for `q ≥ 1` and a quasi-norm for
`0 < q < 1`.-/
noncomputable def schattenQ {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (q : ℝ) : ℝ :=
  (∑ i, (decreasingEigenvalues hA.isHermitian i) ^ q) ^ q⁻¹

lemma schattenQ_pos {n : ℕ} [NeZero n]
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (q : ℝ) :
    0 < schattenQ hA q := by
  unfold schattenQ
  apply Real.rpow_pos_of_pos
  exact Finset.sum_pos
    (fun i _ ↦ Real.rpow_pos_of_pos
      (Matrix.PosDef.decreasingEigenvalues_pos hA i) q)
    Finset.univ_nonempty

end HiaiLimPowerMeans
