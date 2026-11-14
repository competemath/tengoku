import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Formal statements corresponding to the two main results in the paper.

The analytic definitions of the rates `r`, `s`, and `C` are developed in
separate modules. Keeping the statement layer independent lets Comparator
compare the trusted challenge before those long proofs are assembled.
-/

namespace PiIrrationality

open Filter
open scoped Topology

def IrrationalityMeasureAtMost (theta mu : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ q0 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q0 ≤ q → 0 < q →
        |theta - (p : ℝ) / (q : ℝ)| > (q : ℝ) ^ (-mu - eps)

noncomputable def IrrationalityMeasure (theta : ℝ) : ℝ :=
  sInf {mu : ℝ | IrrationalityMeasureAtMost theta mu}

def Admissible (p : ℝ × ℝ) : Prop :=
  p.1 + p.2 > 1 ∧
  2 * p.2 > 1 ∧
  7 * p.2 < 5 ∧
  2 * p.1 + 4 * p.2 - 2 > 1

def StrictLocalMinimizer (f : ℝ × ℝ → ℝ) (domain : ℝ × ℝ → Prop)
    (p0 : ℝ × ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∀ p : ℝ × ℝ, domain p → p ≠ p0 →
      ‖p - p0‖ < delta → f p0 < f p

noncomputable def AuxiliaryBound (r s cost : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  1 + (r p + cost p) / (-s p - cost p)

noncomputable def candidate : ℝ × ℝ :=
  ((1857 : ℝ) / 5570, (1857 : ℝ) / 2785)

/- Theorem 1.1, with the paper's decimal written as an exact rational. -/
noncomputable def theorem11 : Prop :=
  IrrationalityMeasure Real.pi < ((7101862832357 : ℝ) / 10^12)

/- Theorem 1.2, parameterized until the analytic rate functions are defined. -/
noncomputable def theorem12 (r s cost : ℝ × ℝ → ℝ) : Prop :=
  StrictLocalMinimizer (AuxiliaryBound r s cost) Admissible candidate

/--
@isnad1 id=admissib.0h0v.s1.3cc4e7e87e95 from=translated src=- shape=49959d42 vocab=593dff82
-/
theorem candidate_admissible : Admissible candidate := by
  norm_num [Admissible, candidate]

/--
@isnad1 id=irration.2h3v.s4.4d630092745c from=translated src=- shape=847200ad vocab=c9bd228c
-/
theorem IrrationalityMeasureAtMost.mono {theta mu mu' : ℝ}
    (hmu : IrrationalityMeasureAtMost theta mu) (h : mu ≤ mu') :
    IrrationalityMeasureAtMost theta mu' := by
  intro eps heps
  obtain ⟨q0, hq0⟩ := hmu eps heps
  refine ⟨q0, ?_⟩
  intro p q hq0' hqpos
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))
  have hexp : -mu' - eps ≤ -mu - eps := by linarith
  have hpow : (q : ℝ) ^ (-mu' - eps) ≤ (q : ℝ) ^ (-mu - eps) :=
    Real.rpow_le_rpow_of_exponent_le hqone hexp
  exact lt_of_le_of_lt hpow (hq0 p q hq0' hqpos)

/--
@isnad1 id=eq.0h0v.s5.f859def853a3 from=translated src=- shape=6d0f34e9 vocab=9e37e9cd
-/
theorem candidate_coordinates :
    candidate = ((1857 : ℝ) / 5570, (1857 : ℝ) / 2785) := rfl

/--
@isnad1 id=le.2h2v.s4.643414659ddd from=translated src=- shape=93c604c6 vocab=3192e72c
-/
theorem irrationalityMeasure_le_of_atMost (theta mu : ℝ)
    (hBdd : BddBelow {x : ℝ | IrrationalityMeasureAtMost theta x})
    (hmu : IrrationalityMeasureAtMost theta mu) :
    IrrationalityMeasure theta ≤ mu := by
  unfold IrrationalityMeasure
  exact csInf_le hBdd hmu

/--
@isnad1 id=theorem1.2h0v.s5.a5119fd20e33 from=translated src=- shape=b7f58aa7 vocab=8e65c657
-/
theorem theorem11_of_atMost_bound
    (hBdd : BddBelow {x : ℝ | IrrationalityMeasureAtMost Real.pi x})
    (hbound : IrrationalityMeasureAtMost Real.pi
      ((7101862832356 : ℝ) / 10^12)) : theorem11 := by
  unfold theorem11
  exact lt_of_le_of_lt
    (irrationalityMeasure_le_of_atMost Real.pi _ hBdd hbound) (by norm_num)

/--
@isnad1 id=irration.2h3v.s7.688c422f3984 from=translated src=- shape=9ed6f0a1 vocab=8a337ea3
-/
theorem irrationalityMeasureAtMost_of_uniform_power_bound
    {theta kappa c : ℝ}
    (hpower : ∃ q1 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q1 ≤ q → 0 < q →
        |theta - (p : ℝ) / (q : ℝ)| > c * (q : ℝ) ^ (-1 - kappa))
    (htail : ∀ eps : ℝ, 0 < eps → ∃ q2 : ℕ, ∀ q : ℕ,
      q2 ≤ q → (q : ℝ) ^ (-eps) < c) :
    IrrationalityMeasureAtMost theta (1 + kappa) := by
  intro eps heps
  obtain ⟨q1, hq1⟩ := hpower
  obtain ⟨q2, hq2⟩ := htail eps heps
  refine ⟨max q1 q2, ?_⟩
  intro p q hq hqpos
  have hq1' : q1 ≤ q := le_trans (Nat.le_max_left _ _) hq
  have hq2' : q2 ≤ q := le_trans (Nat.le_max_right _ _) hq
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have htail' : (q : ℝ) ^ (-eps) < c := hq2 q hq2'
  have hpowpos : 0 < (q : ℝ) ^ (-1 - kappa) :=
    Real.rpow_pos_of_pos hqreal _
  have hprod : (q : ℝ) ^ (-eps) * (q : ℝ) ^ (-1 - kappa) <
      c * (q : ℝ) ^ (-1 - kappa) :=
    mul_lt_mul_of_pos_right htail' hpowpos
  calc
    |theta - (p : ℝ) / (q : ℝ)| >
        c * (q : ℝ) ^ (-1 - kappa) := hq1 p q hq1' hqpos
    _ > (q : ℝ) ^ (-eps) * (q : ℝ) ^ (-1 - kappa) := hprod
    _ = (q : ℝ) ^ (-(1 + kappa) - eps) := by
      rw [← Real.rpow_add hqreal]
      congr 1
      ring

/--
@isnad1 id=ex.2h2v.s5.f0835d41d15c from=translated src=- shape=6249677c vocab=6a8d15ab
-/
theorem rpow_neg_eventually_lt
    {c eps : ℝ} (hc : 0 < c) (heps : 0 < eps) :
    ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q → (q : ℝ) ^ (-eps) < c := by
  have hlim : Tendsto (fun q : ℕ => (q : ℝ) ^ (-eps)) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop heps).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨q0, hq0⟩ := eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds hc))
  refine ⟨q0, ?_⟩
  intro q hq
  exact hq0 q hq

/--
@isnad1 id=irration.2h3v.s6.a45a16e587f9 from=translated src=- shape=bc44eb4b vocab=8a337ea3
-/
theorem irrationalityMeasureAtMost_of_uniform_power_bound_of_pos_constant
    {theta kappa c : ℝ} (hc : 0 < c)
    (hpower : ∃ q1 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q1 ≤ q → 0 < q →
        |theta - (p : ℝ) / (q : ℝ)| > c * (q : ℝ) ^ (-1 - kappa)) :
    IrrationalityMeasureAtMost theta (1 + kappa) := by
  apply irrationalityMeasureAtMost_of_uniform_power_bound hpower
  intro eps heps
  exact rpow_neg_eventually_lt hc heps

/--
@isnad1 id=theorem1.4h2v.s7.2adba5bb1c96 from=translated src=- shape=8ba39556 vocab=a71a9d73
-/
theorem theorem11_of_uniform_power_bound
    (hBdd : BddBelow {x : ℝ | IrrationalityMeasureAtMost Real.pi x})
    {kappa c : ℝ}
    (hpower : ∃ q1 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q1 ≤ q → 0 < q →
        |Real.pi - (p : ℝ) / (q : ℝ)| > c * (q : ℝ) ^ (-1 - kappa))
    (htail : ∀ eps : ℝ, 0 < eps → ∃ q2 : ℕ, ∀ q : ℕ,
      q2 ≤ q → (q : ℝ) ^ (-eps) < c)
    (hkappa : 1 + kappa ≤ (7101862832356 : ℝ) / 10^12) : theorem11 := by
  have hmu := irrationalityMeasureAtMost_of_uniform_power_bound hpower htail
  have hmu' := IrrationalityMeasureAtMost.mono hmu hkappa
  exact theorem11_of_atMost_bound hBdd hmu'

/--
@isnad1 id=theorem1.4h2v.s7.ea1723ac3b63 from=translated src=- shape=a61a0edc vocab=a71a9d73
-/
theorem theorem11_of_uniform_power_bound_of_pos_constant
    (hBdd : BddBelow {x : ℝ | IrrationalityMeasureAtMost Real.pi x})
    {kappa c : ℝ} (hc : 0 < c)
    (hpower : ∃ q1 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q1 ≤ q → 0 < q →
        |Real.pi - (p : ℝ) / (q : ℝ)| > c * (q : ℝ) ^ (-1 - kappa))
    (hkappa : 1 + kappa ≤ (7101862832356 : ℝ) / 10^12) : theorem11 := by
  have hmu := irrationalityMeasureAtMost_of_uniform_power_bound_of_pos_constant hc hpower
  have hmu' := IrrationalityMeasureAtMost.mono hmu hkappa
  exact theorem11_of_atMost_bound hBdd hmu'

end PiIrrationality
