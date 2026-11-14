import Tengoku.Piirrationalitymeasure.Formalization.ConstructionArithmetic
import Tengoku.Piirrationalitymeasure.Formalization.ParameterSaving
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldDeletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! General prime selection, the strict initial gap (6.63)--(6.64), and finite-field primitives. -/

namespace PiIrrationality

def constructionSavingCondition (a b c : ℕ) (u : ℝ) : Prop :=
  Int.fract ((a : ℝ) * u + 1 / 2) + 2 * Int.fract ((b : ℝ) * u) <
    Int.fract ((c : ℝ) * u)

def constructionSavingSet (a b c : ℕ) : Set ℝ :=
  {u | 0 ≤ u ∧ u < 1 ∧ constructionSavingCondition a b c u}

def constructionRemovablePrime (a b c n p : ℕ) : Prop :=
  Nat.Prime p ∧ 5 < p ∧ Nat.sqrt (constructionDegree a b c * n) < p ∧
    p ≤ constructionDegree a b c * n ∧
    Int.fract (((a * n : ℕ) : ℚ) / p + 1 / 2) +
      2 * Int.fract (((b * n : ℕ) : ℚ) / p) < Int.fract (((c * n : ℕ) : ℚ) / p)

noncomputable def constructionRemovablePrimes (a b c n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (constructionDegree a b c * n)).filter
    (constructionRemovablePrime a b c n)

noncomputable def constructionPhi (a b c n : ℕ) : ℕ :=
  (constructionRemovablePrimes a b c n).prod id

theorem constructionSavingCondition_iff_chi (a b c : ℕ) (u : ℝ) :
    constructionSavingCondition a b c u ↔
      savingChi ((a : ℝ) * u) ((b : ℝ) * u) ((c : ℝ) * u) = 1 := by
  unfold constructionSavingCondition savingChi
  split_ifs <;> simp_all

private theorem fract_integer_scale (k : ℕ) (u t : ℝ) :
    Int.fract ((k : ℝ) * Int.fract u + t) = Int.fract ((k : ℝ) * u + t) := by
  have heq : (k : ℝ) * Int.fract u + t =
      ((k : ℝ) * u + t) - (((k : ℤ) * ⌊u⌋ : ℤ) : ℝ) := by
    simp only [Int.fract, Int.cast_mul, Int.cast_natCast]
    ring
  rw [heq, Int.fract_sub_intCast]

theorem constructionSavingCondition_fract (a b c : ℕ) (u : ℝ) :
    constructionSavingCondition a b c (Int.fract u) ↔ constructionSavingCondition a b c u := by
  have hb := fract_integer_scale b u 0
  have hc := fract_integer_scale c u 0
  simp only [add_zero] at hb hc
  simp only [constructionSavingCondition, fract_integer_scale, hb, hc]

theorem fract_mem_constructionSavingSet (a b c : ℕ) (u : ℝ) :
    Int.fract u ∈ constructionSavingSet a b c ↔ constructionSavingCondition a b c u := by
  simp only [constructionSavingSet, Set.mem_ofPred_eq, Int.fract_nonneg, Int.fract_lt_one,
    true_and, constructionSavingCondition_fract]

theorem constructionRemovablePrime_iff_periodic (a b c n p : ℕ) :
    constructionRemovablePrime a b c n p ↔
      Nat.Prime p ∧ 5 < p ∧ Nat.sqrt (constructionDegree a b c * n) < p ∧
        p ≤ constructionDegree a b c * n ∧
        Int.fract ((n : ℝ) / p) ∈ constructionSavingSet a b c := by
  rw [fract_mem_constructionSavingSet]
  unfold constructionRemovablePrime constructionSavingCondition
  have hcast :
      (Int.fract (((a * n : ℕ) : ℚ) / p + 1 / 2) +
        2 * Int.fract (((b * n : ℕ) : ℚ) / p) < Int.fract (((c * n : ℕ) : ℚ) / p)) ↔
      Int.fract ((a : ℝ) * ((n : ℝ) / p) + 1 / 2) +
        2 * Int.fract ((b : ℝ) * ((n : ℝ) / p)) <
          Int.fract ((c : ℝ) * ((n : ℝ) / p)) := by
    rw [← Rat.cast_lt (K := ℝ)]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_fract, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_one, Nat.cast_mul, mul_div_assoc]
  rw [hcast]

theorem constructionSaving_initial_gap {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, 0 < u →
      u ≤ 1 / (constructionDegree a b c : ℝ) + ε →
      ¬ constructionSavingCondition a b c u := by
  have hm := construction_integer_margins hc hp
  let K : ℕ := max (2 * a) (max b c)
  have hKa : 2 * a ≤ K := le_max_left _ _
  have hKb : b ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKc : c ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hKpos : 0 < K := lt_of_lt_of_le hc hKc
  have hKD : K < constructionDegree a b c :=
    max_lt hm.2.2.2.2.1 (max_lt hm.2.2.2.2.2.1 hm.2.2.2.2.2.2)
  have hK : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hD : (0 : ℝ) < constructionDegree a b c := by exact_mod_cast hKpos.trans hKD
  have hKD' : (K : ℝ) < constructionDegree a b c := by exact_mod_cast hKD
  have hfrac : 1 / (constructionDegree a b c : ℝ) < 1 / (K : ℝ) :=
    one_div_lt_one_div_of_lt hK hKD'
  refine ⟨(1 / (K : ℝ) - 1 / (constructionDegree a b c : ℝ)) / 2, by linarith, ?_⟩
  intro u hu hupper
  have huK : u < 1 / (K : ℝ) := by linarith
  have hKu : (K : ℝ) * u < 1 := by
    have := (lt_div_iff₀ hK).mp huK
    nlinarith
  have hKa' : 2 * (a : ℝ) ≤ K := by exact_mod_cast hKa
  have hKb' : (b : ℝ) ≤ K := by exact_mod_cast hKb
  have hKc' : (c : ℝ) ≤ K := by exact_mod_cast hKc
  have hcb : (c : ℝ) < 2 * b := by
    exact_mod_cast (construction_admissible_inequalities hc hp).2.1
  have hzero := savingChi_eq_zero_of_no_wrap
    (mul_nonneg (Nat.cast_nonneg a) hu.le)
    (show (a : ℝ) * u < 1 / 2 by nlinarith)
    (mul_nonneg (Nat.cast_nonneg b) hu.le)
    (show (b : ℝ) * u < 1 by nlinarith)
    (mul_nonneg (Nat.cast_nonneg c) hu.le)
    (show (c : ℝ) * u < 1 by nlinarith)
    (show 0 ≤ (a : ℝ) * u + 2 * ((b : ℝ) * u) - (c : ℝ) * u by
      nlinarith [mul_nonneg (Nat.cast_nonneg a) hu.le])
  intro hsel
  have := (constructionSavingCondition_iff_chi a b c u).mp hsel
  linarith

theorem constructionSavingSet_initial_gap {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    ∃ ε : ℝ, 0 < ε ∧ constructionSavingSet a b c ∩
      Set.Ioc 0 (1 / (constructionDegree a b c : ℝ) + ε) = ∅ := by
  obtain ⟨ε, hε, hgap⟩ := constructionSaving_initial_gap hc hp
  refine ⟨ε, hε, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro u hu
  exact hgap u hu.2.1 hu.2.2 hu.1.2.2

theorem constructionSavingOmega_eq_phi (a b c : ℕ) (hc : 0 < c) :
    savingOmega a b c = (c : ℝ) * savingPhi (constructionParameter a b c) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have h := savingOmega_eq_scaled_phi ((a : ℝ) / c) ((b : ℝ) / c)
    (show (0 : ℝ) < c by exact_mod_cast hc)
  simpa only [mul_div_cancel₀ _ hc', constructionParameter] using h

theorem constructionRemovablePrime_residue_cases {a b c n p : ℕ}
    (hp : constructionRemovablePrime a b c n p) :
    (2 * ((a * n) % p) < p ∧
      (a * n) % p + 2 * ((b * n) % p) + (p + 1) / 2 ≤ (c * n) % p) ∨
      (p + 1 ≤ 2 * ((a * n) % p) ∧
        (a * n) % p + 2 * ((b * n) % p) ≤ (c * n) % p + (p - 1) / 2) := by
  have hcond := hp.2.2.2.2
  rw [fract_div_nat_add_eq_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod] at hcond
  have hodd : p % 2 = 1 := by
    rcases hp.1.eq_two_or_odd with htwo | hodd
    · have := hp.2.1
      omega
    · exact hodd
  exact deletion_residue_cases p _ _ _ hp.1.pos hodd (Nat.mod_lt _ hp.1.pos) hcond

theorem constructionRemovablePrime_obstructionFree {a b c n p : ℕ} [Fact p.Prime]
    (hp : constructionRemovablePrime a b c n p) :
    evenObstructionFree p
      (finiteFieldH p ((a * n) % p) ((b * n) % p) ((c * n) % p)) := by
  have hCp : (c * n) % p ≤ p - 1 := by
    have := Nat.mod_lt (c * n) hp.1.pos
    omega
  rcases constructionRemovablePrime_residue_cases hp with ⟨_, hC⟩ | ⟨hA, hC⟩
  · exact finiteFieldH_evenObstructionFree_low_bound p _ _ _ hp.2.1 hCp hC
  · exact finiteFieldH_evenObstructionFree_high_bound p _ _ _ hp.2.1 hCp hA hC

theorem constructionRemovablePrime_polynomial_primitive {a b c n p : ℕ} [Fact p.Prime]
    (hp : constructionRemovablePrime a b c n p) :
    ∃ V : Polynomial (ZMod p), Polynomial.derivative V =
      Polynomial.X ^ (2 * ((a * n) % p)) *
        (Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 25) ^
          ((b * n) % p) *
        (Polynomial.C 25 - Polynomial.X ^ 2) ^ (p - 1 - (c * n) % p) := by
  refine ⟨evenPolynomialPrimitive p
    (finiteFieldH p ((a * n) % p) ((b * n) % p) ((c * n) % p)), ?_⟩
  rw [evenPolynomialPrimitive_derivative p _ (constructionRemovablePrime_obstructionFree hp),
    evenLift_finiteFieldH]

end PiIrrationality
