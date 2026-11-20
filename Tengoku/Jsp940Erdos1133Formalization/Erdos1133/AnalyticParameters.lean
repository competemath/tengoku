import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
namespace Erdos1133

def interiorRatio (δ : ℝ) : ℝ := 1 / (1 + δ/4)
def plateauRate (δ : ℝ) : ℝ := Real.pi * δ / 24
def compressedType (δ : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (((2*n : ℕ) : ℝ) + 1) / (2*interiorRatio δ*n)

/--
@isnad1 id=lt.1h1v.s4.59ec816ae173 from=translated src=- shape=35bd48ee vocab=240d0df8
-/
theorem interiorRatio_pos {δ : ℝ} (hδ : 0 < δ) : 0 < interiorRatio δ := by
  unfold interiorRatio
  positivity

/--
@isnad1 id=lt.1h1v.s4.7c5f8d09fef2 from=translated src=- shape=3965f485 vocab=240d0df8
-/
theorem interiorRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : interiorRatio δ < 1 := by
  unfold interiorRatio
  apply (div_lt_one (by positivity)).mpr
  linarith

/--
@isnad1 id=lt.1h1v.s4.bba59681c9ba from=translated src=- shape=35bd48ee vocab=20083522
-/
theorem plateauRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < plateauRate δ := by
  unfold plateauRate
  positivity

/--
@isnad1 id=and.2h2v.s7.474f4a7263a5 from=translated src=- shape=a13dc126 vocab=f9c3be6d
-/
theorem compressedType_bounds {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hn : (4+δ)/δ ≤ (n : ℝ)) :
    Real.pi ≤ compressedType δ n ∧
      compressedType δ n + 6*plateauRate δ ≤ Real.pi*(1+3*δ/4) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hscale : (4+δ) ≤ (n : ℝ)*δ := (div_le_iff₀ hδ).mp hn
  have hβ := interiorRatio_pos hδ
  have heq : compressedType δ n = Real.pi*((1+δ/4)*(1+1/(2*(n : ℝ)))) := by
    unfold compressedType interiorRatio
    push_cast
    field_simp
  rw [heq]
  constructor
  · have hone : 1 ≤ (1+δ/4)*(1+1/(2*(n : ℝ))) := by
      nlinarith [one_div_pos.mpr (show (0 : ℝ) < 2*n by positivity)]
    nlinarith [Real.pi_pos]
  · have hsmall : (1+δ/4)/(2*(n : ℝ)) ≤ δ/4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*n)).mpr
      nlinarith
    have hs : (1+δ/4)*(1+1/(2*(n : ℝ))) ≤ 1+δ/2 := by
      calc
        _ = 1+δ/4 + (1+δ/4)/(2*(n : ℝ)) := by ring
        _ ≤ _ := by linarith
    unfold plateauRate
    nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]

/--
@isnad1 id=other.2h2v.s7.4ca4c73adca4 from=translated src=- shape=c2b37b10 vocab=7906f539
-/
theorem compressed_bandwidth_budget {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hn : (4+δ)/δ ≤ (n : ℝ)) :
    let m := Nat.ceil ((compressedType δ n + 6*plateauRate δ)*(2*(n : ℝ))/(2*Real.pi))
    n ≤ m ∧ (m : ℝ) ≤ n + δ*n := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hnδ : 4+δ ≤ (n : ℝ)*δ := (div_le_iff₀ hδ).mp hn
  obtain ⟨hlo,hhi⟩ := compressedType_bounds hδ hn
  have hα := plateauRate_pos hδ
  let b : ℝ := (compressedType δ n+6*plateauRate δ)*(2*(n : ℝ))/(2*Real.pi)
  have hb : (n : ℝ) ≤ b := by
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlo (show (0 : ℝ) ≤ 2*n by positivity),
      mul_nonneg hα.le hn0.le]
  have hbu : b ≤ (1+3*δ/4)*(n : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhi (show (0 : ℝ) ≤ 2*n by positivity)]
  dsimp only
  constructor
  · exact Nat.cast_le.mp (hb.trans (Nat.le_ceil b))
  · have hc : (Nat.ceil b : ℝ) < b+1 := Nat.ceil_lt_add_one (hn0.le.trans hb)
    change (Nat.ceil b : ℝ) ≤ _
    nlinarith

/-- A deliberately loose asymptotic estimate suffices for all window errors.
Its threshold is explicit and no convergence theorem is assumed.
@isnad1 id=ex.3h3v.s6.b2da05ab5f72 from=translated src=- shape=077eac9b vocab=bbfbc6af
-/
theorem linear_over_sixth_eventually_small {A d ε : ℝ}
    (hA : 0 ≤ A) (hd : 0 < d) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n ∧ A*n/(d*n)^6 ≤ ε := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max 1 (A/(d^6*ε)))
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans (hn₀.le.trans hnn)
  have hn0 : (0 : ℝ) < n := by linarith
  have hthreshold : A/(d^6*ε) ≤ n := (le_max_right _ _).trans (hn₀.le.trans hnn)
  have hA' : A ≤ (n : ℝ)*(d^6*ε) :=
    (div_le_iff₀ (by positivity : 0 < d^6*ε)).mp hthreshold
  refine ⟨by exact_mod_cast hn0, ?_⟩
  have hpow : (n : ℝ) ≤ (n : ℝ)^5 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ (5 : ℕ) by omega)
  have heq : A*(n : ℝ)/(d*n)^6 = (A/d^6)/(n : ℝ)^5 := by
    field_simp
  rw [heq]
  calc
    (A/d^6)/(n : ℝ)^5 ≤ (A/d^6)/(n : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn0 hpow
    _ ≤ ε := by
      apply (div_le_iff₀ hn0).mpr
      apply (div_le_iff₀ (by positivity : 0 < d^6)).mpr
      nlinarith

end Erdos1133
