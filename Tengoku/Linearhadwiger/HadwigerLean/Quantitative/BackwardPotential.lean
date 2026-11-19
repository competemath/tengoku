import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Backward potential coefficients for matching rounds

The potential weights are defined by elapsed rounds, then read backward
along a fixed finite horizon. This makes the one-round conditional
expectation estimate telescope without constructing a global sample space.
-/

namespace HadwigerLean.Theorem2

/-- Coefficient of the surviving-vertex count after `k` remaining rounds.-/
def potentialCoeff (q c β : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => q * potentialCoeff q c β k + c * (k : ℝ) + β

/--
@isnad1 id=le.3h4v.s5.20450d9de9d9 from=translated src=- shape=ab035b08 vocab=111c6b6d
-/
theorem potentialCoeff_nonneg (q c β : ℝ)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (k : ℕ) : 0 ≤ potentialCoeff q c β k := by
  induction k with
  | zero => norm_num [potentialCoeff]
  | succ k ih =>
      simp only [potentialCoeff]
      positivity
/--
@isnad1 id=le.4h4v.s7.0cdf25c003b2 from=translated src=- shape=4c3e6171 vocab=46ec9c81
-/
theorem potentialCoeff_le (q c β : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (k : ℕ) :
    potentialCoeff q c β k ≤
      q ^ k + c * (k : ℝ) ^ 2 + β * (k : ℝ) := by
  induction k with
  | zero => simp [potentialCoeff]
  | succ k ih =>
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hpoly : 0 ≤ c * (k : ℝ) ^ 2 + β * (k : ℝ) := by positivity
      have hqpoly :
          q * (c * (k : ℝ) ^ 2 + β * (k : ℝ)) ≤
            c * (k : ℝ) ^ 2 + β * (k : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hpoly]
      have hmul := mul_le_mul_of_nonneg_left ih hq0
      have hslack : 0 ≤ c * ((k : ℝ) + 1) := by positivity
      change q * potentialCoeff q c β k + c * (k : ℝ) + β ≤
        q ^ (k + 1) + c * ((k + 1 : ℕ) : ℝ) ^ 2 +
          β * ((k + 1 : ℕ) : ℝ)
      rw [pow_succ]
      push_cast
      nlinarith [hmul, hqpoly, hslack]

/-- Coefficient of the degree-deficit state at round `i` in a horizon `T`.-/
def lossPotentialB (a : ℝ) (T i : ℕ) : ℝ :=
  a * (T - i : ℕ)

/-- Coefficient of the survivor-count state at round `i`.-/
def lossPotentialA (q δ a β : ℝ) (T i : ℕ) : ℝ :=
  potentialCoeff q (δ * a) β (T - i)

/--
@isnad1 id=le.4h6v.s6.89aa84c360b2 from=translated src=- shape=d189369e vocab=a9a9905b
-/
theorem lossPotentialA_nonneg (q δ a β : ℝ)
    (hq : 0 ≤ q) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (T i : ℕ) : 0 ≤ lossPotentialA q δ a β T i := by
  exact potentialCoeff_nonneg q (δ * a) β hq (mul_nonneg hδ ha) hβ _

/--
@isnad1 id=le.1h3v.s4.2ddb94dfbc3c from=translated src=- shape=f4002352 vocab=a141f471
-/
theorem lossPotentialB_nonneg (a : ℝ) (ha : 0 ≤ a) (T i : ℕ) :
    0 ≤ lossPotentialB a T i := by
  unfold lossPotentialB
  positivity
/--
@isnad1 id=eq.0h2v.s4.a4a38f0cd4e8 from=translated src=- shape=8124fa46 vocab=12b64398
-/
theorem lossPotentialB_terminal (a : ℝ) (T : ℕ) :
    lossPotentialB a T T = 0 := by simp [lossPotentialB]

/--
@isnad1 id=eq.0h5v.s4.9c68a5798b3a from=translated src=- shape=9c83b4f6 vocab=d6321e16
-/
theorem lossPotentialA_terminal (q δ a β : ℝ) (T : ℕ) :
    lossPotentialA q δ a β T T = 1 := by
  simp [lossPotentialA, potentialCoeff]

/--
@isnad1 id=eq.1h3v.s5.96729d48dec6 from=translated src=- shape=1a280f9c vocab=eead7e89
-/
theorem lossPotentialB_step (a : ℝ) {T i : ℕ} (hi : i < T) :
    lossPotentialB a T i = lossPotentialB a T (i + 1) + a := by
  have hsub : T - i = T - (i + 1) + 1 := by omega
  simp only [lossPotentialB, hsub, Nat.cast_add, Nat.cast_one]
  ring

/--
@isnad1 id=eq.1h6v.s6.1d7e05e0869b from=translated src=- shape=5e565110 vocab=682b709f
-/
theorem lossPotentialA_step (q δ a β : ℝ) {T i : ℕ} (hi : i < T) :
    lossPotentialA q δ a β T i =
      q * lossPotentialA q δ a β T (i + 1) +
        δ * lossPotentialB a T (i + 1) + β := by
  have hsub : T - i = T - (i + 1) + 1 := by omega
  simp only [lossPotentialA, lossPotentialB, hsub, potentialCoeff]
  ring

/--
@isnad1 id=le.5h5v.s7.a23dcf443e3d from=translated src=- shape=becd00dc vocab=5162b396
-/
theorem lossPotentialA_zero_le (q δ a β : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (T : ℕ) :
    lossPotentialA q δ a β T 0 ≤
      q ^ T + δ * a * (T : ℝ) ^ 2 + β * (T : ℝ) := by
  simpa [lossPotentialA, mul_assoc] using
    potentialCoeff_le q (δ * a) β hq0 hq1 (mul_nonneg hδ ha) hβ T

/--
@isnad1 id=eq.0h2v.s4.45a59b2d1b24 from=translated src=- shape=667c9a64 vocab=76013bf5
-/
theorem lossPotentialB_zero (a : ℝ) (T : ℕ) :
    lossPotentialB a T 0 = a * (T : ℝ) := by
  simp [lossPotentialB]

end HadwigerLean.Theorem2
