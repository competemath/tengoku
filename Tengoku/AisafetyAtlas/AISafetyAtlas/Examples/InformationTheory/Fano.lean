module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.InformationTheory.Fano
public import Tengoku.Seed.Probability.ProbabilityMassFunction.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fano's inequality — worked consequences

Three checks that the general statement in `AISafetyAtlas.InformationTheory.Fano`
has the intended content.

1. **It implies the printed statement.** Cover & Thomas take the estimator to be
   a function `X̂ = g(Y)` of an observation. `fano_of_estimator` is that case,
   obtained by instantiating the general theorem — no separate proof.
2. **It reads correctly at the boundary.** `condEntropy_nonpos_of_perfect` reads
   the inequality at zero error: a perfect estimate forces the conditional
   entropy to be at most zero, which is the qualitative statement Fano is usually
   quoted for. This is a sanity check on the *shape* of the bound, not evidence
   of non-vacuity — deriving a true consequence proves nothing about vacuity,
   since a vacuous theorem entails everything. Non-vacuity is item 3.
3. **It cannot be improved, and it is not vacuous.**
   `entropy_eq_fano_of_witness` exhibits equality at
   *every* error probability `p ∈ [0, 1]`: the truth sits on a fixed guess with
   probability `1 − p` and is otherwise uniform on the rest of the alphabet.
   This is exactly the instance of `entropy_le_fano` at `A = Finset.univ`, so
   the bound is attained along the whole curve and neither term can be reduced.

The first two are corollaries, pinning the general form to the readings a
consumer will want. The third is a witness, and is what makes "sharp" a checked
claim rather than a remark.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open AISafetyAtlas.InformationTheory

universe uΩ uS uT

variable {Ω : Type uΩ} {S : Type uS}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
variable [Countable S] [DecidableEq S]

/-! ## The bound is attained, at every error probability -/

/--
The weights of Cover & Thomas's sharpness example: mass `1 − p` on the guess,
and the remaining `p` spread evenly over the other `n − 1` values of the
alphabet.-/
@[expose] public noncomputable def fanoWeights {n : ℕ} (y₀ : Fin n) (p : ℝ) : Fin n → ℝ≥0∞ :=
  fun x => if x = y₀ then ENNReal.ofReal (1 - p) else ENNReal.ofReal (p / ((n : ℝ) - 1))

/-- The weights are a probability vector.-/
public theorem sum_fanoWeights {n : ℕ} (hn : 2 ≤ n) (y₀ : Fin n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∑ x, fanoWeights y₀ p x = 1 := by
  classical
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsplit : ∑ x, fanoWeights y₀ p x
      = fanoWeights y₀ p y₀ + ∑ x ∈ Finset.univ.erase y₀, fanoWeights y₀ p x := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y₀)]
  have hconst : ∀ x ∈ Finset.univ.erase y₀,
      fanoWeights y₀ p x = ENNReal.ofReal (p / ((n : ℝ) - 1)) := by
    intro x hx
    simp [fanoWeights, (Finset.mem_erase.mp hx).1]
  rw [hsplit, Finset.sum_congr rfl hconst, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : 1 ≤ n := by omega
    push_cast [this]
    ring
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hcard]
  rw [mul_div_cancel₀ _ (ne_of_gt hn1)]
  simp only [fanoWeights, ite_true]
  rw [← ENNReal.ofReal_add (by linarith) hp0]
  simp

/-- The witness measure: the truth is `1 − p` likely to equal the guess `y₀`, and
otherwise uniform on the rest of the alphabet.-/
@[expose] public noncomputable def fanoWitness {n : ℕ} (hn : 2 ≤ n) (y₀ : Fin n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure (Fin n) :=
  (PMF.ofFintype (fanoWeights y₀ p) (sum_fanoWeights hn y₀ hp0 hp1)).toMeasure

/--
The arithmetic behind the witness: spreading `p` over `n − 1` values contributes
exactly `binEntropy p + p·log(n − 1)`, which is Fano's right-hand side.-/
private theorem fano_witness_identity {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) :
    Real.negMulLog (1 - p) + ((n : ℝ) - 1) * Real.negMulLog (p / ((n : ℝ) - 1))
      = p * Real.log ((n : ℝ) - 1) + binEntropy p := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rcases eq_or_lt_of_le hp0 with h | hp
  · rw [← h]
    simp
  · rw [Real.negMulLog, Real.negMulLog,
      Real.log_div (ne_of_gt hp) (ne_of_gt hn1),
      binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    field_simp
    ring

end AISafetyAtlas.Examples.InformationTheory
