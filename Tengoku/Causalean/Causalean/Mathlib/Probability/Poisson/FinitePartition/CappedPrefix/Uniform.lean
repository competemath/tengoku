module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# Uniform permutation and Boolean mark laws

An iid sample remains iid after a coordinate permutation. Independent fair
Boolean marks pair with that sample to give the paired iid product law. The
finite mark and permutation normalizations are explicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- [The fair Boolean law](goal) assigns probability one half to each Boolean value. -/
noncomputable def fairBoolLaw : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac false + Measure.dirac true)

/-- For [an iid probability law](hyp:μ), [a sample size](hyp:n), and [a coordinate permutation](hyp:perm),
[reordering its finite iid product leaves the law unchanged](goal). -/
theorem map_perm_pi {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (perm : Equiv.Perm (Fin n)) :
    Measure.map (fun x : Fin n → X => fun i => x (perm i))
      (Measure.pi (fun _ : Fin n => μ)) =
      Measure.pi (fun _ : Fin n => μ) := by
  /- Use `measurePreserving_piCongrLeft` for the index equivalence `perm`. -/
  have hf : (fun x : Fin n → X => fun i => x (perm i)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) perm.symm :
        (Fin n → X) → (Fin n → X)) := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  simpa using Measure.pi_map_piCongrLeft perm.symm (fun _ : Fin n => μ)

/-- For [a sample size](hyp:n), [the finite permutation and mark averaging weights sum to one](goal),
including when the sample size is zero. -/
theorem perm_mark_weight_sum (n : ℕ) :
    (∑ _perm : Equiv.Perm (Fin n),
      ∑ _marks : Fin n → Bool,
        (1 : ℝ) / ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (Fintype.card (Fin n → Bool) : ℝ))) = 1 := by
  /- Both finite types are nonempty; reduce the two constant sums to cardinalities. -/
  have hp : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hm : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  simp [div_eq_mul_inv, hp, ← mul_assoc]

end Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
