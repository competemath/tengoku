import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTInterlacing
import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTRootShrinkArithmetic
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Barrier potentials for root shrinking

This file isolates the one-variable barrier argument used in the
Ravichandran--Srivastava root-shrinking theorem.  Roots are counted with
multiplicity throughout.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-- The upper barrier potential of a polynomial, written as its logarithmic derivative.-/
noncomputable def rootBarrierPotential (p : ℝ[X]) (b : ℝ) : ℝ :=
  p.derivative.eval b / p.eval b

/-- The sum-of-squares curvature term attached to the roots of `p`.-/
noncomputable def rootBarrierCurvature (p : ℝ[X]) (b : ℝ) : ℝ :=
  (p.roots.map fun r ↦ (1 / (b - r)) ^ 2).sum

/-- For a split polynomial away from its roots, the logarithmic derivative is the sum of the
reciprocal root gaps.-/
lemma rootBarrierPotential_eq_sum_roots {p : ℝ[X]} (hp : RealRooted p) {b : ℝ}
    (hb : p.eval b ≠ 0) :
    rootBarrierPotential p b = (p.roots.map fun r ↦ 1 / (b - r)).sum := by
  exact hp.eval_derivative_div_eval_of_ne_zero hb

/-! ## The finite-dimensional algebra in one barrier step -/

-- Preserve the existing parameter list for downstream callers.

/-- The reciprocal-gap transform is ordered strongly enough for the weighted rearrangement
inequality.-/
lemma reciprocal_gap_pair_nonneg {A ai aj : ℝ}
    (hA : 0 < A) (hai : 0 < ai) (haj : 0 < aj)
    (haiA : ai < A) (hajA : aj < A) :
    let ti := ai * A / (A - ai)
    let tj := aj * A / (A - aj)
    0 ≤ (ti - tj) * (aj * ti - ai * tj) := by
  dsimp
  have hi : 0 < A - ai := sub_pos.mpr haiA
  have hj : 0 < A - aj := sub_pos.mpr hajA
  have hfirst :
      ai * A / (A - ai) - aj * A / (A - aj) =
        A ^ 2 * (ai - aj) / ((A - ai) * (A - aj)) := by
    field_simp
    ring
  have hsecond :
      aj * (ai * A / (A - ai)) - ai * (aj * A / (A - aj)) =
        ai * aj * A * (ai - aj) / ((A - ai) * (A - aj)) := by
    field_simp
    ring
  rw [hfirst, hsecond]
  rw [div_mul_div_comm]
  apply div_nonneg
  · have :
        A ^ 2 * (ai - aj) * (ai * aj * A * (ai - aj)) =
          ai * aj * A ^ 3 * (ai - aj) ^ 2 := by ring
    rw [this]
    positivity
  · positivity

-- Preserve the existing parameter list for downstream callers.

/-! ## Moving between root multisets and finite sums -/

/-- A list sum can be written as a sum over its position type.-/
lemma list_sum_eq_fin_sum {l : List ℝ} : l.sum = ∑ i : Fin l.length, l.get i := by
  simpa only [List.ofFn_get] using (List.sum_ofFn (f := l.get))

/-- Sorting a multiset exposes its multiplicities as an honest finite index type without changing
any mapped sum.-/
lemma multiset_map_sum_eq_fin_sum_sort (s : Multiset ℝ) (f : ℝ → ℝ) :
    (s.map f).sum = ∑ i : Fin (s.sort (· ≤ ·)).length, f ((s.sort (· ≤ ·)).get i) := by
  let l := s.sort (· ≤ ·)
  have hcoe : (↑l : Multiset ℝ) = s := by simp [l]
  calc
    (s.map f).sum = ((↑l : Multiset ℝ).map f).sum := by rw [hcoe]
    _ = (l.map f).sum := by rfl
    _ = ∑ i : Fin l.length, f (l.get i) := by
      simp [list_sum_eq_fin_sum]

/-! ## A reusable conditional iteration harness -/

/-- The one-step barrier property needed by the iteration.  It is a plain proposition: clients
may prove it from the concrete root geometry available in their application.-/
def DerivativeBarrierStep (p : ℝ[X]) (b φ : ℝ) : Prop :=
  0 < φ ∧
    IsStrictRootUpperBound p b ∧
    IsStrictRootUpperBound p.derivative (b - 1 / φ) ∧
    rootBarrierPotential p.derivative (b - 1 / φ) ≤ φ

/-- Iterating a supplied one-step barrier certificate gives the linear barrier displacement used
in root shrinking.  The conclusion is an upper bound for every root of the iterated derivative.-/
theorem iterate_derivative_rootUpperBound_of_barrier_steps
    {p : ℝ[X]} {b φ : ℝ} (hφ : 0 < φ) (hbase : IsRootUpperBound p b) (d : ℕ)
    (hsteps : ∀ j < d,
      DerivativeBarrierStep (Polynomial.derivative^[j] p) (b - (j : ℝ) / φ) φ) :
    IsRootUpperBound (Polynomial.derivative^[d] p) (b - (d : ℝ) / φ) := by
  by_cases hd : d = 0
  · subst d
    simpa using hbase
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hj := hsteps j (Nat.lt_succ_self j)
    have hderivative :
        Polynomial.derivative^[j + 1] p =
          (Polynomial.derivative^[j] p).derivative := by
      rw [Function.iterate_succ_apply']
    rw [hderivative]
    have hbound : b - ((j + 1 : ℕ) : ℝ) / φ = b - (j : ℝ) / φ - 1 / φ := by
      push_cast
      field_simp [hφ.ne']
      ring
    rw [hbound]
    intro r hr
    exact (hj.2.2.1 r hr).le

end CommutatorTheorem
