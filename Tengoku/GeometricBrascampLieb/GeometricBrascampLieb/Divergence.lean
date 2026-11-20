import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Integration
import Tengoku.Seed.Analysis.Calculus.Deriv.Pi
import Tengoku.Seed.Analysis.InnerProductSpace.Trace
import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cancellation of integrable divergences

The proof reduces each component to the real-line fundamental theorem through
volume-preserving orthonormal coordinates. No divergence theorem is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]

theorem integral_partial_derivative_eq_zero [NormedSpace ℝ E] {n : ℕ}
    (e : E ≃L[ℝ] (Fin (n + 1) → ℝ)) {ν : Measure E}
    (he : MeasurePreserving e ν volume) (i : Fin (n + 1))
    {f : E → ℝ} {df : E → E →L[ℝ] ℝ}
    (hf : Integrable f ν)
    (hg : Integrable (fun x => df x (e.symm (Pi.single i 1))) ν)
    (hd : ∀ x, HasFDerivAt f (df x) x) :
    ∫ x, df x (e.symm (Pi.single i 1)) ∂ν = 0 := by
  let c := e.toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
  have hc : MeasurePreserving c ν (volume.prod volume) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).comp he
  apply integral_derivative_eq_zero_of_coordinates c hc hf hg
  intro y x
  have hi : HasDerivAt (fun s : ℝ => (i.insertNth s y : Fin (n + 1) → ℝ))
      (Pi.single i (1 : ℝ)) x := by
    have heq : Function.update (i.insertNth 0 y : Fin (n + 1) → ℝ) i =
        (fun s : ℝ => i.insertNth s y) :=
      funext fun s => Fin.update_insertNth (α := fun _ : Fin (n + 1) => ℝ) i 0 s y
    rw [← heq]
    exact hasDerivAt_update (i.insertNth 0 y) i x
  have hp := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hi
  exact (hd (c.symm (x, y))).comp_hasDerivAt x hp

section InnerProduct

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- All of the analytic conditions needed to cancel a divergence are explicit:
the vector field and its diagonal directional derivatives are integrable.-/
theorem integral_trace_derivative_eq_zero {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E)
    {V : E → E} {dV : E → E →L[ℝ] E}
    (hV : Integrable V)
    (hdV : ∀ i, Integrable (fun x => inner ℝ (b i) (dV x (b i))))
    (hd : ∀ x, HasFDerivAt V (dV x) x) :
    ∫ x, LinearMap.trace ℝ E (dV x).toLinearMap = 0 := by
  classical
  simp_rw [LinearMap.trace_eq_sum_inner _ b, ContinuousLinearMap.coe_coe]
  rw [integral_finsetSum Finset.univ (fun i _ => hdV i)]
  cases n with
  | zero => simp
  | succ n =>
    apply Finset.sum_eq_zero
    intro i _
    let e : E ≃L[ℝ] (Fin (n + 1) → ℝ) :=
      b.repr.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ _)
    have he : MeasurePreserving e volume volume :=
      (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
    have hb : e.symm (Pi.single i 1) = b i := b.repr_symm_single i
    have hi := integral_partial_derivative_eq_zero e he i
      (f := fun x => inner ℝ (b i) (V x))
      (df := fun x => (innerSL ℝ (b i)).comp (dV x))
    suffices hz : ∫ x, ((innerSL ℝ (b i)).comp (dV x)) (e.symm (Pi.single i 1)) = 0 by
      simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, hb] using hz
    apply hi
    · exact (innerSL ℝ (b i)).integrable_comp hV
    · simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, hb] using hdV i
    · intro x
      exact (innerSL ℝ (b i)).hasFDerivAt.comp x (hd x)

end InnerProduct
end GeometricBrascampLieb
