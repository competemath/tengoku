import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSStability
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.Slope
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Analysis.Complex.RealDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic ingredients of the MSS multivariate barrier argument

The upper-half-plane signs below are derived from stability. In particular, they
are not supplied as barrier monotonicity assumptions. The final quantitative
shift theorem will use the mixed derivative signs proved in this file.
-/

namespace NoEpsilon.MSSBarrier

open NoEpsilon.MSSStability Polynomial Filter
open scoped BigOperators Topology

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def coordinateShift {R : Type*} [Add R] [Zero R]
    (z : σ → R) (j : σ) (t : R) : σ → R :=
  fun i ↦ z i + if i = j then t else 0

omit [Fintype σ] in
/--
@isnad1 id=eq.0h4v.s5.35145f692bf0 from=translated src=- shape=a85433f5 vocab=618aa4d8
-/
@[simp] theorem coordinateShift_zero {R : Type*} [AddZeroClass R]
    (z : σ → R) (j : σ) : coordinateShift z j 0 = z := by
  funext i
  simp [coordinateShift]

-- Preserve the existing parameter list for downstream callers.

/-- Real stability is the semantic stability of the polynomial after the real
coefficient inclusion.-/
def RealStable (p : MvPolynomial σ ℝ) : Prop :=
  UpperStable (p.map Complex.ofRealHom)

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h3v.s6.a1757f40ca97 from=translated src=- shape=224f68aa vocab=225ce1ad
-/
@[simp] theorem eval₂_ofReal (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun i ↦ (z i : ℂ)) p =
      (MvPolynomial.eval z p : ℂ) :=
  (MvPolynomial.eval₂_comp Complex.ofRealHom z p).symm

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h3v.s8.885497bbc5c2 from=translated src=- shape=e8652f87 vocab=106febd6
-/
@[simp] theorem eval_complexification (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval (fun i ↦ (z i : ℂ)) (p.map Complex.ofRealHom) =
      (MvPolynomial.eval z p : ℂ) := by
  rw [MvPolynomial.eval_map, eval₂_ofReal]

noncomputable def barrier (p : MvPolynomial σ ℝ) (i : σ) (z : σ → ℝ) : ℝ :=
  MvPolynomial.eval z (MvPolynomial.pderiv i p) / MvPolynomial.eval z p

noncomputable def mixedBarrierDerivative (p : MvPolynomial σ ℝ)
    (i j : σ) (z : σ → ℝ) : ℝ :=
  (MvPolynomial.eval z (MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) *
      MvPolynomial.eval z p - MvPolynomial.eval z (MvPolynomial.pderiv i p) *
      MvPolynomial.eval z (MvPolynomial.pderiv j p)) / (MvPolynomial.eval z p)^2

-- Preserve the existing parameter list for downstream callers.

omit [Fintype σ] in
/--
@isnad1 id=eq.0h6v.s6.58d69269c812 from=translated src=- shape=c845efc2 vocab=31822771
-/
@[simp] theorem coordinateShift_twice {R : Type*} [AddMonoid R]
    (z : σ → R) (j : σ) (a b : R) :
    coordinateShift (coordinateShift z j a) j b = coordinateShift z j (a + b) := by
  funext i
  by_cases hi : i = j <;> simp [coordinateShift, hi, add_assoc]

-- Preserve the existing parameter list for downstream callers.

/-- Positivity throughout the upper orthant, the MSS definition of being above
all roots. Using a pointwise order makes its upward closure explicit.-/
def AboveRoots (p : MvPolynomial σ ℝ) (z : σ → ℝ) : Prop :=
  ∀ y, z ≤ y → 0 < MvPolynomial.eval y p

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=lt.1h3v.s6.e317b9ad6343 from=translated src=- shape=bd473b11 vocab=2a7ce7f3
-/
theorem AboveRoots.eval_pos {p : MvPolynomial σ ℝ} {z : σ → ℝ}
    (hz : AboveRoots p z) : 0 < MvPolynomial.eval z p := hz z le_rfl

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=aboveroo.2h4v.s5.287900b0a361 from=translated src=- shape=808fdccc vocab=34c1d3b6
-/
theorem AboveRoots.mono {p : MvPolynomial σ ℝ} {z y : σ → ℝ}
    (hz : AboveRoots p z) (hy : z ≤ y) : AboveRoots p y :=
  fun w hw ↦ hz w (hy.trans hw)

omit [Fintype σ] in
/--
@isnad1 id=le.1h4v.s5.4f0bc25bc2f4 from=translated src=- shape=742dea8a vocab=1a976143
-/
theorem le_coordinateShift (z : σ → ℝ) (j : σ) {t : ℝ} (ht : 0 ≤ t) :
    z ≤ coordinateShift z j t := by
  intro k
  by_cases hk : k = j <;> simp [coordinateShift, hk, ht]

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.MSSBarrier
