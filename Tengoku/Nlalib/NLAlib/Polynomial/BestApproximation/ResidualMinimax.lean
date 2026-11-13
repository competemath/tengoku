import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Normed.Approximation
import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.Minimax
import Tengoku.Seed.Topology.ContinuousMap.Polynomial
import Tengoku.Seed.Topology.ContinuousMap.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residual-polynomial minimax on arbitrary complex sets

The supremum and infimum are extended nonnegative reals, so unbounded and empty
sets need no special side conditions. Compact attainment takes place in the
finite-dimensional image of coefficient evaluation, automatically removing
coefficients invisible on the set. Source: operator derivations, Section 7.
Atlas: `residual-polynomial`.
-/

noncomputable section
open Polynomial
open scoped ENNReal
namespace NLAlib

/-- The extended uniform modulus of a real polynomial on a complex set.
The empty supremum is zero. Source: operator derivations, Section 7.
atlas: residual-polynomial (partial)-/
def polynomialSupNorm (s : Set ℂ) (p : ℝ[X]) : ℝ≥0∞ :=
  ⨆ z ∈ s, ‖aeval z p‖ₑ

/-- Residual minimax error for degree at most `k` and constant coefficient one.
Its value lies between zero and one even on unbounded sets, and is zero on the
empty set. Source: operator derivations, Section 7.
atlas: residual-polynomial (partial)-/
def residualMinimaxError (s : Set ℂ) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (p : ℝ[X]) (_ : p.degree ≤ k) (_ : p.eval 0 = 1), polynomialSupNorm s p

/-- Enlarging the complex domain increases every polynomial's extended uniform modulus.
Source: operator derivations, Section 7.
@isnad1 id=le.1h3v.s4.260786ea2f4f from=translated src=- shape=b279e3bf vocab=0eac6769
-/
theorem polynomialSupNorm_mono {s t : Set ℂ} (hst : s ⊆ t) (p : ℝ[X]) :
    polynomialSupNorm s p ≤ polynomialSupNorm t p := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  exact le_iSup_of_le z (le_iSup_of_le (hst hz) le_rfl)

/-- Every admissible residual polynomial bounds the minimax error.
Source: operator derivations, Section 7.
@isnad1 id=le.2h3v.s5.8be59032e016 from=translated src=- shape=2b3c42ad vocab=690c6e4a
-/
theorem residualMinimaxError_le {s : Set ℂ} {k : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ k) (hp0 : p.eval 0 = 1) :
    residualMinimaxError s k ≤ polynomialSupNorm s p :=
  iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le hp0 le_rfl))

/-- Allowing a larger degree can only decrease residual minimax error.
Source: operator derivations, Section 7.
atlas: residual-polynomial (partial)
@isnad1 id=antitone.0h1v.s3.522c2d3c3ff4 from=translated src=- shape=ed1bc477 vocab=b031c2d6
-/
theorem residualMinimaxError_antitone (s : Set ℂ) :
    Antitone (residualMinimaxError s) := by
  intro k l hkl
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  apply le_iInf
  intro hp0
  exact residualMinimaxError_le (hp.trans (by exact_mod_cast hkl)) hp0

/-- Enlarging the domain increases residual minimax error, without boundedness assumptions.
Source: operator derivations, Section 7.
atlas: residual-polynomial (partial)
@isnad1 id=le.1h3v.s4.ffc4e04e7a8a from=translated src=- shape=23617870 vocab=afb45bf7
-/
theorem residualMinimaxError_mono {s t : Set ℂ} (hst : s ⊆ t) (k : ℕ) :
    residualMinimaxError s k ≤ residualMinimaxError t k := by
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  apply le_iInf
  intro hp0
  exact (residualMinimaxError_le hp hp0).trans (polynomialSupNorm_mono hst p)

/-- The constant residual polynomial one gives the universal upper bound one.
Source: operator derivations, Section 7.
atlas: residual-polynomial (partial)
@isnad1 id=le.0h2v.s4.595b2bd036fa from=translated src=- shape=1a68ef72 vocab=afb45bf7
-/
theorem residualMinimaxError_le_one (s : Set ℂ) (k : ℕ) :
    residualMinimaxError s k ≤ 1 := by
  apply (residualMinimaxError_le (p := (1 : ℝ[X])) (by simp) (by simp)).trans
  apply iSup_le
  intro z
  apply iSup_le
  intro _
  simp

/-- The empty-domain residual minimax problem has value zero.
Source: operator derivations, Section 7.
atlas: residual-polynomial (partial)
@isnad1 id=eq.0h1v.s4.b7ae5f02bc57 from=translated src=- shape=1368939f vocab=ed4cb3d1
-/
@[simp] theorem residualMinimaxError_empty (k : ℕ) :
    residualMinimaxError ∅ k = 0 := by
  apply le_antisymm _ bot_le
  simpa [polynomialSupNorm] using
    residualMinimaxError_le (s := ∅) (p := (1 : ℝ[X])) (by simp) (by simp)

/-- Restriction of a real polynomial to a complex domain as a continuous map.
Source: evaluation of the complexification of its coefficient polynomial.-/
def complexPolynomialRestriction (s : Set ℂ) : ℝ[X] →ₗ[ℝ] C(s, ℂ) where
  toFun p := (p.map (algebraMap ℝ ℂ)).toContinuousMapOn s
  map_add' p q := by ext z; simp
  map_smul' a p := by ext z; simp [Polynomial.smul_eq_C_mul]

/-- Restriction is the usual real-coefficient algebra evaluation at a complex point.
@isnad1 id=eq.0h3v.s9.6347e6864f50 from=translated src=- shape=ad6386f2 vocab=9dc5d2a9
-/
@[simp] theorem complexPolynomialRestriction_apply (s : Set ℂ) (p : ℝ[X]) (z : s) :
    complexPolynomialRestriction s p z = aeval (z : ℂ) p := by
  simp [complexPolynomialRestriction, eval_map, aeval_def]

/-- Degree-bounded polynomials with zero constant coefficient form the direction
space of the affine residual-polynomial constraint.-/
def residualPolynomialDirections (k : ℕ) : Submodule ℝ ℝ[X] :=
  degreeLE ℝ k ⊓ LinearMap.ker (aeval (0 : ℝ)).toLinearMap

/-- The direction space has exactly the degree and zero-evaluation conditions.
@isnad1 id=iff.0h2v.s6.21f0c3b4965e from=translated src=- shape=8536962a vocab=31ad4b53
-/
theorem mem_residualPolynomialDirections_iff (k : ℕ) (p : ℝ[X]) :
    p ∈ residualPolynomialDirections k ↔ p.degree ≤ k ∧ p.eval 0 = 0 := by
  simp [residualPolynomialDirections, mem_degreeLE, aeval_def, coeff_zero_eq_eval_zero]

/-- The restricted direction space quotients out coefficients invisible on the domain.-/
def residualEvaluationDirections (s : Set ℂ) (k : ℕ) : Submodule ℝ C(s, ℂ) :=
  (residualPolynomialDirections k).map (complexPolynomialRestriction s)

/-- Restricted residual directions are finite dimensional even when evaluation is
not injective, for example when the set has fewer than `k` points.
@isnad1 id=finitedi.0h2v.s10.5c3f352f334c from=translated src=- shape=9e0ae0f4 vocab=f3cd071c
-/
instance residualEvaluationDirections_finiteDimensional (s : Set ℂ) (k : ℕ) :
    FiniteDimensional ℝ (residualEvaluationDirections s k) := by
  have : FiniteDimensional ℝ (degreeLT ℝ (k + 1)) :=
    FiniteDimensional.of_injective (degreeLTEquiv ℝ (k + 1)).toLinearMap
      (degreeLTEquiv ℝ (k + 1)).injective
  have : FiniteDimensional ℝ (degreeLE ℝ (k : WithBot ℕ)) := by
    rw [← degreeLT_succ_eq_degreeLE]
    infer_instance
  unfold residualEvaluationDirections residualPolynomialDirections
  infer_instance

/-- The extended polynomial supremum is the continuous-map uniform norm on a compact set.
@isnad1 id=eq.0h2v.s9.dedc0a961ab6 from=translated src=- shape=1df511c3 vocab=5fb8890b
-/
theorem polynomialSupNorm_eq_enorm {s : Set ℂ} [CompactSpace s] (p : ℝ[X]) :
    polynomialSupNorm s p = ‖complexPolynomialRestriction s p‖ₑ := by
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  simp only [polynomialSupNorm, complexPolynomialRestriction_apply]
  exact (iSup_subtype'' s (fun z => ‖aeval z p‖ₑ)).symm

/-- A real residual polynomial attains the minimax error on every compact complex
set, including finite and empty sets. Invisible coefficient directions are removed
by taking the evaluation image, rather than assuming bounded coefficient sublevels.
Source: operator derivations, (S6)–(S8).
atlas: residual-polynomial (partial)
@isnad1 id=ex.0h2v.s6.dd4d951c68bf from=translated src=- shape=7324e56e vocab=c375f9b0
-/
theorem exists_polynomialSupNorm_eq_residualMinimaxError {s : Set ℂ} [CompactSpace s]
    (k : ℕ) : ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval 0 = 1 ∧
      polynomialSupNorm s p = residualMinimaxError s k := by
  obtain ⟨g, hg, hbest⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional
    (residualEvaluationDirections s k) (1 : C(s, ℂ))
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hg
  obtain ⟨hqdeg, hq0⟩ := (mem_residualPolynomialDirections_iff k q).mp hq
  have hpdeg : (1 - q).degree ≤ k := (degree_sub_le _ _).trans
    (max_le (by simp) hqdeg)
  have hp0 : (1 - q).eval 0 = 1 := by simp [hq0]
  refine ⟨1 - q, hpdeg, hp0, le_antisymm ?_ (residualMinimaxError_le hpdeg hp0)⟩
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  apply le_iInf
  intro hp0'
  rw [polynomialSupNorm_eq_enorm, polynomialSupNorm_eq_enorm]
  have hd : 1 - p ∈ residualPolynomialDirections k := by
    apply (mem_residualPolynomialDirections_iff _ _).mpr
    exact ⟨(degree_sub_le _ _).trans (max_le (by simp) hp), by simp [hp0']⟩
  have hle := Metric.infDist_le_dist_of_mem (x := (1 : C(s, ℂ)))
    (Submodule.mem_map.mpr ⟨1 - p, hd, rfl⟩ :
      complexPolynomialRestriction s (1 - p) ∈ residualEvaluationDirections s k)
  change Metric.infDist (1 : C(s, ℂ)) (residualEvaluationDirections s k) ≤
    dist 1 (complexPolynomialRestriction s (1 - p)) at hle
  rw [← hbest, dist_eq_norm] at hle
  have heq : complexPolynomialRestriction s (1 - q) =
      1 - complexPolynomialRestriction s q := by ext z; simp
  have heq' : (1 : C(s, ℂ)) - complexPolynomialRestriction s (1 - p) =
      complexPolynomialRestriction s p := by ext z; simp
  rw [heq'] at hle
  rw [heq]
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hle

/-- On a positive real interval, embedded in the complex plane, residual minimax
error is the sharp reciprocal Chebyshev value, including degree zero.
Source: operator derivations, (S9); Trefethen–Bau, Theorem 38.5.
atlas: residual-polynomial (partial)
@isnad1 id=eq.2h3v.s7.2d1d2ebc2623 from=translated src=- shape=4e79fe01 vocab=9aa47628
-/
theorem residualMinimaxError_real_interval {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (k : ℕ) :
    residualMinimaxError ((algebraMap ℝ ℂ) '' Set.Icc a b) k =
      ENNReal.ofReal (1 / (Chebyshev.T ℝ k).eval ((b + a) / (b - a))) := by
  let s : Set ℂ := (algebraMap ℝ ℂ) '' Set.Icc a b
  have hs : IsCompact s := isCompact_Icc.image Complex.continuous_ofReal
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have heval (p : ℝ[X]) (x : ℝ) :
      ‖aeval (algebraMap ℝ ℂ x) p‖ = |p.eval x| := by
    rw [aeval_algebraMap_apply_eq_algebraMap_eval]
    change ‖Complex.ofReal (p.eval x)‖ = |p.eval x|
    simp only [Complex.norm_real, Real.norm_eq_abs]
  apply le_antisymm
  · have hcheb := (isLeast_chebyshev_minimax k ha hab).1
    obtain ⟨p, hp, hp0, hbound⟩ := hcheb
    apply (residualMinimaxError_le hp hp0).trans
    apply iSup_le
    intro z
    apply iSup_le
    rintro ⟨x, hx, rfl⟩
    rw [← ofReal_norm, heval]
    exact ENNReal.ofReal_le_ofReal (hbound x hx)
  · apply le_iInf
    intro p
    apply le_iInf
    intro hp
    apply le_iInf
    intro hp0
    have hfinite : polynomialSupNorm s p ≠ ∞ := by
      rw [polynomialSupNorm_eq_enorm]
      exact enorm_ne_top
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
    apply (isLeast_chebyshev_minimax k ha hab).2
    refine ⟨p, hp, hp0, ?_⟩
    intro x hx
    have hpoint : ‖aeval (algebraMap ℝ ℂ x) p‖ₑ ≤ polynomialSupNorm s p :=
      le_iSup_of_le (algebraMap ℝ ℂ x) (le_iSup_of_le ⟨x, hx, rfl⟩ le_rfl)
    have hreal := ENNReal.toReal_mono hfinite hpoint
    simpa only [toReal_enorm, heval] using hreal

end NLAlib
