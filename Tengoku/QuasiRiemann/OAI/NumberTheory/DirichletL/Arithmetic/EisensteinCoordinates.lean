import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Tengoku.Seed.Topology.Maps.Proper.Basic
import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Integral.Gamma
import Tengoku.Seed.Analysis.Distribution.AEEqOfIntegralContDiff
import Tengoku.Seed.Analysis.Fourier.AddCircleMulti
import Tengoku.Seed.LinearAlgebra.Matrix.FixedDetMatrices
import Tengoku.Seed.Topology.ContinuousMap.Bounded.Normed
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.Seed.Analysis.Normed.Module.MultipliableUniformlyOn
import Tengoku.Seed.Analysis.Meromorphic.Basic
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousLinearMap
import Tengoku.Seed.Analysis.CStarAlgebra.Spectrum
import Tengoku.Seed.Analysis.Normed.Operator.Compact.FiniteDimension
import Tengoku.Seed.Analysis.Normed.Module.RCLike.Basic
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.Basic
import Tengoku.Seed.Analysis.Normed.Operator.Fredholm.Basic
import Tengoku.Seed.Topology.Compactness.Lindelof
import Tengoku.Seed.Analysis.InnerProductSpace.LinearPMap
import Tengoku.Seed.Analysis.Normed.Operator.Extend
import Tengoku.Seed.Analysis.Calculus.ContDiff.Defs
import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Analysis.Convolution
import Tengoku.Seed.Analysis.Normed.Operator.Compact.Basic
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Basic
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Complete
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Indicator
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Tengoku.Seed.MeasureTheory.Measure.Haar.OfBasis
import Tengoku.Seed.MeasureTheory.Measure.Haar.Unique
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.MeasureTheory.Measure.Real
import Tengoku.Seed.Probability.Moments.Variance
import Tengoku.Seed.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Tengoku.Seed.Geometry.Manifold.ContMDiff.Atlas
import Tengoku.Seed.Analysis.InnerProductSpace.Dual
import Tengoku.Seed.MeasureTheory.SpecificCodomains.Pi
import Tengoku.Seed.Geometry.Manifold.ContMDiff.Basic
import Tengoku.Seed.Geometry.Manifold.SmoothApprox
import Tengoku.Seed.Analysis.Distribution.TemperedDistribution
import Tengoku.Seed.Topology.Algebra.Module.LinearPMap
import Tengoku.Seed.Analysis.InnerProductSpace.ProdL2
import Tengoku.Seed.Topology.Order.ProjIcc
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential
import Tengoku.Seed.Topology.Covering.Quotient
import Tengoku.Seed.MeasureTheory.Function.ContinuousMapDense
import Tengoku.Seed.MeasureTheory.Function.Jacobian
import Tengoku.Seed.Geometry.Euclidean.Inversion.Calculus
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Tengoku.Seed.Order.PiLex
import Tengoku.Seed.MeasureTheory.Group.FundamentalDomain
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper
import Tengoku.Seed.MeasureTheory.Function.L2Space
import Tengoku.Seed.MeasureTheory.Measure.WithDensity
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.Analysis.Normed.Lp.SmoothApprox
import Tengoku.Seed.RingTheory.Multiplicity
import Tengoku.Seed.Topology.MetricSpace.HausdorffDistance
import Tengoku.Seed.GroupTheory.Index
import Tengoku.Seed.Topology.Instances.Matrix
import Tengoku.Seed.Analysis.SpecialFunctions.SmoothTransition
import Tengoku.Seed.Analysis.Calculus.ContDiff.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Tengoku.Seed.Analysis.Calculus.FDeriv.Measurable
import Tengoku.Seed.Analysis.Calculus.Deriv.Star
import Tengoku.Seed.MeasureTheory.Function.LocallyIntegrable
import Tengoku.Seed.Analysis.Calculus.Deriv.Shift
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence
import Tengoku.Seed.Analysis.Calculus.SmoothSeries
import Tengoku.Seed.RingTheory.Ideal.Quotient.Nilpotent
import Tengoku.Seed.NumberTheory.NumberField.DedekindZeta
import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.Multiplicity
import Tengoku.Seed.Data.Finsupp.Multiset
import Tengoku.Seed.Tactic.Tauto
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Sigma
import Tengoku.Seed.Data.Finset.Powerset
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.Algebra.Module.ZLattice.Summable
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
import Tengoku.Seed.LinearAlgebra.UnitaryGroup
import Tengoku.Seed.GroupTheory.GroupAction.Quotient
import Tengoku.Seed.MeasureTheory.Constructions.HaarToSphere
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Integral
import Tengoku.Seed.Analysis.Fourier.PoissonSummation
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Powerset
import Tengoku.Seed.Data.Multiset.Interval
import Tengoku.Seed.Analysis.SumIntegralComparisons
import Tengoku.Seed.Analysis.Fourier.Inversion
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Complex
import Tengoku.Seed.Tactic.FunProp
import Tengoku.Seed.Analysis.Real.Pi.Bounds
import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar
import Tengoku.Seed.Analysis.Calculus.BumpFunction.FiniteDimension
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal
import Tengoku
import Tengoku.Seed.Order.Filter.AtTopBot.Field
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Finset.Image
import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Complex.Convex
import Tengoku.Seed.Analysis.Complex.HalfPlane
import Tengoku.Seed.NumberTheory.ArithmeticFunction.Moebius
import Tengoku.Seed.NumberTheory.LSeries.DirichletContinuation
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing
import Tengoku.Seed.NumberTheory.LSeries.Convolution
import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.Moebius
import Tengoku.Seed.NumberTheory.GaussSum
import Tengoku.Seed.NumberTheory.JacobiSum.Basic
import Tengoku.Seed.Algebra.GroupWithZero.Units.Fintype
import Tengoku.Seed.Tactic.Group
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Piecewise
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.MellinInversion
import Tengoku.Seed.Analysis.Fourier.RiemannLebesgueLemma
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.PID
import Tengoku.Seed.NumberTheory.LSeries.Dirichlet
import Tengoku.Seed.NumberTheory.DirichletCharacter.Orthogonality
import Tengoku.Seed.NumberTheory.DirichletCharacter.Bounds
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Fourier
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.RingTheory.Coprime.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.Analysis.Calculus.ContDiff.Bounds
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.Seed.Algebra.Group.AddChar
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.LinearAlgebra.Matrix.SpecialLinearGroup
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Geometry.Manifold.PartitionOfUnity
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Three
import Tengoku.Seed.Algebra.Group.Pi.Units
import Tengoku.Seed.RingTheory.Ideal.IsPrincipal
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.NumberTheory.Cyclotomic.PrimitiveRoots
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.NumberTheory.Cyclotomic.Gal
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.CircleAddChar
import Tengoku.Seed.NumberTheory.NumberField.Norm
import Tengoku.Seed.NumberTheory.NumberField.Ideal.Asymptotics
import Tengoku.Seed.Data.Int.Order.Lemmas
import Tengoku.Seed.NumberTheory.LegendreSymbol.Complex
import Tengoku.Seed.RingTheory.PowerBasis
import Tengoku.Seed.RingTheory.Ideal.Norm.AbsNorm
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.NumberTheory.Chebyshev
import Tengoku.Seed.Analysis.Normed.Group.Tannery
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Bounds
import Tengoku.Seed.Analysis.SpecialFunctions.Exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

open scoped BigOperators

namespace ShortDraft

/--
@isnad1 id=isprinci.0h0v.s6.1aca30fcd36d from=translated src=- shape=841f1c06 vocab=9aa81f15
-/
theorem eisenstein_ring_pid :
    IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)

abbrev EisensteinCoordinates := ℤ × ℤ

def eisensteinMul (x y : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def eisensteinConj (x : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 - x.2, -x.2)

def eisensteinNorm (x : EisensteinCoordinates) : ℤ :=
  x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

/--
@isnad1 id=eq.0h2v.s4.d8da30e2f5e4 from=translated src=- shape=88b36870 vocab=648540be
-/
theorem eisenstein_norm_mul (x y : EisensteinCoordinates) :
    eisensteinNorm (eisensteinMul x y) = eisensteinNorm x * eisensteinNorm y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  dsimp [eisensteinNorm, eisensteinMul]
  ring

/--
@isnad1 id=eq.0h1v.s3.4daced1d94c9 from=translated src=- shape=8d4cac31 vocab=64cb4020
-/
theorem eisenstein_norm_conj (x : EisensteinCoordinates) :
    eisensteinNorm (eisensteinConj x) = eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm, eisensteinConj]
  ring

/--
@isnad1 id=eq.0h1v.s4.b6238c7b11a7 from=translated src=- shape=bc04d26c vocab=32c77fb9
-/
theorem eisenstein_mul_conj (x : EisensteinCoordinates) :
    eisensteinMul x (eisensteinConj x) = (eisensteinNorm x, 0) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> dsimp [eisensteinNorm, eisensteinConj, eisensteinMul] <;> ring

/--
@isnad1 id=le.0h1v.s3.ef7f6989db3b from=translated src=- shape=b9369acb vocab=a53ce562
-/
theorem eisenstein_norm_nonneg (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

/--
@isnad1 id=iff.0h1v.s4.90137f70ad32 from=translated src=- shape=ee7ffebc vocab=ffb06622
-/
theorem eisenstein_norm_eq_zero_iff (x : EisensteinCoordinates) :
    eisensteinNorm x = 0 ↔ x = (0, 0) := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  constructor
  · intro h
    have hb : b = 0 := by
      nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
    have ha : a = 0 := by
      subst b
      nlinarith [sq_nonneg a]
    simp [ha, hb]
  · intro h
    simp_all

def DirichletTarget : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    (23 / 24 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) →
      DirichletCharacter.LFunction χ s ≠ 0

/--
@isnad1 id=ne.2h3v.s6.546db22bd6a7 from=translated src=- shape=565a808f vocab=4d8f04de
-/
theorem dirichlet_target_of_one_le_re
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 ≤ s.re) (hprincipal : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hprincipal) hs

/--
@isnad1 id=iff.0h0v.s6.4deed647f50e from=translated src=- shape=b755dc1a vocab=f41d33a1
-/
theorem dirichletTarget_iff_open_strip :
    DirichletTarget ↔
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        (23 / 24 : ℝ) < s.re → s.re < 1 →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  constructor
  · intro h q _ χ s h23 _
    apply h q χ s h23
    intro ⟨_, hs⟩
    simp [hs] at *
  · intro h q _ χ s h23 hprincipal
    by_cases hs : s.re < 1
    · exact h q χ s h23 hs
    · exact dirichlet_target_of_one_le_re q χ s (le_of_not_gt hs) hprincipal

/--
@isnad1 id=eq.0h1v.s5.e7a7ac01bc87 from=translated src=- shape=a99b4232 vocab=84a741a3
-/
theorem cube_index_filter (b : ℕ) :
    (∑ h ∈ b.divisors, (ArithmeticFunction.moebius h : ℤ)) =
      if b = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f b)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  simpa using h

private lemma square_le_two_squares {x y e : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (h : x ≤ y + e) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * e ^ 2 := by
  have h₁ : 0 ≤ y + e - x := sub_nonneg.mpr h
  have h₂ : 0 ≤ y + e + x := by nlinarith
  have h₃ := mul_nonneg h₁ h₂
  have h₄ := sq_nonneg (y - e)
  nlinarith

/--
@isnad1 id=le.7h9v.s8.e99e2f0300cc from=translated src=- shape=1b9e9c92 vocab=41f8616d
-/
theorem finite_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (a : α → ℝ) (a₀ error bound : ℝ)
    (ha₀ : 0 ≤ a₀) (ha : ∀ u, 0 ≤ a u) (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, a₀ ≤ a (row p) + error)
    (hmean : (∑ u ∈ rows, (a u) ^ 2) ≤ bound) :
    (primes.card : ℝ) * a₀ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  have hselected : (∑ p ∈ primes, (a (row p)) ^ 2) ≤ bound := by
    calc
      (∑ p ∈ primes, (a (row p)) ^ 2) =
          ∑ u ∈ primes.image row, (a u) ^ 2 := by
            rw [Finset.sum_image hinj]
      _ ≤ ∑ u ∈ rows, (a u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hrows (by
          intro u _ _
          positivity)
      _ ≤ bound := hmean
  have hpoint (p : β) (hp : p ∈ primes) :
      a₀ ^ 2 ≤ 2 * (a (row p)) ^ 2 + 2 * error ^ 2 :=
    square_le_two_squares ha₀ (ha _) herror (happrox p hp)
  have hsum :
      (∑ p ∈ primes, a₀ ^ 2) ≤
        ∑ p ∈ primes, (2 * (a (row p)) ^ 2 + 2 * error ^ 2) :=
    Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/--
@isnad1 id=le.5h9v.s7.e9f1b56e86dc from=translated src=- shape=84b8cd26 vocab=fd2fc4a5
-/
theorem complex_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (error bound : ℝ)
    (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, ‖A untwisted - A (row p)‖ ≤ error)
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ bound) :
    (primes.card : ℝ) * ‖A untwisted‖ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  apply finite_row_extraction rows primes row (fun u ↦ ‖A u‖)
    ‖A untwisted‖ error bound (norm_nonneg _) (fun u ↦ norm_nonneg _) herror
    hrows hinj ?_ hmean
  intro p hp
  calc
    ‖A untwisted‖ = ‖(A untwisted - A (row p)) + A (row p)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖A untwisted - A (row p)‖ + ‖A (row p)‖ := norm_add_le _ _
    _ ≤ ‖A (row p)‖ + error := by linarith [happrox p hp]

/--
@isnad1 id=eq.0h0v.s5.3417b23be74c from=translated src=- shape=54a42274 vocab=cbf878e5
-/
theorem mean_square_exponent : (21 / 10 : ℚ) - 11 / 60 = 23 / 12 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s5.177b972e58b5 from=translated src=- shape=308ac54c vocab=cbf878e5
-/
theorem approximation_exponent : (2 : ℚ) - 11 / 30 = 49 / 30 := by
  norm_num

/--
@isnad1 id=ne.7h5v.s7.7df1451545f1 from=translated src=- shape=10147444 vocab=23620982
-/
theorem zero_free_of_analytic_identity
    (σ : ℝ) (hσ : σ < 1) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → L s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hzeroIn : (2 : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < (2 : ℂ).re
    simpa using lt_trans hσ (show (1 : ℝ) < 2 by norm_num)
  have heventual : (fun s : ℂ => L s * M s) =ᶠ[nhds (2 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (2 : ℂ) ∈
        {s : ℂ | 1 < s.re}))] with s hs
    exact heq s hs
  have hident : Set.EqOn (fun s : ℂ => L s * M s) W {s | σ < s.re} :=
    (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
      ((convex_halfSpace_re_gt σ).isPreconnected) hzeroIn heventual
  intro hLρ
  have hρeq := hident hρ
  change L ρ * M ρ = W ρ at hρeq
  rw [hLρ, zero_mul] at hρeq
  exact hWρ hρeq.symm

/--
@isnad1 id=ne.9h6v.s8.4527cfe8799f from=translated src=- shape=4e5acd3a vocab=fe580428
-/
theorem zero_free_of_regularized_analytic_identity
    (σ : ℝ) (hσ : σ < 1) (L Lregular M W : ℂ → ℂ)
    (hLregular : AnalyticOnNhd ℂ Lregular {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * L s)
    (heq : ∀ s : ℂ, 1 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hWregular :
      AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * W s) {s | σ < s.re} :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hW
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity σ hσ Lregular M
    (fun s : ℂ => (s - 1) * W s) hLregular hM hWregular heq
    ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2

/--
@isnad1 id=and.20h20v.s9.1c7d2dbe5ad0 from=translated src=- shape=19355efb vocab=8e69f003
-/
theorem two_poisson_scale_substitution
    (K X F B L A C d t J Y g e ge v Li K' X' F' Δ : ℝ)
    (hK : K ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0)
    (ht : t ≠ 0) (hJ : J ≠ 0) (he : e ≠ 0)
    (hge : ge ≠ 0) (hv : v ≠ 0) (hL0 : L ≠ 0)
    (hL : L = X / B ^ 3)
    (hLi : Li = L / (A * C * t))
    (hg : g = e * ge)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hK' : K' = d * e ^ 2 * Li ^ 2 / (Y * g ^ 2))
    (hX' : X' = Li / (g * v))
    (hF' : F' = J * C * e * v)
    (hΔ : Δ = B * F * A * t * ge) :
    K' = K * J / (Δ ^ 2 * B ^ 2) ∧
      X' * F' = X * F * J / (Δ * B ^ 2) := by
  constructor
  · rw [hK', hLi, hg, hY, hΔ]
    field_simp
  · rw [hX', hF', hLi, hL, hg, hΔ]
    field_simp

/--
@isnad1 id=and.11h10v.s8.a4831be96c83 from=translated src=- shape=96b19afa vocab=d8b90f1e
-/
theorem two_poisson_budget
    (K X F R B J Δ K' childColumnMass R' : ℝ)
    (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (hB : 0 < B) (hJpos : 0 < J) (hΔpos : 0 < Δ)
    (hJ : J ≤ B ^ 2) (hΔ : B * F ≤ Δ)
    (hK' : K' = K * J / (Δ ^ 2 * B ^ 2))
    (hM' : childColumnMass = X * F * J / (Δ * B ^ 2))
    (hR' : R' ≤ R * Δ) :
    K' * R' / childColumnMass ≤ K * R / (X * F) ∧
      K' ≤ K / (B * F) ^ 2 ∧
      childColumnMass ≤ X * F / (B * F) ∧
      (Δ * B ^ 2 / J) * childColumnMass = X * F := by
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hBF : 0 < B * F := mul_pos hB hF
  have hXF : 0 < X * F := mul_pos hX hF
  have hMpos : 0 < childColumnMass := by rw [hM']; positivity
  have hK'nonneg : 0 ≤ K' := by rw [hK']; positivity
  constructor
  · have hstep : K' * R' ≤ K' * (R * Δ) :=
      mul_le_mul_of_nonneg_left hR' hK'nonneg
    apply (div_le_div_iff₀ hMpos hXF).2
    calc
      K' * R' * (X * F) ≤ K' * (R * Δ) * (X * F) := by
        gcongr
      _ = (K * R / (X * F)) * childColumnMass * (X * F) := by
        rw [hK', hM']
        field_simp
      _ = K * R * childColumnMass := by field_simp
  constructor
  · rw [hK']
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hΔpos) hB2)
      (sq_pos_of_pos hBF)).2
    have hΔ2 : (B * F) ^ 2 ≤ Δ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hΔ)
        (show 0 ≤ Δ + B * F by positivity)]
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg hK (le_of_lt hB2)) (sub_nonneg.mpr hΔ2)]
  constructor
  · rw [hM']
    apply (div_le_div_iff₀ (mul_pos hΔpos hB2) hBF).2
    have hΔBF : B * F ≤ Δ := hΔ
    nlinarith [mul_nonneg (le_of_lt hXF) (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg (le_of_lt hXF) (le_of_lt hB2))
        (sub_nonneg.mpr hΔBF)]
  · rw [hM']
    field_simp

/--
@isnad1 id=le.9h9v.s7.fd01b3e9f2cb from=translated src=- shape=b4b0879b vocab=373ada53
-/
theorem two_poisson_charge
    (R R' b0 B F A t ge Δ : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hF : 1 ≤ F) (hA : 1 ≤ A)
    (ht : 0 ≤ t) (hge : 0 ≤ ge)
    (hb0B : b0 ≤ B)
    (hR' : R' ≤ R * b0 * t * ge)
    (hΔ : Δ = B * F * A * t * ge) : R' ≤ R * Δ := by
  calc
    R' ≤ R * b0 * t * ge := hR'
    _ ≤ R * B * t * ge := by gcongr
    _ ≤ R * (B * F * A * t * ge) := by
      have hBA : B ≤ B * F * A := by
        have hBF : B ≤ B * F := by nlinarith
        have hBFA : B * F ≤ B * F * A := by
          nlinarith [mul_nonneg (mul_nonneg hB (le_trans zero_le_one hF))
            (sub_nonneg.mpr hA)]
        exact hBF.trans hBFA
      nlinarith [mul_nonneg (mul_nonneg hR (sub_nonneg.mpr hBA))
        (mul_nonneg ht hge)]
    _ = R * Δ := by rw [hΔ]

/--
@isnad1 id=eq.15h18v.s9.00694bd4f1bc from=translated src=- shape=a90109e2 vocab=ef8d8fda
-/
theorem two_poisson_cost_identity
    (K A C d L B F c Y g e Li J t ge v X Δ : ℝ)
    (hK : K ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0) (hL : L ≠ 0)
    (hB : B ≠ 0) (hF : F ≠ 0) (hc : 0 < c)
    (hg : g ≠ 0) (he : e ≠ 0) (hLi : Li ≠ 0)
    (hJ : J ≠ 0) (hv : v ≠ 0)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hM : X = Li / (g * v) * (J * C * e * v))
    (hΔ : Δ = B * F * A * t * ge) :
    (K * A * C / (d * L ^ 2 * B ^ 2 * F * Real.sqrt c)) *
      (Y * g / (e * Li)) *
      ((B * Real.sqrt c / J) * t * ge) * X = Δ * B ^ 2 / J := by
  have hcsqrt : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  rw [hY, hM, hΔ]
  field_simp

end ShortDraft

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=eq.1h2v.s9.92a959ac40cf from=translated src=- shape=5c2e507e vocab=612240de
-/
theorem sextic_character_exponent (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ 3 := by
  calc
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ (-3 : ℤ) := by group
    _ = χ ^ 3 := by
      calc
        χ ^ (-3 : ℤ) = χ ^ ((-3 : ℤ) + 6) := by
          rw [zpow_add, zpow_ofNat, hχ, mul_one]
        _ = χ ^ 3 := by norm_num

/--
@isnad1 id=eq.1h4v.s7.a98a860b3318 from=translated src=- shape=92404a51 vocab=623b7913
-/
theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (a : F) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst a
    have hshift : ψ.mulShift (0 : F) = 1 := by
      ext x
      simp
    rw [hshift, gaussSum_one_right hχ]
    simp
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    simpa [hu.unit_spec] using gaussSum_mulShift_eq χ ψ hu.unit

/--
@isnad1 id=eq.0h3v.s7.c9607756422c from=translated src=- shape=b103b7da vocab=2a7205f6
-/
theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  have hzero : χ (0 : F) * ψ (0 : F) = 0 := by simp
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, hzero, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun y : Fˣ => χ (y : F) * ψ (y : F))
        (fun x : {x : F // x ≠ 0} => χ x * ψ x) ?_).symm
      intro y
      rfl

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=eq.1h2v.s9.40db6dcbccd2 from=translated src=- shape=0718e572 vocab=5aefe7d6
-/
theorem sextic_character_quadratic (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    (χ ^ 3)⁻¹ = χ ^ 3 := by
  calc
    (χ ^ 3)⁻¹ = χ ^ (-3 : ℤ) := by group
    _ = χ ^ 3 := by
      calc
        χ ^ (-3 : ℤ) = χ ^ ((-3 : ℤ) + 6) := by
          rw [zpow_add, zpow_ofNat, hχ, mul_one]
        _ = χ ^ 3 := by norm_num

/--
@isnad1 id=eq.1h4v.s10.5a4c997fbcde from=translated src=- shape=268a1b44 vocab=9c8698e6
-/
theorem sextic_inversion_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by
  classical
  calc
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) (y⁻¹) * ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro y
          simp
    _ = ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      rw [sextic_character_exponent χ hχ]
      have hy := sextic_character_quadratic χ hχ
      have hval : (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3) (y : F) := by
        calc
          (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3)⁻¹ (y : F) := by
            rw [MulChar.inv_apply', Units.val_inv_eq_inv_val]
          _ = (χ ^ 3) (y : F) := by rw [hy]
      rw [← Units.val_inv_eq_inv_val y, hval]

/--
@isnad1 id=eq.1h4v.s9.bbef2e4e32fe from=translated src=- shape=2fb1d8a7 vocab=ad2ac8e3
-/
theorem sextic_inversion_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ 3) (ψ.mulShift a) := by
  rw [sextic_inversion_sum χ ψ hχ a, gaussSum_eq_units_sum]
  simp only [AddChar.mulShift_apply]

/--
@isnad1 id=eq.2h5v.s10.f77e09d761c2 from=translated src=- shape=bb66e8bf vocab=b20fe894
-/
theorem sextic_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 3) ε * gaussSum (χ ^ 3) ψ * (χ ^ 3) x := by
  rw [sextic_inversion_gaussSum χ ψ hχ (ε * x)]
  rw [gaussSum_mulShift_any (χ ^ 3) ψ hχ₃ (ε * x)]
  rw [sextic_character_quadratic χ hχ, map_mul]
  ring

/--
@isnad1 id=eq.1h3v.s8.caeec5e1dbed from=translated src=- shape=f2a611f2 vocab=a48cc313
-/
theorem additive_unit_sum (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a : F) :
    (∑ y : Fˣ, ψ (a * (y : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hgauss : (∑ y : Fˣ, ψ (a * (y : F))) =
      gaussSum (1 : MulChar F ℂ) (ψ.mulShift a) := by
    rw [gaussSum_eq_units_sum]
    simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
  rw [hgauss]
  split_ifs with ha
  · subst a
    simp only [AddChar.mulShift_zero, gaussSum_one_one]
    exact_mod_cast (Nat.card_eq_fintype_card (α := Fˣ))
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have hshift : ψ.mulShift a ≠ 1 := by
      intro heq
      exact hψ ((AddChar.mulShift_unit_eq_one_iff ψ hu).mp heq)
    exact gaussSum_one_left hshift

/--
@isnad1 id=eq.2h4v.s10.ba32903c7b55 from=translated src=- shape=e28f966f vocab=07fd26ed
-/
theorem sextic_fourth_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hexp : ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = 1 := by
    calc
      ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = (χ ^ 6)⁻¹ := by group
      _ = 1 := by rw [hχ, inv_one]
  rw [hexp]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp
    _ = _ := additive_unit_sum ψ hψ a

/--
@isnad1 id=eq.1h5v.s10.0914bcb6a974 from=translated src=- shape=81030345 vocab=b20fe894
-/
theorem active_zero_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
  classical
  have hquad : ((χ⁻¹) ^ 2)⁻¹ = χ ^ 2 := by group
  calc
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ ^ 2) (y : F) * ψ ((ε * x) * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
          rw [← hquad, MulChar.inv_apply', inv_inv]
    _ = gaussSum (χ ^ 2) (ψ.mulShift (ε * x)) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
    _ = (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
      rw [gaussSum_mulShift_any (χ ^ 2) ψ hχ₂ (ε * x)]
      rw [map_mul]
      ring

/--
@isnad1 id=eq.1h4v.s8.49826db53f72 from=translated src=- shape=040d58a6 vocab=a0a9e98d
-/
theorem nontrivial_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  calc
    (∑ t : F, χ t * ψ (-(h * t))) =
        gaussSum χ ((ψ.mulShift (-1)).mulShift h) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) :=
      gaussSum_mulShift_any χ (ψ.mulShift (-1)) hχ h

/--
@isnad1 id=eq.1h3v.s8.c0998390dff1 from=translated src=- shape=2b7531f9 vocab=dfb19c70
-/
theorem trivial_fourier_coefficient (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (h : F) :
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
      if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  calc
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
        gaussSum (1 : MulChar F ℂ) (ψ.mulShift (-h)) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = ∑ u : Fˣ, ψ ((-h) * (u : F)) := by
      rw [gaussSum_eq_units_sum]
      simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
    _ = if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
      simpa only [neg_eq_zero] using additive_unit_sum ψ hψ (-h)

/--
@isnad1 id=eq.2h6v.s10.c62bf7a05d18 from=translated src=- shape=9a60bbed vocab=9fa9053c
-/
theorem sextic_fourier_theta_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  classical
  have hχ₁ : χ ≠ 1 := by
    intro heq
    exact hχ₃ (by simp [heq])
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ((χ⁻¹) ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * (χ⁻¹) ^ 2) h *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ₁, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, sextic_local_row χ ψ hχ hχ₃ ε x]
  ring

end ShortDraftLocal

end OAI
