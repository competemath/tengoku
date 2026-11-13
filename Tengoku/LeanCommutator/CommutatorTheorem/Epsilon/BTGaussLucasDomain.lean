import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTStableLine
import Tengoku.Seed.Analysis.Complex.OpenMapping
import Tengoku.Seed.Analysis.Analytic.Polynomial
import Tengoku.Seed.Algebra.MvPolynomial.Funext

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/Epsilon/BTGaussLucasDomain.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! # The product upper-half-plane domain used in multivariate Gauss--Lucas -/

namespace CommutatorTheorem.BTGaussLucasDomain

open Set
open CommutatorTheorem.BTRealStabilityClosure

/-- The Cartesian product of open upper half-planes.-/
def upperHalfPlaneProduct (sigma : Type*) : Set (sigma → ℂ) :=
  {z | ∀ i, InUpperHalfPlane (z i)}

/--
@isnad1 id=iff.0h2v.s4.4608f433ad6a from=translated src=- shape=73ef1642 vocab=26de4e35
-/
@[simp] theorem mem_upperHalfPlaneProduct {sigma : Type*} {z : sigma → ℂ} :
    z ∈ upperHalfPlaneProduct sigma ↔ ∀ i, InUpperHalfPlane (z i) :=
  Iff.rfl

/--
@isnad1 id=isopen.0h1v.s4.1e27c14b7cd3 from=translated src=- shape=fea4225f vocab=e729a7f0
-/
theorem isOpen_upperHalfPlaneProduct (sigma : Type*) [Finite sigma] :
    IsOpen (upperHalfPlaneProduct sigma) := by
  have hset : upperHalfPlaneProduct sigma =
      Set.univ.pi (fun _ : sigma ↦ {z : ℂ | 0 < z.im}) := by
    ext z
    simp [upperHalfPlaneProduct, InUpperHalfPlane]
  rw [hset]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦
    isOpen_lt continuous_const Complex.continuous_im

-- Preserve the existing parameter list for downstream callers.
/--
@isnad1 id=convex.0h1v.s5.dcfd7bb78d55 from=translated src=- shape=629f2229 vocab=5b9841d9
-/
theorem convex_upperHalfPlaneProduct (sigma : Type*) [Fintype sigma] :
    Convex ℝ (upperHalfPlaneProduct sigma) := by
  have hset : upperHalfPlaneProduct sigma =
      Set.univ.pi (fun _ : sigma ↦ {z : ℂ | 0 < z.im}) := by
    ext z
    simp [upperHalfPlaneProduct, InUpperHalfPlane]
  rw [hset]
  apply convex_pi
  intro i _
  exact convex_halfSpace_gt Complex.imCLM.isLinear 0

-- Preserve the existing parameter list for downstream callers.
/--
@isnad1 id=isprecon.0h1v.s4.b60049cc2f37 from=translated src=- shape=fea4225f vocab=8dccdb75
-/
theorem isPreconnected_upperHalfPlaneProduct (sigma : Type*) [Fintype sigma] :
    IsPreconnected (upperHalfPlaneProduct sigma) :=
  (convex_upperHalfPlaneProduct sigma).isPreconnected

/--
@isnad1 id=nonempty.0h1v.s3.0806bb9eb073 from=translated src=- shape=01e60de4 vocab=ce34d0e0
-/
theorem nonempty_upperHalfPlaneProduct (sigma : Type*) :
    (upperHalfPlaneProduct sigma).Nonempty := by
  refine ⟨fun _ ↦ Complex.I, ?_⟩
  simp [upperHalfPlaneProduct, InUpperHalfPlane]

/-- The open upper half-plane is infinite; the horizontal line `x + I`
already gives an injective infinite subset.
@isnad1 id=infinite.0h0v.s3.f220b194d2e2 from=translated src=- shape=66b19da4 vocab=af8117f4
-/
theorem infinite_upperHalfPlane :
    ({z : ℂ | InUpperHalfPlane z} : Set ℂ).Infinite := by
  let f : ℝ → ℂ := fun x ↦ (x : ℂ) + Complex.I
  have hf : Function.Injective f := by
    intro x y hxy
    have hre := congrArg Complex.re hxy
    simpa [f] using hre
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨x, rfl⟩
  simp [f, InUpperHalfPlane]

/-- An open subset of `ℂ` containing zero cannot stay inside the closed
lower half-plane.
@isnad1 id=not.2h1v.s5.694f76edb186 from=translated src=- shape=74ef6416 vocab=98deb23a
-/
theorem not_isOpen_of_zero_mem_of_im_nonpos {s : Set ℂ}
    (hzero : 0 ∈ s) (him : ∀ z ∈ s, z.im ≤ 0) : ¬ IsOpen s := by
  intro hs
  have hsnhds : s ∈ nhds (0 : ℂ) := hs.mem_nhds hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hsnhds
  let z : ℂ := (ε / 2 : ℝ) * Complex.I
  have hzball : z ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball]
    simp only [dist_zero_right, z, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hz := him z (hball hzball)
  have hzim : z.im = ε / 2 := by simp [z]
  rw [hzim] at hz
  linarith

/-- A multivariate complex polynomial vanishing throughout the product upper
half-plane is the zero polynomial.
@isnad1 id=eq.1h2v.s7.baf977e459bc from=translated src=- shape=9d61d4d3 vocab=5fa2946f
-/
theorem mvPolynomial_eq_zero_of_eval_zero_upper
    {sigma : Type*} {q : MvPolynomial sigma ℂ}
    (hq : ∀ z ∈ upperHalfPlaneProduct sigma,
      MvPolynomial.eval z q = 0) :
    q = 0 := by
  apply MvPolynomial.funext_set
    (fun _ : sigma ↦ {z : ℂ | InUpperHalfPlane z})
    (fun _ ↦ infinite_upperHalfPlane)
  intro z hz
  rw [hq z]
  · simp
  · intro i
    exact hz i (Set.mem_univ i)

end CommutatorTheorem.BTGaussLucasDomain
