import Tengoku.LanaHeights.Heights.WeierstrassCurveTopology
import Tengoku.Seed.Analysis.Calculus.FDeriv.Pow
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option linter.style.header false

/-!
# Finite analytic germs on complex Weierstrass curves

At a finite point of a nonsingular complex Weierstrass equation, at least one
of the two equation derivatives is nonzero.  This file computes the complex
Fréchet derivative of the affine equation and applies the complex implicit
function theorem in either coordinate.  The resulting implicit functions are
complex analytic at the base point, parametrize the equation in a
neighbourhood, and are locally unique.

The inverse-function neighborhoods are also restricted along the zero fiber to
explicit `OpenPartialHomeomorph`s from the affine equation locus to `ℂ`, in
both coordinate directions, and every finite point lies in one chart source.
The companion file `Heights.WeierstrassFiniteManifold` packages whole-overlap
holomorphic transitions and installs a `ChartedSpace` on the affine locus.
Neither file installs a charted space on the compact point type or addresses
the chart at infinity. In particular, no manifold structure is transported
from a period lattice.
-/

open Filter
open scoped ContDiff Topology

noncomputable section

namespace Heights

/-- The affine Weierstrass polynomial, viewed as a complex-valued function on
`ℂ × ℂ`. -/
def complexWeierstrassEquation (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 -
    (p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)

/-- The partial derivative of the affine equation with respect to `x`. -/
def complexWeierstrassEquationX (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  W.a₁ * p.2 - (3 * p.1 ^ 2 + 2 * W.a₂ * p.1 + W.a₄)

/-- The partial derivative of the affine equation with respect to `y`. -/
def complexWeierstrassEquationY (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  2 * p.2 + W.a₁ * p.1 + W.a₃

/--
@isnad1 id=iff.0h2v.s5.956cc5ab8b8e from=translated src=- shape=3239fea4 vocab=fa1ffb9b
-/
@[simp] theorem complexWeierstrassEquation_eq_zero_iff
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquation W p = 0 ↔
      W.toAffine.Equation p.1 p.2 := by
  rw [WeierstrassCurve.Affine.equation_iff']
  rfl

/--
@isnad1 id=eq.0h2v.s5.22338e93842e from=translated src=- shape=15c6ce88 vocab=2262672a
-/
@[simp] theorem complexWeierstrassEquationX_eq_polynomialX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquationX W p =
      W.toAffine.polynomialX.evalEval p.1 p.2 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialX]
  rfl

/--
@isnad1 id=eq.0h2v.s5.4da654fd6419 from=translated src=- shape=15c6ce88 vocab=327b5863
-/
@[simp] theorem complexWeierstrassEquationY_eq_polynomialY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquationY W p =
      W.toAffine.polynomialY.evalEval p.1 p.2 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  rfl

/-- The affine equation is an entire function on `ℂ × ℂ`.
@isnad1 id=contdiff.0h1v.s5.b7ca1f2781f8 from=translated src=- shape=d173f0b9 vocab=e5da47bf
-/
theorem contDiff_complexWeierstrassEquation (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassEquation W) := by
  unfold complexWeierstrassEquation
  fun_prop

/-- The exact complex Fréchet derivative of the affine equation.
@isnad1 id=hasfderi.0h2v.s9.3f969c566106 from=translated src=- shape=70ebc313 vocab=9546a304
-/
theorem hasFDerivAt_complexWeierstrassEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassEquation W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p)) p := by
  have hx : HasFDerivAt (fun q : ℂ × ℂ => q.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℂ × ℂ => q.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
  have hyy := hy.pow 2
  have ha1xy := ((hasFDerivAt_const W.a₁ p).mul hx).mul hy
  have ha3y := (hasFDerivAt_const W.a₃ p).mul hy
  have hxxx := hx.pow 3
  have ha2xx := (hasFDerivAt_const W.a₂ p).mul (hx.pow 2)
  have ha4x := (hasFDerivAt_const W.a₄ p).mul hx
  have ha6 : HasFDerivAt (fun _ : ℂ × ℂ => W.a₆)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) p := hasFDerivAt_const W.a₆ p
  have h := ((hyy.add ha1xy).add ha3y).sub
      (((hxxx.add ha2xx).add ha4x).add ha6)
  change HasFDerivAt (complexWeierstrassEquation W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassEquation W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨z, w⟩
    simp [complexWeierstrassEquationX, complexWeierstrassEquationY]
    ring
  rwa [hfd] at hd

private theorem isInvertible_smulRight_id (a : ℂ) (ha : a ≠ 0) :
    ((ContinuousLinearMap.id ℂ ℂ).smulRight a).IsInvertible := by
  let u : ℂˣ := Units.mk0 a ha
  refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℂ) u, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  simp [u, mul_comm]

/-- If the `y`-derivative is nonzero, the partial Fréchet derivative in the
second factor is invertible.
@isnad1 id=isinvert.1h2v.s8.ed0e2a5dbdbf from=translated src=- shape=038cefd5 vocab=4383b1e4
-/
theorem isInvertible_fderiv_inr_complexWeierstrassEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    (fderiv ℂ (complexWeierstrassEquation W) p ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassEquation W p).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationX W p) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationY W p)) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p) := by
    apply ContinuousLinearMap.ext
    intro z
    simp
  rw [heq]
  exact isInvertible_smulRight_id _ hy

/-- The implicit holomorphic `y`-coordinate near a point where `∂F/∂y ≠ 0`. -/
def complexWeierstrassImplicitY (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) : ℂ → ℂ :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/--
@isnad1 id=eq.1h2v.s5.60b39867a02e from=translated src=- shape=8ce5558b vocab=7c7c6b34
-/
@[simp] theorem complexWeierstrassImplicitY_apply_self
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    complexWeierstrassImplicitY W p hy p.1 = p.2 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.implicitFunction_apply_self
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- Near its base point, the implicit `y`-function parametrizes the same level
set of the Weierstrass equation.
@isnad1 id=eventual.1h2v.s6.6f69ede1b7d1 from=translated src=- shape=af7ef254 vocab=189229d9
-/
theorem eventually_complexWeierstrassEquation_iff_implicitY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ∀ᶠ q in 𝓝 p,
      complexWeierstrassEquation W q = complexWeierstrassEquation W p ↔
        complexWeierstrassImplicitY W p hy q.1 = q.2 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.eventually_apply_eq_iff_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- If the base point lies on the curve, the graph of the implicit `y`-function
lies on the curve near the base coordinate.
@isnad1 id=eventual.2h2v.s6.46f4201d273f from=translated src=- shape=9ccac7d1 vocab=26b2ad58
-/
theorem eventually_complexWeierstrassImplicitY_equation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ∀ᶠ x in 𝓝 p.1,
      W.toAffine.Equation x (complexWeierstrassImplicitY W p hy x) := by
  have h :=
    (contDiff_complexWeierstrassEquation W).contDiffAt.eventually_apply_implicitFunction
      (u := p) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)
  have hp0 : complexWeierstrassEquation W p = 0 :=
    (complexWeierstrassEquation_eq_zero_iff W p).2 hp
  filter_upwards [h] with x hx
  apply (complexWeierstrassEquation_eq_zero_iff W
    (x, complexWeierstrassImplicitY W p hy x)).1
  simpa [hp0, complexWeierstrassImplicitY] using hx

/-- The implicit `y`-coordinate is complex analytic at its base coordinate.
@isnad1 id=contdiff.1h2v.s5.3d62a9451bfe from=translated src=- shape=21f921b8 vocab=28602d94
-/
theorem contDiffAt_complexWeierstrassImplicitY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ContDiffAt ℂ ω (complexWeierstrassImplicitY W p hy) p.1 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.contDiffAt_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- The affine equation with coordinates exchanged.  Its second variable is
`x`, so the ordinary product-domain implicit theorem solves for `x`. -/
def complexWeierstrassEquationSwap (W : WeierstrassCurve ℂ)
    (p : ℂ × ℂ) : ℂ :=
  complexWeierstrassEquation W (p.2, p.1)

/-- The swapped equation is entire.
@isnad1 id=contdiff.0h1v.s5.1264e8d27cfe from=translated src=- shape=d173f0b9 vocab=197d7498
-/
theorem contDiff_complexWeierstrassEquationSwap (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassEquationSwap W) := by
  unfold complexWeierstrassEquationSwap
  exact (contDiff_complexWeierstrassEquation W).comp (by fun_prop)

/-- The exact derivative of the equation after exchanging coordinates.
@isnad1 id=hasfderi.0h2v.s9.2e3cf2637261 from=translated src=- shape=61dcae22 vocab=c8603a51
-/
theorem hasFDerivAt_complexWeierstrassEquationSwap
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassEquationSwap W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W (p.2, p.1)) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1))) p := by
  have hs : HasFDerivAt (fun q : ℂ × ℂ => (q.2, q.1))
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod
        (ContinuousLinearMap.fst ℂ ℂ ℂ)) p :=
    hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have h := (hasFDerivAt_complexWeierstrassEquation W (p.2, p.1)).comp p hs
  change HasFDerivAt (complexWeierstrassEquationSwap W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassEquationSwap W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W (p.2, p.1)) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1)) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨z, w⟩
    simp
    ring
  rwa [hfd] at hd

/-- If the `x`-derivative is nonzero, the second-factor derivative of the
swapped equation is invertible.
@isnad1 id=isinvert.1h2v.s8.06cbb655fe20 from=translated src=- shape=b61912f6 vocab=9978cbe0
-/
theorem isInvertible_fderiv_inr_complexWeierstrassEquationSwap
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W (p.2, p.1) ≠ 0) :
    (fderiv ℂ (complexWeierstrassEquationSwap W) p ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassEquationSwap W p).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationY W (p.2, p.1)) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationX W (p.2, p.1))) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp
  rw [heq]
  exact isInvertible_smulRight_id _ hx

/-- The implicit holomorphic `x`-coordinate near a point where `∂F/∂x ≠ 0`.
Its argument is the `y`-coordinate. -/
def complexWeierstrassImplicitX (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) : ℂ → ℂ :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

/--
@isnad1 id=eq.1h2v.s5.1b185be797a7 from=translated src=- shape=8ce5558b vocab=e1b0d0df
-/
@[simp] theorem complexWeierstrassImplicitX_apply_self
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    complexWeierstrassImplicitX W p hx p.2 = p.1 :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.implicitFunction_apply_self
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

/-- Near its base point, the implicit `x`-function parametrizes the same level
set of the Weierstrass equation.
@isnad1 id=eventual.1h2v.s6.476093132f7f from=translated src=- shape=af7ef254 vocab=433f2ac8
-/
theorem eventually_complexWeierstrassEquation_iff_implicitX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ∀ᶠ q in 𝓝 p,
      complexWeierstrassEquation W q = complexWeierstrassEquation W p ↔
        complexWeierstrassImplicitX W p hx q.2 = q.1 := by
  have h :=
    (contDiff_complexWeierstrassEquationSwap W).contDiffAt.eventually_apply_eq_iff_implicitFunction
      (u := (p.2, p.1)) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W (p.2, p.1) hx)
  have hswap : Tendsto (fun q : ℂ × ℂ => (q.2, q.1)) (𝓝 p) (𝓝 (p.2, p.1)) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  filter_upwards [h.filter_mono hswap] with q hq
  simpa [complexWeierstrassEquationSwap, complexWeierstrassImplicitX] using hq

/-- If the base point lies on the curve, the graph of the implicit `x`-function
lies on the curve near the base coordinate.
@isnad1 id=eventual.2h2v.s6.8c1cd649842d from=translated src=- shape=4bf92a70 vocab=13fc6ded
-/
theorem eventually_complexWeierstrassImplicitX_equation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ∀ᶠ y in 𝓝 p.2,
      W.toAffine.Equation (complexWeierstrassImplicitX W p hx y) y := by
  have h :=
    (contDiff_complexWeierstrassEquationSwap W).contDiffAt.eventually_apply_implicitFunction
      (u := (p.2, p.1)) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W (p.2, p.1) hx)
  have hp0 : complexWeierstrassEquationSwap W (p.2, p.1) = 0 := by
    apply (complexWeierstrassEquation_eq_zero_iff W p).2 hp
  filter_upwards [h] with y hy
  apply (complexWeierstrassEquation_eq_zero_iff W
    (complexWeierstrassImplicitX W p hx y, y)).1
  change complexWeierstrassEquationSwap W
    (y, complexWeierstrassImplicitX W p hx y) = 0
  exact hy.trans hp0

/-- The implicit `x`-coordinate is complex analytic at its base coordinate.
@isnad1 id=contdiff.1h2v.s5.94014ff68df5 from=translated src=- shape=21f921b8 vocab=4b6e386f
-/
theorem contDiffAt_complexWeierstrassImplicitX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ContDiffAt ℂ ω (complexWeierstrassImplicitX W p hx) p.2 :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.contDiffAt_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

/-- The inverse-function-theorem neighborhood in ambient `ℂ × ℂ` whose
forward map is `(x, y) ↦ (F(x,y), x)`.  Restricting its zero fiber produces
the topological chart in the `x`-coordinate. -/
def complexWeierstrassImplicitYAmbientHomeomorph
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  let e :=
    (((contDiff_complexWeierstrassEquation W).contDiffAt.hasStrictFDerivAt
      (by simp)).implicitFunctionDataOfProdDomain
        (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)).toOpenPartialHomeomorph
  e.restrOpen {q | complexWeierstrassEquationY W q ≠ 0} (by
    apply isOpen_ne.preimage
    unfold complexWeierstrassEquationY
    fun_prop)

/--
@isnad1 id=mem.1h2v.s7.060f829584ed from=translated src=- shape=1955f1a9 vocab=ac89a1e3
-/
theorem complexWeierstrassImplicitYAmbientHomeomorph_mem_source
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    p ∈ (complexWeierstrassImplicitYAmbientHomeomorph W p hy).source := by
  rw [complexWeierstrassImplicitYAmbientHomeomorph,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _, hy⟩

/--
@isnad1 id=eq.1h3v.s6.5293269e6ded from=translated src=- shape=64a90479 vocab=3e5055d3
-/
@[simp] theorem complexWeierstrassImplicitYAmbientHomeomorph_apply
    (W : WeierstrassCurve ℂ) (p q : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    complexWeierstrassImplicitYAmbientHomeomorph W p hy q =
      (complexWeierstrassEquation W q, q.1) :=
  rfl

/-- The inverse of the restricted ambient implicit-function neighborhood is
complex analytic at every point of its target, not only at its original
center.  Restricting the source to `∂F/∂y ≠ 0` is what makes this whole-target
statement available.
@isnad1 id=contdiff.2h3v.s8.afaa0db3078a from=translated src=- shape=50bcdd80 vocab=f510ff21
-/
theorem contDiffAt_complexWeierstrassImplicitYAmbientHomeomorph_symm
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) (z : ℂ × ℂ)
    (hz : z ∈ (complexWeierstrassImplicitYAmbientHomeomorph W p hy).target) :
    ContDiffAt ℂ ω
      (complexWeierstrassImplicitYAmbientHomeomorph W p hy).symm z := by
  let e := complexWeierstrassImplicitYAmbientHomeomorph W p hy
  let q := e.symm z
  have hqsource : q ∈ e.source := e.map_target hz
  have hqy : complexWeierstrassEquationY W q ≠ 0 := by
    exact hqsource.2
  let φ :=
    ((contDiff_complexWeierstrassEquation W).contDiffAt.hasStrictFDerivAt
      (by simp)).implicitFunctionDataOfProdDomain
        (isInvertible_fderiv_inr_complexWeierstrassEquation W q hqy)
  apply e.contDiffAt_symm hz
  · change HasFDerivAt
      (fun q : ℂ × ℂ => (complexWeierstrassEquation W q, q.1)) _ q
    have hφ := φ.hasStrictFDerivAt.hasFDerivAt
    change HasFDerivAt
      (fun q : ℂ × ℂ => (complexWeierstrassEquation W q, q.1)) _ q at hφ
    exact hφ
  · change ContDiffAt ℂ ω
      (fun q : ℂ × ℂ => (complexWeierstrassEquation W q, q.1)) q
    exact (contDiff_complexWeierstrassEquation W).contDiffAt.prodMk contDiffAt_fst

private def complexWeierstrassImplicitYChartInv
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hy : complexWeierstrassEquationY W p ≠ 0) (x : ℂ) :
    ComplexWeierstrassAffine W := by
  classical
  exact if hx : (0, x) ∈
      (complexWeierstrassImplicitYAmbientHomeomorph W p hy).target then
    ⟨(complexWeierstrassImplicitYAmbientHomeomorph W p hy).symm (0, x),
      (complexWeierstrassEquation_eq_zero_iff W _).1 (by
        have hright :=
          (complexWeierstrassImplicitYAmbientHomeomorph W p hy).right_inv hx
        exact congrArg Prod.fst hright)⟩
  else ⟨p, hp⟩

private theorem complexWeierstrassImplicitYChartInv_coe_of_mem
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hy : complexWeierstrassEquationY W p ≠ 0) (x : ℂ)
    (hx : (0, x) ∈
      (complexWeierstrassImplicitYAmbientHomeomorph W p hy).target) :
    (complexWeierstrassImplicitYChartInv W p hp hy x : ℂ × ℂ) =
      (complexWeierstrassImplicitYAmbientHomeomorph W p hy).symm (0, x) := by
  classical
  simp [complexWeierstrassImplicitYChartInv, hx]

/-- The zero-fiber restriction of the ambient inverse-function neighborhood is
an open partial homeomorphism from the affine equation locus to `ℂ`.  It is a
finite topological chart whose forward map is the `x`-coordinate. -/
def complexWeierstrassImplicitYChart
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hy : complexWeierstrassEquationY W P.1 ≠ 0) :
    OpenPartialHomeomorph (ComplexWeierstrassAffine W) ℂ := by
  let e := complexWeierstrassImplicitYAmbientHomeomorph W P.1 hy
  let inv := complexWeierstrassImplicitYChartInv W P.1 P.2 hy
  refine
    { toFun := fun Q => Q.1.1
      invFun := inv
      source := {Q | Q.1 ∈ e.source}
      target := {x | (0, x) ∈ e.target}
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := ?_
      open_target := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro Q hQ
    change (0, Q.1.1) ∈ e.target
    have hm := e.map_source hQ
    have hzero : complexWeierstrassEquation W Q.1 = 0 :=
      (complexWeierstrassEquation_eq_zero_iff W Q.1).2 Q.2
    simpa [e, hzero] using hm
  · intro x hx
    change (inv x).1 ∈ e.source
    rw [complexWeierstrassImplicitYChartInv_coe_of_mem W P.1 P.2 hy x hx]
    exact e.map_target hx
  · intro Q hQ
    apply Subtype.ext
    change (inv Q.1.1).1 = Q.1
    have ht : (0, Q.1.1) ∈ e.target := by
      have hm := e.map_source hQ
      have hzero : complexWeierstrassEquation W Q.1 = 0 :=
        (complexWeierstrassEquation_eq_zero_iff W Q.1).2 Q.2
      simpa [e, hzero] using hm
    rw [complexWeierstrassImplicitYChartInv_coe_of_mem W P.1 P.2 hy _ ht]
    have hleft := e.left_inv hQ
    have hzero : complexWeierstrassEquation W Q.1 = 0 :=
      (complexWeierstrassEquation_eq_zero_iff W Q.1).2 Q.2
    simpa [e, hzero] using hleft
  · intro x hx
    rw [complexWeierstrassImplicitYChartInv_coe_of_mem W P.1 P.2 hy x hx]
    have hright := e.right_inv hx
    exact congrArg Prod.snd hright
  · exact continuous_subtype_val.fst.continuousOn
  · rw [continuousOn_iff_continuous_domRestrict]
    let inc : {x : ℂ | (0, x) ∈ e.target} → ℂ × ℂ := fun x => (0, x.1)
    have hinc : Continuous inc := continuous_const.prodMk continuous_subtype_val
    have hamb : Continuous (fun x => e.symm (inc x)) :=
      e.continuousOn_symm.comp_continuous hinc (fun x => x.2)
    let g : {x : ℂ | (0, x) ∈ e.target} → ComplexWeierstrassAffine W :=
      fun x => ⟨e.symm (inc x),
        (complexWeierstrassEquation_eq_zero_iff W _).1 (by
          have hright := e.right_inv x.2
          exact congrArg Prod.fst hright)⟩
    have hg : Continuous g := Continuous.subtype_mk hamb _
    have heq : {x : ℂ | (0, x) ∈ e.target}.domRestrict inv = g := by
      funext x
      apply Subtype.ext
      exact complexWeierstrassImplicitYChartInv_coe_of_mem
        W P.1 P.2 hy x.1 x.2
    rw [heq]
    exact hg
  · exact e.open_source.preimage continuous_subtype_val
  · exact e.open_target.preimage (continuous_const.prodMk continuous_id)

/--
@isnad1 id=eq.1h3v.s7.b16bd3c460d1 from=translated src=- shape=a5740e51 vocab=8a967797
-/
@[simp] theorem complexWeierstrassImplicitYChart_apply
    (W : WeierstrassCurve ℂ) (P Q : ComplexWeierstrassAffine W)
    (hy : complexWeierstrassEquationY W P.1 ≠ 0) :
    complexWeierstrassImplicitYChart W P hy Q = Q.1.1 :=
  rfl

/--
@isnad1 id=mem.1h2v.s7.24e075765061 from=translated src=- shape=386508ee vocab=b7542e18
-/
theorem complexWeierstrassImplicitYChart_mem_source
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hy : complexWeierstrassEquationY W P.1 ≠ 0) :
    P ∈ (complexWeierstrassImplicitYChart W P hy).source :=
  complexWeierstrassImplicitYAmbientHomeomorph_mem_source W P.1 hy

/-- On its target, the inverse topological chart is exactly the graph of the
implicit analytic `y`-function constructed above.
@isnad1 id=eq.2h3v.s8.c648a363d851 from=translated src=- shape=f50d95c6 vocab=8be43bb0
-/
theorem complexWeierstrassImplicitYChart_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hy : complexWeierstrassEquationY W P.1 ≠ 0) (x : ℂ)
    (hx : x ∈ (complexWeierstrassImplicitYChart W P hy).target) :
    ((complexWeierstrassImplicitYChart W P hy).symm x :
        ComplexWeierstrassAffine W) =
      (x, complexWeierstrassImplicitY W P.1 hy x) := by
  let e := complexWeierstrassImplicitYAmbientHomeomorph W P.1 hy
  change (complexWeierstrassImplicitYChartInv W P.1 P.2 hy x : ℂ × ℂ) = _
  rw [complexWeierstrassImplicitYChartInv_coe_of_mem W P.1 P.2 hy x hx]
  apply Prod.ext_iff.mpr
  constructor
  · have hright := e.right_inv hx
    exact congrArg Prod.snd hright
  · have hzero : complexWeierstrassEquation W P.1 = 0 :=
      (complexWeierstrassEquation_eq_zero_iff W P.1).2 P.2
    change (e.symm (0, x)).2 = (e.symm (complexWeierstrassEquation W P.1, x)).2
    rw [hzero]

/-- The inverse of the finite `x`-coordinate chart is complex analytic at
every point of its target, in ambient affine coordinates.
@isnad1 id=contdiff.2h3v.s8.1b8090ab713b from=translated src=- shape=fbe62eb1 vocab=1a05730f
-/
theorem contDiffAt_complexWeierstrassImplicitYChart_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hy : complexWeierstrassEquationY W P.1 ≠ 0) (x : ℂ)
    (hx : x ∈ (complexWeierstrassImplicitYChart W P hy).target) :
    ContDiffAt ℂ ω (fun x =>
      (((complexWeierstrassImplicitYChart W P hy).symm x :
        ComplexWeierstrassAffine W) : ℂ × ℂ)) x := by
  let e := complexWeierstrassImplicitYAmbientHomeomorph W P.1 hy
  let c := complexWeierstrassImplicitYChart W P hy
  have hamb : ContDiffAt ℂ ω e.symm (0, x) :=
    contDiffAt_complexWeierstrassImplicitYAmbientHomeomorph_symm W P.1 hy _ hx
  have hcomp : ContDiffAt ℂ ω (fun x => e.symm (0, x)) x :=
    hamb.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have ht : c.target ∈ 𝓝 x := c.open_target.mem_nhds hx
  have heq : (fun x => ((c.symm x : ComplexWeierstrassAffine W) : ℂ × ℂ)) =ᶠ[𝓝 x]
      (fun x => e.symm (0, x)) := by
    filter_upwards [ht] with x hx
    exact complexWeierstrassImplicitYChartInv_coe_of_mem W P.1 P.2 hy x hx
  exact hcomp.congr_of_eventuallyEq heq

/-- The inverse of the finite `x`-coordinate chart is complex analytic at its
center, for the ambient affine coordinates.
@isnad1 id=contdiff.1h2v.s8.125b993f26de from=translated src=- shape=7605fcc0 vocab=489c7f1d
-/
theorem contDiffAt_complexWeierstrassImplicitYChart_symm_coe
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hy : complexWeierstrassEquationY W P.1 ≠ 0) :
    ContDiffAt ℂ ω (fun x =>
      (((complexWeierstrassImplicitYChart W P hy).symm x :
        ComplexWeierstrassAffine W) : ℂ × ℂ)) P.1.1 := by
  let c := complexWeierstrassImplicitYChart W P hy
  have hPc : P ∈ c.source := complexWeierstrassImplicitYChart_mem_source W P hy
  have hPt : P.1.1 ∈ c.target := c.map_source hPc
  have ht : c.target ∈ 𝓝 P.1.1 := c.open_target.mem_nhds hPt
  have heq : (fun x => ((c.symm x : ComplexWeierstrassAffine W) : ℂ × ℂ)) =ᶠ[𝓝 P.1.1]
      (fun x => (x, complexWeierstrassImplicitY W P.1 hy x)) := by
    filter_upwards [ht] with x hx
    exact complexWeierstrassImplicitYChart_symm_coe_of_mem W P hy x hx
  apply (contDiffAt_id.prodMk
    (contDiffAt_complexWeierstrassImplicitY W P.1 hy)).congr_of_eventuallyEq
  simpa [c] using heq

/-- The inverse-function-theorem neighborhood for the swapped equation.  Its
forward map is `(y, x) ↦ (F(x,y), y)`. -/
def complexWeierstrassImplicitXAmbientHomeomorph
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  let e :=
    (((contDiff_complexWeierstrassEquationSwap W).contDiffAt.hasStrictFDerivAt
      (by simp)).implicitFunctionDataOfProdDomain
        (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
          (p.2, p.1) hx)).toOpenPartialHomeomorph
  e.restrOpen {q | complexWeierstrassEquationX W (q.2, q.1) ≠ 0} (by
    apply isOpen_ne.preimage
    unfold complexWeierstrassEquationX
    fun_prop)

/--
@isnad1 id=mem.1h2v.s7.2974e7e997e0 from=translated src=- shape=c1a182ce vocab=e4b91666
-/
theorem complexWeierstrassImplicitXAmbientHomeomorph_mem_source
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    (p.2, p.1) ∈
      (complexWeierstrassImplicitXAmbientHomeomorph W p hx).source := by
  rw [complexWeierstrassImplicitXAmbientHomeomorph,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _, hx⟩

/--
@isnad1 id=eq.1h3v.s6.d09798743c8d from=translated src=- shape=64a90479 vocab=f6c63de2
-/
@[simp] theorem complexWeierstrassImplicitXAmbientHomeomorph_apply
    (W : WeierstrassCurve ℂ) (p q : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    complexWeierstrassImplicitXAmbientHomeomorph W p hx q =
      (complexWeierstrassEquationSwap W q, q.1) :=
  rfl

/-- The inverse of the swapped ambient implicit-function neighborhood is
complex analytic everywhere on its target.
@isnad1 id=contdiff.2h3v.s8.8bfba1d927f3 from=translated src=- shape=50bcdd80 vocab=e4867253
-/
theorem contDiffAt_complexWeierstrassImplicitXAmbientHomeomorph_symm
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) (z : ℂ × ℂ)
    (hz : z ∈ (complexWeierstrassImplicitXAmbientHomeomorph W p hx).target) :
    ContDiffAt ℂ ω
      (complexWeierstrassImplicitXAmbientHomeomorph W p hx).symm z := by
  let e := complexWeierstrassImplicitXAmbientHomeomorph W p hx
  let q := e.symm z
  have hqsource : q ∈ e.source := e.map_target hz
  have hqx : complexWeierstrassEquationX W (q.2, q.1) ≠ 0 := by
    exact hqsource.2
  let φ :=
    ((contDiff_complexWeierstrassEquationSwap W).contDiffAt.hasStrictFDerivAt
      (by simp)).implicitFunctionDataOfProdDomain
        (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W q hqx)
  apply e.contDiffAt_symm hz
  · change HasFDerivAt
      (fun q : ℂ × ℂ => (complexWeierstrassEquationSwap W q, q.1)) _ q
    have hφ := φ.hasStrictFDerivAt.hasFDerivAt
    change HasFDerivAt
      (fun q : ℂ × ℂ => (complexWeierstrassEquationSwap W q, q.1)) _ q at hφ
    exact hφ
  · change ContDiffAt ℂ ω
      (fun q : ℂ × ℂ => (complexWeierstrassEquationSwap W q, q.1)) q
    exact (contDiff_complexWeierstrassEquationSwap W).contDiffAt.prodMk contDiffAt_fst

private def complexWeierstrassImplicitXChartInv
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hx : complexWeierstrassEquationX W p ≠ 0) (y : ℂ) :
    ComplexWeierstrassAffine W := by
  classical
  let e := complexWeierstrassImplicitXAmbientHomeomorph W p hx
  exact if hy : (0, y) ∈ e.target then
    ⟨((e.symm (0, y)).2, (e.symm (0, y)).1),
      (complexWeierstrassEquation_eq_zero_iff W _).1 (by
        change complexWeierstrassEquationSwap W (e.symm (0, y)) = 0
        have hright := e.right_inv hy
        exact congrArg Prod.fst hright)⟩
  else ⟨p, hp⟩

private theorem complexWeierstrassImplicitXChartInv_coe_of_mem
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hx : complexWeierstrassEquationX W p ≠ 0) (y : ℂ)
    (hy : (0, y) ∈
      (complexWeierstrassImplicitXAmbientHomeomorph W p hx).target) :
    (complexWeierstrassImplicitXChartInv W p hp hx y : ℂ × ℂ) =
      (((complexWeierstrassImplicitXAmbientHomeomorph W p hx).symm (0, y)).2,
       ((complexWeierstrassImplicitXAmbientHomeomorph W p hx).symm (0, y)).1) := by
  classical
  simp [complexWeierstrassImplicitXChartInv, hy]

/-- The zero-fiber restriction in the other coordinate direction.  This is an
open partial homeomorphism from the affine equation locus to `ℂ` whose forward
map is the `y`-coordinate. -/
def complexWeierstrassImplicitXChart
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hx : complexWeierstrassEquationX W P.1 ≠ 0) :
    OpenPartialHomeomorph (ComplexWeierstrassAffine W) ℂ := by
  let e := complexWeierstrassImplicitXAmbientHomeomorph W P.1 hx
  let inv := complexWeierstrassImplicitXChartInv W P.1 P.2 hx
  refine
    { toFun := fun Q => Q.1.2
      invFun := inv
      source := {Q | (Q.1.2, Q.1.1) ∈ e.source}
      target := {y | (0, y) ∈ e.target}
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := ?_
      open_target := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro Q hQ
    change (0, Q.1.2) ∈ e.target
    have hm := e.map_source hQ
    have hzero : complexWeierstrassEquationSwap W (Q.1.2, Q.1.1) = 0 :=
      (complexWeierstrassEquation_eq_zero_iff W Q.1).2 Q.2
    simpa [e, hzero] using hm
  · intro y hy
    change ((inv y).1.2, (inv y).1.1) ∈ e.source
    rw [complexWeierstrassImplicitXChartInv_coe_of_mem W P.1 P.2 hx y hy]
    simpa using e.map_target hy
  · intro Q hQ
    apply Subtype.ext
    change (inv Q.1.2).1 = Q.1
    have ht : (0, Q.1.2) ∈ e.target := by
      have hm := e.map_source hQ
      have hzero : complexWeierstrassEquationSwap W (Q.1.2, Q.1.1) = 0 :=
        (complexWeierstrassEquation_eq_zero_iff W Q.1).2 Q.2
      simpa [e, hzero] using hm
    rw [complexWeierstrassImplicitXChartInv_coe_of_mem W P.1 P.2 hx _ ht]
    have hleft := e.left_inv hQ
    have hzero : complexWeierstrassEquationSwap W (Q.1.2, Q.1.1) = 0 :=
      (complexWeierstrassEquation_eq_zero_iff W Q.1).2 Q.2
    have hpair : e.symm (0, Q.1.2) = (Q.1.2, Q.1.1) := by
      simpa [e, hzero] using hleft
    rw [hpair]
  · intro y hy
    rw [complexWeierstrassImplicitXChartInv_coe_of_mem W P.1 P.2 hx y hy]
    have hright := e.right_inv hy
    exact congrArg Prod.snd hright
  · exact continuous_subtype_val.snd.continuousOn
  · rw [continuousOn_iff_continuous_domRestrict]
    let inc : {y : ℂ | (0, y) ∈ e.target} → ℂ × ℂ := fun y => (0, y.1)
    have hinc : Continuous inc := continuous_const.prodMk continuous_subtype_val
    have hamb : Continuous (fun y => e.symm (inc y)) :=
      e.continuousOn_symm.comp_continuous hinc (fun y => y.2)
    have hswap : Continuous (fun y => ((e.symm (inc y)).2, (e.symm (inc y)).1)) :=
      hamb.snd.prodMk hamb.fst
    let g : {y : ℂ | (0, y) ∈ e.target} → ComplexWeierstrassAffine W :=
      fun y => ⟨((e.symm (inc y)).2, (e.symm (inc y)).1),
        (complexWeierstrassEquation_eq_zero_iff W _).1 (by
          change complexWeierstrassEquationSwap W (e.symm (inc y)) = 0
          have hright := e.right_inv y.2
          exact congrArg Prod.fst hright)⟩
    have hg : Continuous g := Continuous.subtype_mk hswap _
    have heq : {y : ℂ | (0, y) ∈ e.target}.domRestrict inv = g := by
      funext y
      apply Subtype.ext
      exact complexWeierstrassImplicitXChartInv_coe_of_mem
        W P.1 P.2 hx y.1 y.2
    rw [heq]
    exact hg
  · exact e.open_source.preimage
      (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst)
  · exact e.open_target.preimage (continuous_const.prodMk continuous_id)

/--
@isnad1 id=eq.1h3v.s7.e524bb49978c from=translated src=- shape=d4c5a5de vocab=a30deeeb
-/
@[simp] theorem complexWeierstrassImplicitXChart_apply
    (W : WeierstrassCurve ℂ) (P Q : ComplexWeierstrassAffine W)
    (hx : complexWeierstrassEquationX W P.1 ≠ 0) :
    complexWeierstrassImplicitXChart W P hx Q = Q.1.2 :=
  rfl

/--
@isnad1 id=mem.1h2v.s7.cbf2dffebcac from=translated src=- shape=386508ee vocab=0735f4e0
-/
theorem complexWeierstrassImplicitXChart_mem_source
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hx : complexWeierstrassEquationX W P.1 ≠ 0) :
    P ∈ (complexWeierstrassImplicitXChart W P hx).source :=
  complexWeierstrassImplicitXAmbientHomeomorph_mem_source W P.1 hx

/-- On its target, the inverse topological chart is exactly the graph of the
implicit analytic `x`-function, written back in `(x,y)` order.
@isnad1 id=eq.2h3v.s8.be434a10ed36 from=translated src=- shape=ea221d79 vocab=6bc56412
-/
theorem complexWeierstrassImplicitXChart_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hx : complexWeierstrassEquationX W P.1 ≠ 0) (y : ℂ)
    (hy : y ∈ (complexWeierstrassImplicitXChart W P hx).target) :
    ((complexWeierstrassImplicitXChart W P hx).symm y :
        ComplexWeierstrassAffine W) =
      (complexWeierstrassImplicitX W P.1 hx y, y) := by
  let e := complexWeierstrassImplicitXAmbientHomeomorph W P.1 hx
  change (complexWeierstrassImplicitXChartInv W P.1 P.2 hx y : ℂ × ℂ) = _
  rw [complexWeierstrassImplicitXChartInv_coe_of_mem W P.1 P.2 hx y hy]
  have hfirst : (e.symm (0, y)).2 = complexWeierstrassImplicitX W P.1 hx y := by
    have hzero : complexWeierstrassEquationSwap W (P.1.2, P.1.1) = 0 :=
      (complexWeierstrassEquation_eq_zero_iff W P.1).2 P.2
    change (e.symm (0, y)).2 =
      (e.symm (complexWeierstrassEquationSwap W (P.1.2, P.1.1), y)).2
    rw [hzero]
  have hright := e.right_inv hy
  have hsecond : (e.symm (0, y)).1 = y := congrArg Prod.snd hright
  exact Prod.ext hfirst hsecond

/-- The inverse of the finite `y`-coordinate chart is complex analytic at
every point of its target, in ambient affine coordinates.
@isnad1 id=contdiff.2h3v.s8.4ecb4cdff2b3 from=translated src=- shape=fbe62eb1 vocab=8a412ea0
-/
theorem contDiffAt_complexWeierstrassImplicitXChart_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hx : complexWeierstrassEquationX W P.1 ≠ 0) (y : ℂ)
    (hy : y ∈ (complexWeierstrassImplicitXChart W P hx).target) :
    ContDiffAt ℂ ω (fun y =>
      (((complexWeierstrassImplicitXChart W P hx).symm y :
        ComplexWeierstrassAffine W) : ℂ × ℂ)) y := by
  let e := complexWeierstrassImplicitXAmbientHomeomorph W P.1 hx
  let c := complexWeierstrassImplicitXChart W P hx
  have hamb : ContDiffAt ℂ ω e.symm (0, y) :=
    contDiffAt_complexWeierstrassImplicitXAmbientHomeomorph_symm W P.1 hx _ hy
  have hcomp : ContDiffAt ℂ ω
      (fun y => ((e.symm (0, y)).2, (e.symm (0, y)).1)) y :=
    (hamb.comp y (contDiffAt_const.prodMk contDiffAt_id)).snd.prodMk
      (hamb.comp y (contDiffAt_const.prodMk contDiffAt_id)).fst
  have ht : c.target ∈ 𝓝 y := c.open_target.mem_nhds hy
  have heq : (fun y => ((c.symm y : ComplexWeierstrassAffine W) : ℂ × ℂ)) =ᶠ[𝓝 y]
      (fun y => ((e.symm (0, y)).2, (e.symm (0, y)).1)) := by
    filter_upwards [ht] with y hy
    exact complexWeierstrassImplicitXChartInv_coe_of_mem W P.1 P.2 hx y hy
  exact hcomp.congr_of_eventuallyEq heq

/-- The inverse of the finite `y`-coordinate chart is complex analytic at its
center, for the ambient affine coordinates.
@isnad1 id=contdiff.1h2v.s8.49c7f92557c7 from=translated src=- shape=3f748ddf vocab=8223e06c
-/
theorem contDiffAt_complexWeierstrassImplicitXChart_symm_coe
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hx : complexWeierstrassEquationX W P.1 ≠ 0) :
    ContDiffAt ℂ ω (fun y =>
      (((complexWeierstrassImplicitXChart W P hx).symm y :
        ComplexWeierstrassAffine W) : ℂ × ℂ)) P.1.2 := by
  let c := complexWeierstrassImplicitXChart W P hx
  have hPc : P ∈ c.source := complexWeierstrassImplicitXChart_mem_source W P hx
  have hPt : P.1.2 ∈ c.target := c.map_source hPc
  have ht : c.target ∈ 𝓝 P.1.2 := c.open_target.mem_nhds hPt
  have heq : (fun y => ((c.symm y : ComplexWeierstrassAffine W) : ℂ × ℂ)) =ᶠ[𝓝 P.1.2]
      (fun y => (complexWeierstrassImplicitX W P.1 hx y, y)) := by
    filter_upwards [ht] with y hy
    exact complexWeierstrassImplicitXChart_symm_coe_of_mem W P hx y hy
  apply ((contDiffAt_complexWeierstrassImplicitX W P.1 hx).prodMk
    contDiffAt_id).congr_of_eventuallyEq
  simpa [c] using heq

/-- At every finite point of a nonsingular complex Weierstrass equation, one
of the two analytic implicit-coordinate constructions applies.
@isnad1 id=or.0h2v.s6.284f867880b2 from=translated src=- shape=78717387 vocab=1c0559ff
-/
theorem complexWeierstrassAffine_derivative_ne_zero
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    complexWeierstrassEquationX W P.1 ≠ 0 ∨
      complexWeierstrassEquationY W P.1 ≠ 0 := by
  have hns : W.toAffine.Nonsingular P.1.1 P.1.2 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp P.2
  simpa [complexWeierstrassEquationX_eq_polynomialX,
    complexWeierstrassEquationY_eq_polynomialY] using hns.2

/-- Every finite point is contained in the source of one of the two explicit
open partial homeomorphisms to `ℂ`.  Their forward maps are the corresponding
coordinate projections, so their topology is the existing subtype topology.
This is the topological chart layer; holomorphic transition packaging is still
separate.
@isnad1 id=or.0h2v.s9.840ec1c6e4bd from=translated src=- shape=b749726c vocab=056ad89a
-/
theorem complexWeierstrassAffine_exists_openPartialHomeomorph
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    (∃ hy : complexWeierstrassEquationY W P.1 ≠ 0,
      P ∈ (complexWeierstrassImplicitYChart W P hy).source ∧
      ∀ Q, complexWeierstrassImplicitYChart W P hy Q = Q.1.1) ∨
    (∃ hx : complexWeierstrassEquationX W P.1 ≠ 0,
      P ∈ (complexWeierstrassImplicitXChart W P hx).source ∧
      ∀ Q, complexWeierstrassImplicitXChart W P hx Q = Q.1.2) := by
  rcases complexWeierstrassAffine_derivative_ne_zero W P with hx | hy
  · exact Or.inr ⟨hx, complexWeierstrassImplicitXChart_mem_source W P hx,
      fun Q => complexWeierstrassImplicitXChart_apply W P Q hx⟩
  · exact Or.inl ⟨hy, complexWeierstrassImplicitYChart_mem_source W P hy,
      fun Q => complexWeierstrassImplicitYChart_apply W P Q hy⟩

/-- Every finite curve point admits an honest complex-analytic graph germ in
one of the two coordinate directions.  This packages the analytic output next
to the open topological charts, without pretending that a complex atlas has
already been assembled.
@isnad1 id=or.0h2v.s9.160ad970694a from=translated src=- shape=9a729e19 vocab=f4922c94
-/
theorem complexWeierstrassAffine_exists_analytic_graph_germ
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    (∃ hy : complexWeierstrassEquationY W P.1 ≠ 0,
        ContDiffAt ℂ ω (complexWeierstrassImplicitY W P.1 hy) P.1.1 ∧
        complexWeierstrassImplicitY W P.1 hy P.1.1 = P.1.2 ∧
        ∀ᶠ x in 𝓝 P.1.1,
          W.toAffine.Equation x
            (complexWeierstrassImplicitY W P.1 hy x)) ∨
      (∃ hx : complexWeierstrassEquationX W P.1 ≠ 0,
        ContDiffAt ℂ ω (complexWeierstrassImplicitX W P.1 hx) P.1.2 ∧
        complexWeierstrassImplicitX W P.1 hx P.1.2 = P.1.1 ∧
        ∀ᶠ y in 𝓝 P.1.2,
          W.toAffine.Equation
            (complexWeierstrassImplicitX W P.1 hx y) y) := by
  rcases complexWeierstrassAffine_derivative_ne_zero W P with hx | hy
  · exact Or.inr ⟨hx, contDiffAt_complexWeierstrassImplicitX W P.1 hx,
      complexWeierstrassImplicitX_apply_self W P.1 hx,
      eventually_complexWeierstrassImplicitX_equation W P.1 P.2 hx⟩
  · exact Or.inl ⟨hy, contDiffAt_complexWeierstrassImplicitY W P.1 hy,
      complexWeierstrassImplicitY_apply_self W P.1 hy,
      eventually_complexWeierstrassImplicitY_equation W P.1 P.2 hy⟩

end Heights
