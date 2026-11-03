import Tengoku.HodgeStructuresLean4.HodgePilot.Analytic
import Tengoku.Seed.RingTheory.Extension.Presentation.Submersive
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Analytic.Polynomial
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Analysis.Calculus.FDeriv.Prod
import Tengoku.Seed.Analysis.Calculus.FDeriv.Mul
import Tengoku.Seed.Data.Matrix.Block
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Topology.Algebra.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Jacobian bridge: Fréchet calculus of polynomial maps at ℂ-points

Mathlib's smoothness theory for algebras is *algebraic*: a (pre)submersive
presentation `P` of a ℂ-algebra `S` (`Algebra.PreSubmersivePresentation`)
carries a Jacobian `P.jacobian : S`, the determinant of the matrix of
`MvPolynomial.pderiv`-partial derivatives of the relations.  Mathlib's inverse
function theorem is *analytic*: it consumes a `HasStrictFDerivAt` hypothesis
whose derivative is a continuous linear equivalence.  Nothing in Mathlib
connects the two: `pderiv` does not appear in the Fréchet-calculus library.
This file is that bridge.

* `polyGrad`, `hasFDerivAt_eval`, `hasStrictFDerivAt_eval` — **the bridge
  lemma**: evaluation of a multivariate polynomial, as a map `ℂ^ι → ℂ`, is
  (strictly) Fréchet-differentiable with derivative the `pderiv`-gradient.
* `hasStrictFDerivAt_eval_pi`, `analyticAt_eval_pi` — vector-valued versions
  for finite families of polynomials, `ℂ^ι → ℂ^σ`.
* `ambient` — evaluation of the generators of a presented ℂ-algebra `S` at a
  ℂ-point `φ : CPoints S`, the coordinates of `φ` in the ambient affine space
  `ℂ^ι`; `isEmbedding_ambient` (a topological embedding, by presentation
  independence from `HodgePilot.Analytic`) and `ambient_algebraMap`
  (evaluation of polynomials through a ℂ-point).
* `extendedMap` — for a presubmersive presentation `P` with variables `ι` and
  relations `σ`, the polynomial map `ℂ^ι → ℂ^σ × ℂ^κ` whose components are the
  relations of `P` and the coordinates complementary to `P.map`
  (`κ = Kappa P`); `analyticAt_extendedMap`, `hasStrictFDerivAt_extendedMap`
  (explicit derivative `extendedDeriv`).
* `apply_jacobian` — the value of the algebraic Jacobian at a ℂ-point is the
  determinant of the evaluated Jacobi matrix.
* `bijective_extendedDeriv`, `extendedDerivEquiv`,
  `hasStrictFDerivAt_extendedMap_equiv` — **the key transfer**: if the
  algebraic Jacobian of `P` is invertible at a ℂ-point `φ` (in particular, by
  `isUnit_apply_jacobian`, at *every* ℂ-point when `P` is submersive), the
  strict Fréchet derivative of `extendedMap P` at the ambient coordinates of
  `φ` is a continuous linear equivalence `ℂ^ι ≃L[ℂ] ℂ^σ × ℂ^κ` — exactly the
  input shape of Mathlib's inverse function theorem.
* `range_ambient` — the ambient coordinates of the ℂ-points are precisely the
  common zero locus of the relations.

This file is multivariate-polynomial calculus and a Jacobian-invertibility
transfer only.  No manifold, no chart, no analytic-space structure, and no
statement about smooth varieties is made or claimed here; the inverse function
theorem itself is not yet invoked.
-/

open MvPolynomial Topology Algebra Matrix HodgePilot.Analytic

noncomputable section

universe u v t

namespace HodgePilot.JacobianBridge

/-! ## The pderiv → fderiv bridge -/

section Scalar

variable {ι : Type v} [Fintype ι]

/-- The gradient of a multivariate polynomial at `v`, as a continuous linear
map `(ι → ℂ) →L[ℂ] ℂ`, with coefficients the partial derivatives `pderiv i p`
evaluated at `v`.-/
def polyGrad (p : MvPolynomial ι ℂ) (v : ι → ℂ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, eval v (pderiv i p) • ContinuousLinearMap.proj i

/--
@isnad1 id=eq.0h4v.s8.74082cea02ee from=translated src=- shape=4969d156 vocab=62619dd9
-/
@[simp]
lemma polyGrad_apply (p : MvPolynomial ι ℂ) (v w : ι → ℂ) :
    polyGrad p v w = ∑ i, eval v (pderiv i p) * w i := by
  simp [polyGrad]

/--
@isnad1 id=eq.0h3v.s8.051c3317db8c from=translated src=- shape=7306af49 vocab=96f83522
-/
lemma polyGrad_C (a : ℂ) (v : ι → ℂ) : polyGrad (C a) v = 0 := by
  ext w
  simp

/--
@isnad1 id=eq.0h4v.s8.41c1b66c6941 from=translated src=- shape=46bd294e vocab=6f762c72
-/
lemma polyGrad_add (p q : MvPolynomial ι ℂ) (v : ι → ℂ) :
    polyGrad (p + q) v = polyGrad p v + polyGrad q v := by
  ext w
  simp [Finset.sum_add_distrib, add_mul]

/--
@isnad1 id=eq.0h4v.s10.3a417676247e from=translated src=- shape=da2fc9d1 vocab=df06c685
-/
lemma polyGrad_mul_X [DecidableEq ι] (p : MvPolynomial ι ℂ) (j : ι) (v : ι → ℂ) :
    polyGrad (p * X j) v =
      eval v p • ContinuousLinearMap.proj j + v j • polyGrad p v := by
  ext w
  have hterm : ∀ i : ι, eval v (pderiv i (p * X j)) * w i
      = (if i = j then eval v p * w i else 0) + v j * (eval v (pderiv i p) * w i) := by
    intro i
    rcases eq_or_ne i j with rfl | hij
    · rw [pderiv_mul, pderiv_X_self]
      simp only [map_add, eval_mul, eval_X, mul_one, ite_true]
      ring
    · rw [pderiv_mul, pderiv_X_of_ne (Ne.symm hij)]
      simp only [eval_mul, eval_X, mul_zero, add_zero, ite_eq_right hij]
      ring
  simp only [polyGrad_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j (fun i => eval v p * w i), ← Finset.mul_sum]
  simp

/-- **The bridge**: polynomial evaluation `(ι → ℂ) → ℂ` has Fréchet derivative
given by the `pderiv` gradient.
@isnad1 id=hasfderi.0h3v.s7.e2937a5aff47 from=translated src=- shape=1b9b7246 vocab=8d0c6607
-/
theorem hasFDerivAt_eval (p : MvPolynomial ι ℂ) (v : ι → ℂ) :
    HasFDerivAt (fun w : ι → ℂ => eval w p) (polyGrad p v) v := by
  classical
  apply p.induction_on (fun a => ?_) (fun p q hp hq => ?_) fun p j hp => ?_
  · rw [polyGrad_C]
    simp only [eval_C]
    exact hasFDerivAt_const a v
  · rw [polyGrad_add]
    simp only [map_add]
    exact hp.add hq
  · have hfun : (fun w : ι → ℂ => eval w (p * X j)) =
        fun w : ι → ℂ => eval w p * w j := by
      funext w
      simp
    have hXj : HasFDerivAt (fun w : ι → ℂ => w j)
        (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ) v :=
      (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt
    rw [polyGrad_mul_X, hfun]
    exact hp.mul hXj

/-- Polynomial evaluation `(ι → ℂ) → ℂ` is analytic at every point.
@isnad1 id=analytic.0h3v.s7.6288c6271dbd from=translated src=- shape=f742e885 vocab=af5484b7
-/
theorem analyticAt_eval (p : MvPolynomial ι ℂ) (v : ι → ℂ) :
    AnalyticAt ℂ (fun w : ι → ℂ => eval w p) v :=
  AnalyticOnNhd.eval_mvPolynomial p v (Set.mem_univ v)

/-- Strict-derivative form (input shape for the inverse function theorem):
via analyticity of polynomial maps, the derivative is strict.
@isnad1 id=hasstric.0h3v.s7.c2bcfb7efaa8 from=translated src=- shape=1b9b7246 vocab=97ee60d3
-/
theorem hasStrictFDerivAt_eval (p : MvPolynomial ι ℂ) (v : ι → ℂ) :
    HasStrictFDerivAt (fun w : ι → ℂ => eval w p) (polyGrad p v) v := by
  have ha : AnalyticAt ℂ (fun w : ι → ℂ => eval w p) v := analyticAt_eval p v
  have h := ha.hasStrictFDerivAt
  rwa [(hasFDerivAt_eval p v).fderiv] at h

variable {σ : Type t} [Fintype σ]

omit [Fintype σ] in
/-- Vector-valued bridge: a finite family of polynomials, as a map
`ℂ^ι → ℂ^σ`, has strict Fréchet derivative the matrix of `pderiv`-gradients.
@isnad1 id=hasstric.0h4v.s8.a0932c9ee7a2 from=translated src=- shape=8e4c6f04 vocab=79374a0c
-/
theorem hasStrictFDerivAt_eval_pi (p : σ → MvPolynomial ι ℂ) (v : ι → ℂ) :
    HasStrictFDerivAt (fun w (j : σ) => eval w (p j))
      (ContinuousLinearMap.pi fun j => polyGrad (p j) v) v :=
  hasStrictFDerivAt_pi.mpr fun j => hasStrictFDerivAt_eval (p j) v

/-- A finite family of polynomials, as a map `ℂ^ι → ℂ^σ`, is analytic.
@isnad1 id=analytic.0h4v.s7.c7c9a0c29e81 from=translated src=- shape=39388f4d vocab=af5484b7
-/
theorem analyticAt_eval_pi (p : σ → MvPolynomial ι ℂ) (v : ι → ℂ) :
    AnalyticAt ℂ (fun w (j : σ) => eval w (p j)) v :=
  AnalyticAt.pi fun j => analyticAt_eval (p j) v

end Scalar

/-! ## ℂ-points in ambient coordinates -/

section Ambient

variable {S : Type u} [CommRing S] [Algebra ℂ S] {ι : Type v}

/-- The ambient coordinates of a ℂ-point: evaluation of `φ : CPoints S` at the
generators of a generating family `G`, landing in the affine space `ℂ^ι`.-/
def ambient (G : Generators ℂ S ι) (φ : CPoints S) : ι → ℂ :=
  fun i => φ (G.val i)

/--
@isnad1 id=eq.0h5v.s6.507f93c433e9 from=translated src=- shape=21220465 vocab=319719be
-/
@[simp]
lemma ambient_apply (G : Generators ℂ S ι) (φ : CPoints S) (i : ι) :
    ambient G φ i = φ (G.val i) := rfl

/-- Evaluating a ℂ-point on the image of a polynomial `q` is evaluating `q`
at the ambient coordinates.
@isnad1 id=eq.0h5v.s8.286f6e215b85 from=translated src=- shape=477f49aa vocab=8dde2812
-/
lemma ambient_algebraMap (G : Generators ℂ S ι) (φ : CPoints S)
    (q : MvPolynomial ι ℂ) :
    φ (algebraMap G.Ring S q) = eval (ambient G φ) q := by
  rw [G.algebraMap_apply]
  exact comp_aeval_apply G.val φ q

/-- The ambient-coordinate map of any generating family is a topological
embedding (presentation independence, `HodgePilot.Analytic.isEmbedding_evalGen`).
@isnad1 id=isembedd.0h3v.s5.137a0ab26130 from=translated src=- shape=6fc0e0f7 vocab=ec627b4a
-/
theorem isEmbedding_ambient (G : Generators ℂ S ι) : IsEmbedding (ambient G) := by
  have hg : Algebra.adjoin ℂ (Set.range G.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr G.aeval_val_surjective
  exact isEmbedding_evalGen G.val hg

end Ambient

/-! ## The extended map of a presubmersive presentation and its derivative -/

section Presentation

variable {S : Type u} [CommRing S] [Algebra ℂ S] {ι : Type v} {σ : Type t}
variable [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable (P : PreSubmersivePresentation ℂ S ι σ)

/-- The complementary variables of a presubmersive presentation: the
coordinates not selected by `P.map`.  These are the future chart coordinates.-/
abbrev Kappa := {i : ι // i ∉ Set.range P.map}

/-- Projection onto the complementary coordinates, as a continuous linear map.-/
def kappaProj : (ι → ℂ) →L[ℂ] (Kappa P → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj k.val

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h6v.s8.285ab706ec6e from=translated src=- shape=577643dd vocab=e08ace11
-/
@[simp]
lemma kappaProj_apply (z : ι → ℂ) (k : Kappa P) : kappaProj P z k = z k.val := rfl

/-- The extended map of a presubmersive presentation: the polynomial map
`ℂ^ι → ℂ^σ × ℂ^κ` whose first component evaluates the relations and whose
second component records the complementary coordinates.  At an invertible
Jacobian this is a local analytic isomorphism (the future slice chart machine).-/
def extendedMap : (ι → ℂ) → (σ → ℂ) × (Kappa P → ℂ) :=
  fun z => (fun j => eval z (P.relation j), fun k => z k.val)

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h4v.s7.cc282b13af76 from=translated src=- shape=58b5176f vocab=120a556b
-/
lemma extendedMap_def :
    extendedMap P = fun z => (fun j => eval z (P.relation j), fun k => z k.val) :=
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h5v.s7.bacf611e239c from=translated src=- shape=484b8015 vocab=120a556b
-/
@[simp]
lemma extendedMap_apply (z : ι → ℂ) :
    extendedMap P z = (fun j => eval z (P.relation j), fun k => z k.val) := rfl

omit [DecidableEq σ] in
/-- The extended map is analytic at every point of `ℂ^ι`.
@isnad1 id=analytic.0h5v.s8.d3e565be4d09 from=translated src=- shape=714ccb82 vocab=2d19aab2
-/
theorem analyticAt_extendedMap (z : ι → ℂ) : AnalyticAt ℂ (extendedMap P) z := by
  rw [extendedMap_def]
  exact (AnalyticAt.pi fun j => analyticAt_eval (P.relation j) z).prod
    (AnalyticAt.pi fun k =>
      (ContinuousLinearMap.proj k.val : (ι → ℂ) →L[ℂ] ℂ).analyticAt z)

/-- The derivative of the extended map at `v`: the `pderiv`-gradients of the
relations, paired with the projection onto the complementary coordinates.-/
def extendedDeriv (v : ι → ℂ) : (ι → ℂ) →L[ℂ] (σ → ℂ) × (Kappa P → ℂ) :=
  (ContinuousLinearMap.pi fun j => polyGrad (P.relation j) v).prod (kappaProj P)

omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h6v.s10.782ec1baf0cf from=translated src=- shape=f7808e90 vocab=e4db0363
-/
@[simp]
lemma extendedDeriv_apply (v u : ι → ℂ) :
    extendedDeriv P v u = (fun j => polyGrad (P.relation j) v u, kappaProj P u) :=
  rfl

omit [DecidableEq σ] in
/-- The extended map has strict Fréchet derivative `extendedDeriv` at every
point of `ℂ^ι`.
@isnad1 id=hasstric.0h5v.s8.f46fa20f868b from=translated src=- shape=49c2ff47 vocab=5b51b0c6
-/
theorem hasStrictFDerivAt_extendedMap (v : ι → ℂ) :
    HasStrictFDerivAt (extendedMap P) (extendedDeriv P v) v := by
  rw [extendedMap_def]
  exact (hasStrictFDerivAt_pi.mpr fun j =>
    hasStrictFDerivAt_eval (P.relation j) v).prodMk
    (hasStrictFDerivAt_pi.mpr fun k => hasStrictFDerivAt_apply k.val v)

/-! ## The algebraic Jacobian at a ℂ-point -/

/-- The Jacobi matrix of the presentation, `eval`-ed at a point `v ∈ ℂ^ι`:
rows index the selected variables `P.map i`, columns index the relations,
matching `Algebra.PreSubmersivePresentation.jacobiMatrix`.-/
def evalJacobiMatrix (v : ι → ℂ) : Matrix σ σ ℂ :=
  P.jacobiMatrix.map (eval v)

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=eq.0h7v.s8.59b4353d5528 from=translated src=- shape=6a7edf52 vocab=a37f5813
-/
@[simp]
lemma evalJacobiMatrix_apply (v : ι → ℂ) (i j : σ) :
    evalJacobiMatrix P v i j = eval v (pderiv (P.map i) (P.relation j)) := by
  simp [evalJacobiMatrix, P.jacobiMatrix_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- The value of the algebraic Jacobian of `P` at a ℂ-point `φ` is the
determinant of the Jacobi matrix evaluated at the ambient coordinates of `φ`.
@isnad1 id=eq.0h5v.s6.562ec1c4e588 from=translated src=- shape=1da6d11a vocab=d2318159
-/
theorem apply_jacobian (φ : CPoints S) :
    φ P.jacobian = (evalJacobiMatrix P (ambient P.toGenerators φ)).det := by
  rw [P.jacobian_eq_jacobiMatrix_det, ambient_algebraMap, RingHom.map_det]
  rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] in
/-- At every ℂ-point of a *submersive* presentation the algebraic Jacobian is
invertible: units map to units.
@isnad1 id=isunit.0h5v.s6.3ba705682cda from=translated src=- shape=7036109f vocab=36ce9c88
-/
theorem isUnit_apply_jacobian (Q : SubmersivePresentation ℂ S ι σ)
    (φ : CPoints S) : IsUnit (φ Q.jacobian) :=
  Q.jacobian_isUnit.map φ

/-! ## Invertibility transfer -/

/-- The variable split of a presubmersive presentation: selected variables
(one per relation) plus complementary variables exhaust all variables.-/
def sumEquiv : σ ⊕ Kappa P ≃ ι :=
  Equiv.ofBijective (Sum.elim P.map Subtype.val) <| by
    constructor
    · rintro (j | k) (j' | k') h
      · exact congrArg Sum.inl (P.map_inj h)
      · exact absurd ⟨j, h⟩ k'.prop
      · exact absurd ⟨j', h.symm⟩ k.prop
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro i
      by_cases hi : i ∈ Set.range P.map
      · obtain ⟨j, rfl⟩ := hi
        exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

omit [Fintype ι] [DecidableEq σ] in
/--
@isnad1 id=eq.0h5v.s7.fb65ce85c999 from=translated src=- shape=3a53d1f0 vocab=cc0511e6
-/
@[simp]
lemma sumEquiv_inl (j : σ) : sumEquiv P (Sum.inl j) = P.map j := rfl

omit [Fintype ι] [DecidableEq σ] in
/--
@isnad1 id=eq.0h5v.s7.a5ae6cea5283 from=translated src=- shape=127b1701 vocab=d47709d7
-/
@[simp]
lemma sumEquiv_inr (k : Kappa P) : sumEquiv P (Sum.inr k) = k.val := rfl

/-- The block matrix `[[Jᵀ, B], [0, 1]]` representing `extendedDeriv P v` in
the split coordinates `σ ⊕ κ`: the transposed evaluated Jacobi matrix, the
partial derivatives in the complementary directions, and the identity.-/
def blockMatrix (v : ι → ℂ) : Matrix (σ ⊕ Kappa P) (σ ⊕ Kappa P) ℂ :=
  Matrix.fromBlocks (evalJacobiMatrix P v)ᵀ
    (Matrix.of fun j (k : Kappa P) => eval v (pderiv k.val (P.relation j))) 0 1

/-- The block matrix is block-triangular; its determinant is the determinant
of the evaluated Jacobi matrix.
@isnad1 id=eq.0h5v.s7.758783c20df7 from=translated src=- shape=ca50c314 vocab=93275ecf
-/
theorem det_blockMatrix (v : ι → ℂ) :
    (blockMatrix P v).det = (evalJacobiMatrix P v).det := by
  rw [blockMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_transpose]

private lemma mulVec_apply' {m n : Type*} [Fintype n] (M : Matrix m n ℂ)
    (x : n → ℂ) (i : m) : (M *ᵥ x) i = ∑ s, M i s * x s := rfl

/-- The derivative of the extended map factors through the variable split as
multiplication by the block matrix.
@isnad1 id=eq.0h5v.s9.3167800b6ed4 from=translated src=- shape=109d547d vocab=36669ee2
-/
theorem extendedDeriv_eq_comp (v : ι → ℂ) :
    ⇑(extendedDeriv P v) =
      ⇑(Equiv.sumArrowEquivProdArrow σ (Kappa P) ℂ) ∘ (blockMatrix P v).mulVec ∘
        fun u => u ∘ ⇑(sumEquiv P) := by
  funext u
  have hfst : ∀ j : σ, polyGrad (P.relation j) v u
      = ((blockMatrix P v) *ᵥ (u ∘ ⇑(sumEquiv P))) (Sum.inl j) := by
    intro j
    have hL : polyGrad (P.relation j) v u
        = ∑ j' : σ, eval v (pderiv (P.map j') (P.relation j)) * u (P.map j')
          + ∑ k : Kappa P, eval v (pderiv k.val (P.relation j)) * u k.val := by
      rw [polyGrad_apply,
        ← Equiv.sum_comp (sumEquiv P)
          (fun i => eval v (pderiv i (P.relation j)) * u i),
        Fintype.sum_sum_type]
      rfl
    have hR : ((blockMatrix P v) *ᵥ (u ∘ ⇑(sumEquiv P))) (Sum.inl j)
        = ∑ j' : σ, eval v (pderiv (P.map j') (P.relation j)) * u (P.map j')
          + ∑ k : Kappa P, eval v (pderiv k.val (P.relation j)) * u k.val := by
      rw [mulVec_apply', Fintype.sum_sum_type]
      congr 1
      exact Finset.sum_congr rfl fun j' _ => by
        simp [blockMatrix, evalJacobiMatrix, P.jacobiMatrix_apply]
    exact hL.trans hR.symm
  have hsnd : ∀ k : Kappa P, u k.val
      = ((blockMatrix P v) *ᵥ (u ∘ ⇑(sumEquiv P))) (Sum.inr k) := by
    intro k
    rw [mulVec_apply', Fintype.sum_sum_type]
    simp [blockMatrix, Matrix.one_apply]
  refine Prod.ext ?_ ?_
  · funext j
    exact hfst j
  · funext k
    exact hsnd k

/-- **Invertibility transfer**: if the algebraic Jacobian of `P` is invertible
at a ℂ-point `φ`, the strict derivative of the extended map at the ambient
coordinates of `φ` is bijective.
@isnad1 id=bijectiv.1h5v.s9.ca867c1495c7 from=translated src=- shape=5b7c6106 vocab=0276408e
-/
theorem bijective_extendedDeriv (φ : CPoints S) (h : IsUnit (φ P.jacobian)) :
    Function.Bijective (extendedDeriv P (ambient P.toGenerators φ)) := by
  rw [extendedDeriv_eq_comp]
  have hM : IsUnit (blockMatrix P (ambient P.toGenerators φ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_blockMatrix, ← apply_jacobian]
    exact h
  refine (Equiv.sumArrowEquivProdArrow σ (Kappa P) ℂ).bijective.comp
    (Function.Bijective.comp ?_ ?_)
  · exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hM,
      Matrix.mulVec_surjective_iff_isUnit.mpr hM⟩
  · constructor
    · intro u u' huu'
      funext i
      simpa using congrFun huu' ((sumEquiv P).symm i)
    · intro w
      refine ⟨w ∘ ⇑(sumEquiv P).symm, ?_⟩
      funext s
      simp

/-- The derivative of the extended map at a ℂ-point with invertible algebraic
Jacobian, upgraded to a continuous linear equivalence `ℂ^ι ≃L[ℂ] ℂ^σ × ℂ^κ`.-/
def extendedDerivEquiv (φ : CPoints S) (h : IsUnit (φ P.jacobian)) :
    (ι → ℂ) ≃L[ℂ] (σ → ℂ) × (Kappa P → ℂ) :=
  (LinearEquiv.ofBijective
    (extendedDeriv P (ambient P.toGenerators φ) :
      (ι → ℂ) →ₗ[ℂ] (σ → ℂ) × (Kappa P → ℂ))
    (bijective_extendedDeriv P φ h)).toContinuousLinearEquiv

/--
@isnad1 id=eq.1h5v.s9.403e5d6ed857 from=translated src=- shape=96a76655 vocab=eb3f63bd
-/
@[simp]
lemma coe_extendedDerivEquiv (φ : CPoints S) (h : IsUnit (φ P.jacobian)) :
    (extendedDerivEquiv P φ h : (ι → ℂ) →L[ℂ] (σ → ℂ) × (Kappa P → ℂ))
      = extendedDeriv P (ambient P.toGenerators φ) := by
  refine ContinuousLinearMap.ext fun u => ?_
  rfl

/-- **The inverse-function-theorem input**: at a ℂ-point with invertible
algebraic Jacobian, the extended map of the presentation has a continuous
linear *equivalence* as strict Fréchet derivative.  For a submersive
presentation this holds at every ℂ-point (`isUnit_apply_jacobian`).
@isnad1 id=hasstric.1h5v.s9.4537e670e505 from=translated src=- shape=6f280a3d vocab=156b27e0
-/
theorem hasStrictFDerivAt_extendedMap_equiv (φ : CPoints S)
    (h : IsUnit (φ P.jacobian)) :
    HasStrictFDerivAt (extendedMap P)
      (extendedDerivEquiv P φ h : (ι → ℂ) →L[ℂ] (σ → ℂ) × (Kappa P → ℂ))
      (ambient P.toGenerators φ) := by
  have h1 := hasStrictFDerivAt_extendedMap P (ambient P.toGenerators φ)
  rwa [← coe_extendedDerivEquiv P φ h] at h1

end Presentation

/-! ## The zero locus of the relations -/

section ZeroLocus

variable {S : Type u} [CommRing S] [Algebra ℂ S] {ι : Type v} {σ : Type t}

end ZeroLocus

end HodgePilot.JacobianBridge
