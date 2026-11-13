import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MixedCharacteristic
import Tengoku.Seed.Analysis.Complex.Polynomial.GaussLucas
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Multiset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability under the MSS operator `1 - ∂`

The affine-line restriction algebra below is ported from the original
`CommutatorTheorem.Epsilon.BTStableLine` source. The target is the MSS difference
operator, not an assumed common interlacer or outcome-selection statement.
-/

namespace NoEpsilon
namespace MSSStability

open Polynomial
open scoped BigOperators

def InUpperHalfPlane (z : ℂ) : Prop := 0 < z.im

def UpperStable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, InUpperHalfPlane (z i)) → MvPolynomial.eval z p ≠ 0

noncomputable def nonnegativeDirectionalDerivative {σ : Type*} [Fintype σ]
    (w : σ → ℝ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i, MvPolynomial.C (w i : ℂ) * MvPolynomial.pderiv i p

/-- Restrict a multivariate polynomial to the affine complex line
`t ↦ z + t w`.-/
noncomputable def stableLinePolynomial {sigma : Type*}
    (z : sigma → ℂ) (w : sigma → ℝ) (p : MvPolynomial sigma ℂ) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Polynomial.C (z i) + Polynomial.C (w i : ℂ) * Polynomial.X) p

/-- Evaluation of the affine-line restriction is literal substitution along
that line.-/
theorem eval_stableLinePolynomial {sigma : Type*}
    (z : sigma → ℂ) (w : sigma → ℝ) (p : MvPolynomial sigma ℂ)
    (t : ℂ) :
    (stableLinePolynomial z w p).eval t =
      MvPolynomial.eval (fun i ↦ z i + (w i : ℂ) * t) p := by
  change Polynomial.evalRingHom t
      (MvPolynomial.eval₂ Polynomial.C
        (fun i ↦ Polynomial.C (z i) + Polynomial.C (w i : ℂ) * Polynomial.X) p) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext a
    simp
  have hx :
      (⇑(Polynomial.evalRingHom t) ∘
          (fun i : sigma ↦
            Polynomial.C (z i) + Polynomial.C (w i : ℂ) * Polynomial.X)) =
        (fun i ↦ z i + (w i : ℂ) * t) := by
    funext i
    simp
  rw [hc, hx, MvPolynomial.eval₂_id]

/-- Starting in the open upper half-plane and moving in a nonnegative real
direction stays there for every parameter in the closed upper half-plane.-/
theorem affineLine_inUpperHalfPlane {sigma : Type*}
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i)
    {t : ℂ} (ht : 0 ≤ t.im) :
    ∀ i, InUpperHalfPlane (z i + (w i : ℂ) * t) := by
  intro i
  unfold InUpperHalfPlane at hz ⊢
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  exact add_pos_of_pos_of_nonneg (hz i) (mul_nonneg (hw i) ht)

/-- A nonzero stable polynomial restricts to a nonzero univariate
polynomial on every such line.-/
theorem stableLinePolynomial_ne_zero {sigma : Type*}
    {p : MvPolynomial sigma ℂ}
    (hp : ∀ z : sigma → ℂ, (∀ i, InUpperHalfPlane (z i)) →
      MvPolynomial.eval z p ≠ 0)
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) :
    stableLinePolynomial z w p ≠ 0 := by
  intro hzero
  have heval := congrArg (fun q : ℂ[X] ↦ q.eval 0) hzero
  change (stableLinePolynomial z w p).eval 0 = (0 : ℂ[X]).eval 0 at heval
  rw [eval_stableLinePolynomial] at heval
  simp only [mul_zero, add_zero, eval_zero] at heval
  exact hp z hz heval

/-- Every root of a stable affine-line restriction lies strictly in the
lower half-plane.  The strictness comes from the positive imaginary part of
the base point, so it also holds for real line parameters.-/
theorem root_im_neg_of_stableLinePolynomial {sigma : Type*}
    {p : MvPolynomial sigma ℂ}
    (hp : ∀ z : sigma → ℂ, (∀ i, InUpperHalfPlane (z i)) →
      MvPolynomial.eval z p ≠ 0)
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i)
    {a : ℂ} (ha : (stableLinePolynomial z w p).IsRoot a) :
    a.im < 0 := by
  by_contra hnot
  have haim : 0 ≤ a.im := le_of_not_gt hnot
  have hline := affineLine_inUpperHalfPlane z w hz hw haim
  apply hp (fun i ↦ z i + (w i : ℂ) * a) hline
  rw [← eval_stableLinePolynomial]
  exact ha

/-- The reciprocal displacement from `0` to a strict lower-half-plane point
also has strictly negative imaginary part.-/
theorem one_div_neg_im_neg {a : ℂ} (ha : a.im < 0) :
    (1 / (0 - a)).im < 0 := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  rw [show 0 - a = -a by simp, one_div, Complex.inv_im]
  have hnum : -(-a).im = a.im := by simp
  rw [hnum, Complex.normSq_neg]
  exact div_neg_of_neg_of_pos ha (Complex.normSq_pos.mpr ha0)

private theorem im_multiset_sum (s : Multiset ℂ) :
    s.sum.im = (s.map Complex.im).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih, Complex.add_im]

/-- A logarithmic derivative on a strict lower-root line cannot equal the positive real
number one. This strengthens the nonpositive-imaginary-part estimate by treating the
constant polynomial separately and using a strict sign for every root otherwise.-/
theorem stableLine_logDerivative_ne_one {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : UpperStable p)
    (z : σ → ℂ) (w : σ → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i) :
    (stableLinePolynomial z w p).derivative.eval 0 /
      (stableLinePolynomial z w p).eval 0 ≠ 1 := by
  let f := stableLinePolynomial z w p
  have hf0 : f.eval 0 ≠ 0 := by
    rw [eval_stableLinePolynomial]
    simpa using hp z hz
  have hfne : f ≠ 0 := fun h ↦ hf0 (by rw [h]; simp)
  by_cases hdeg : f.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    change f.derivative.eval 0 / f.eval 0 ≠ 1
    rw [← hc]
    simp
  · have hroot : f.roots ≠ 0 := (IsAlgClosed.splits f).roots_ne_zero hdeg
    have hneg : ∀ a ∈ f.roots, (1 / (0 - a)).im < 0 := by
      intro a ha
      exact one_div_neg_im_neg
        (root_im_neg_of_stableLinePolynomial hp z w hz hw ((mem_roots hfne).mp ha))
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hroot
    have hsum : (f.roots.map (fun a ↦ (1 / (0 - a)).im)).sum < 0 := by
      simpa using (Multiset.sum_lt_sum
        (s := f.roots) (f := fun a ↦ (1 / (0 - a)).im) (g := fun _ ↦ (0 : ℝ))
        (fun a ha ↦ (hneg a ha).le) ⟨a, ha, hneg a ha⟩)
    have him : (f.derivative.eval 0 / f.eval 0).im < 0 := by
      rw [(IsAlgClosed.splits f).eval_derivative_div_eval_of_ne_zero hf0,
        im_multiset_sum, Multiset.map_map]
      exact hsum
    intro h
    change f.derivative.eval 0 / f.eval 0 = 1 at h
    rw [h] at him
    simp at him

section DeterminantPencil

open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A positive semidefinite matrix pencil with positive definite total coefficient is
nonsingular whenever all its coefficients have positive imaginary part.-/
theorem det_psd_pencil_ne_zero (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hTotal : (∑ i, A i).PosDef)
    (z : κ → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (∑ i, z i • A i).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let q : κ → ℂ := fun i ↦ star v ⬝ᵥ ((A i).mulVec v)
  have hq : ∀ i, 0 ≤ (q i).re :=
    fun i ↦ (Complex.nonneg_iff.mp ((hA i).dotProduct_mulVec_nonneg v)).1
  have hqi : ∀ i, (q i).im = 0 :=
    fun i ↦ (Complex.nonneg_iff.mp ((hA i).dotProduct_mulVec_nonneg v)).2.symm
  have hsum : 0 < ∑ i, (q i).re := by
    have ht := (Complex.pos_iff.mp (hTotal.dotProduct_mulVec_pos hv)).1
    simpa only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum] using ht
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hq i)).mp hsum
  have hpos : 0 < ∑ i, (z i).im * (q i).re := by
    apply Finset.sum_pos'
    · exact fun i _ ↦ mul_nonneg (hz i).le (hq i)
    · exact ⟨i, Finset.mem_univ i, mul_pos (hz i) hi⟩
  have him : (star v ⬝ᵥ ((∑ i, z i • A i).mulVec v)).im =
      ∑ i, (z i).im * (q i).re := by
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (z i * q i).im = _
    rw [Complex.mul_im, hqi, mul_zero, zero_add]
  rw [hker, dotProduct_zero] at him
  simp only [Complex.zero_im] at him
  linarith

/-- The determinant polynomial of a positive semidefinite matrix family.-/
noncomputable def psdPencil (A : κ → Matrix ι ι ℂ) : MvPolynomial κ ℂ :=
  (∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C).det

end DeterminantPencil

end MSSStability
end NoEpsilon
