import Tengoku.WasowAsymptoticsLean.WasowPolynomialPhase
import Tengoku.Seed.Analysis.Polynomial.Basic
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.eventually_eval_nonneg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.exists_monotone_tail` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.polynomial_tail_dichotomy` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.eval_realPhasePolynomial` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.root_polynomial_tail_dichotomy` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.phase_difference_tail_dichotomy` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.exists_common_phase_ordering` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.phase_continuous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseOrdering.phase_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/

/-! Automatic eventual ordering of real parts of finite Puiseux-polynomial
phases. The polynomials are fixed before the ray direction is chosen. -/
set_option autoImplicit false
noncomputable section
open Polynomial Filter Set
open scoped Topology BigOperators
namespace WasowPhaseOrdering

/-- The sign of a nonnegative leading coefficient controls a real polynomial
on a sufficiently late half-line, including constant polynomials.
@isnad1 id=eventual.1h1v.s5.fd4fe21c6730 from=translated src=- shape=4819ae1c vocab=10ab22ee
-/
theorem eventually_eval_nonneg (P : Polynomial ℝ) (hP : 0 ≤ P.leadingCoeff) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ P.eval x := by
  by_cases hd : P.natDegree = 0
  · have he : P = C P.leadingCoeff := by
      simpa [leadingCoeff, hd] using P.eq_C_of_natDegree_eq_zero hd
    apply Filter.Eventually.of_forall
    intro x
    rw [he, eval_C]
    exact hP
  · exact (P.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) hP).eventually
        (eventually_ge_atTop 0)

/-- Positive leading coefficient gives eventual monotonicity; a constant
polynomial is allowed.
@isnad1 id=ex.1h1v.s5.014300cba782 from=translated src=- shape=770cddf6 vocab=4f70a55c
-/
theorem exists_monotone_tail (P : Polynomial ℝ) (hP : 0 ≤ P.leadingCoeff) :
    ∃ a : ℝ, MonotoneOn (fun r => P.eval r) (Ici a) := by
  have hd : 0 ≤ P.derivative.leadingCoeff := by
    rw [leadingCoeff_derivative]
    exact mul_nonneg hP (Nat.cast_nonneg _)
  obtain ⟨a, ha⟩ := eventually_atTop.mp (eventually_eval_nonneg P.derivative hd)
  refine ⟨a, monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    P.continuous.continuousOn (fun r _ => (P.hasDerivAt r).hasDerivWithinAt) ?_⟩
  intro r hr
  exact ha r (interior_subset hr)

/-- Every real polynomial is eventually increasing, or decreasing to minus
infinity. Constants belong to the increasing alternative.
@isnad1 id=ex.0h1v.s5.35d351dd41c9 from=translated src=- shape=b6df82e3 vocab=649eb9cd
-/
theorem polynomial_tail_dichotomy (P : Polynomial ℝ) :
    ∃ a : ℝ, MonotoneOn (fun r => P.eval r) (Ici a) ∨
      (AntitoneOn (fun r => P.eval r) (Ici a) ∧
        Tendsto (fun r => P.eval r) atTop atBot) := by
  by_cases hd : P.natDegree = 0
  · refine ⟨0, Or.inl ?_⟩
    rw [P.eq_C_of_natDegree_eq_zero hd]
    simp only [eval_C]
    exact fun _ _ _ _ _ => le_rfl
  · rcases le_or_gt 0 P.leadingCoeff with hp | hp
    · obtain ⟨a, ha⟩ := exists_monotone_tail P hp
      exact ⟨a, Or.inl ha⟩
    · obtain ⟨a, ha⟩ := exists_monotone_tail (-P) (by simpa using hp.le)
      refine ⟨a, Or.inr ⟨?_, P.tendsto_atBot_of_leadingCoeff_nonpos
        (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) hp.le⟩⟩
      intro x hx y hy hxy
      have hh := ha hx hy hxy
      simpa only [eval_neg, neg_le_neg_iff] using hh

/-- Taking real parts after a fixed complex rotation still gives an actual
real polynomial in the radial root parameter.-/
def realPhasePolynomial (P : Polynomial ℂ) (c : ℂ) : Polynomial ℝ :=
  ∑ n ∈ P.support, monomial n ((P.coeff n * c ^ n).re)

/--
@isnad1 id=eq.0h3v.s5.82ee55341904 from=translated src=- shape=32db339c vocab=c3ff6954
-/
theorem eval_realPhasePolynomial (P : Polynomial ℂ) (c : ℂ) (r : ℝ) :
    (realPhasePolynomial P c).eval r = (P.eval ((r : ℂ) * c)).re := by
  unfold realPhasePolynomial
  rw [eval_finsetSum]
  simp only [eval_monomial]
  conv_rhs => rw [eval_eq_sum, Polynomial.sum, Complex.re_sum]
  simp only [mul_pow]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm ((r : ℂ)^n), ← mul_assoc, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Taking a positive real root preserves the eventual polynomial dichotomy.
@isnad1 id=ex.1h2v.s6.9f36054a19f6 from=translated src=- shape=4e446eb7 vocab=4478361a
-/
theorem root_polynomial_tail_dichotomy (P : Polynomial ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ a : ℝ, 1 ≤ a ∧
      (MonotoneOn (fun r => P.eval (r ^ s)) (Ici a) ∨
      (AntitoneOn (fun r => P.eval (r ^ s)) (Ici a) ∧
        Tendsto (fun r => P.eval (r ^ s)) atTop atBot)) := by
  obtain ⟨b, hb⟩ := polynomial_tail_dichotomy P
  obtain ⟨c, hc⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hs).eventually (eventually_ge_atTop b))
  refine ⟨max 1 c, le_max_left _ _, ?_⟩
  have htail {r : ℝ} (hr : r ∈ Ici (max 1 c)) : r ^ s ∈ Ici b :=
    hc r ((le_max_right 1 c).trans hr)
  have hmono {x y : ℝ} (hx : x ∈ Ici (max 1 c)) (hxy : x ≤ y) : x ^ s ≤ y ^ s :=
    Real.rpow_le_rpow (le_trans (by norm_num) ((le_max_left 1 c).trans hx)) hxy hs.le
  rcases hb with hb | ⟨hb, hd⟩
  · exact Or.inl (fun _ hx _ hy hxy => hb (htail hx) (htail hy) (hmono hx hxy))
  · exact Or.inr ⟨(fun _ hx _ hy hxy => hb (htail hx) (htail hy) (hmono hx hxy)),
      hd.comp (tendsto_rpow_atTop hs)⟩

open CRGNormalFormGoal

/-- Each actual phase difference on any chosen root branch admits the
integration direction needed by the Volterra construction.
@isnad1 id=ex.1h5v.s7.76cf7c8d8a4b from=translated src=- shape=259e815b vocab=2899289c
-/
theorem phase_difference_tail_dichotomy (p : ℕ) (hp : 0 < p)
    (G H : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) :
    ∃ a : ℝ, 1 ≤ a ∧
      (MonotoneOn (fun r => (phaseOnRay p G θ ℓ r - phaseOnRay p H θ ℓ r).re) (Ici a) ∨
      (AntitoneOn (fun r => (phaseOnRay p G θ ℓ r - phaseOnRay p H θ ℓ r).re) (Ici a) ∧
        Tendsto (fun r => (phaseOnRay p G θ ℓ r - phaseOnRay p H θ ℓ r).re) atTop atBot)) := by
  let c : ℂ := Complex.exp (((θ + 2 * Real.pi * (ℓ : ℝ)) / (p : ℝ) : ℝ) * Complex.I)
  have he (r : ℝ) :
      (realPhasePolynomial (G-H) c).eval (r ^ (1/(p : ℝ))) =
        (phaseOnRay p G θ ℓ r - phaseOnRay p H θ ℓ r).re := by
    rw [eval_realPhasePolynomial, eval_sub]
    rfl
  simpa only [he] using root_polynomial_tail_dichotomy (realPhasePolynomial (G-H) c)
    (one_div_pos.mpr (by exact_mod_cast hp) : 0 < 1/(p : ℝ))

/-- All pairwise choices work on a single common half-line. The finite
Puiseux phases are fixed independently of the ray angle and root branch.
@isnad1 id=ex.1h5v.s8.912641a37900 from=translated src=- shape=0f2ffa2a vocab=08dcfe45
-/
theorem exists_common_phase_ordering {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (G : ι → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) :
    ∃ a : ℝ, 1 ≤ a ∧ ∃ mode : ι → ι → Bool,
      (∀ j i, if mode j i then
        Antitone (fun t : Ici a =>
          (phaseOnRay p (G i) θ ℓ t - phaseOnRay p (G j) θ ℓ t).re)
        else Monotone (fun t : Ici a =>
          (phaseOnRay p (G i) θ ℓ t - phaseOnRay p (G j) θ ℓ t).re)) ∧
      (∀ j i, mode j i = true →
        Tendsto (fun t : Ici a =>
          (phaseOnRay p (G i) θ ℓ t - phaseOnRay p (G j) θ ℓ t).re) atTop atBot) := by
  classical
  have hpair (j i : ι) := phase_difference_tail_dichotomy p hp (G i) (G j) θ ℓ
  choose b _hb hord using hpair
  obtain ⟨c, hc⟩ := Finite.bddAbove_range (fun ji : ι × ι => b ji.1 ji.2)
  let a := max 1 c
  have hab (j i : ι) : b j i ≤ a := (hc ⟨(j,i),rfl⟩).trans (le_max_right _ _)
  let mode : ι → ι → Bool := fun j i =>
    if MonotoneOn (fun r => (phaseOnRay p (G i) θ ℓ r - phaseOnRay p (G j) θ ℓ r).re)
      (Ici (b j i)) then false else true
  have hval : Tendsto (fun t : Ici a => (t : ℝ)) atTop atTop :=
    tendsto_Ici_atTop.mp tendsto_id
  refine ⟨a, le_max_left _ _, mode, ?_, ?_⟩
  · intro j i
    by_cases h : MonotoneOn
        (fun r => (phaseOnRay p (G i) θ ℓ r - phaseOnRay p (G j) θ ℓ r).re) (Ici (b j i))
    · have hm : mode j i = false := ite_eq_left h
      rw [hm]
      exact fun x y hxy => h ((hab j i).trans x.property)
        ((hab j i).trans y.property) hxy
    · have hm : mode j i = true := ite_eq_right h
      rw [hm]
      obtain ⟨hanti, _⟩ := (hord j i).resolve_left h
      exact fun x y hxy => hanti ((hab j i).trans x.property)
        ((hab j i).trans y.property) hxy
  · intro j i hm
    have hn : ¬ MonotoneOn
        (fun r => (phaseOnRay p (G i) θ ℓ r - phaseOnRay p (G j) θ ℓ r).re)
        (Ici (b j i)) := by
      intro h
      have hf : mode j i = false := ite_eq_left h
      rw [hf] at hm
      cases hm
    exact ((hord j i).resolve_left hn).2.comp hval

/-- The actual phases are continuous on the entire real parameter line.
@isnad1 id=continuo.1h4v.s5.30d976eb0964 from=translated src=- shape=eaceb4dd vocab=122a66b5
-/
theorem phase_continuous (p : ℕ) (hp : 0 < p) (G : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) :
    Continuous (phaseOnRay p G θ ℓ) := by
  unfold phaseOnRay rootOnRay
  exact G.continuous.comp ((Complex.continuous_ofReal.comp
    (Real.continuous_rpow_const (by positivity : 0 ≤ 1/(p : ℝ)))).mul continuous_const)

/-- Actual real-parameter derivative, including the ramified root factor.
@isnad1 id=hasderiv.1h5v.s8.d798ebfb7981 from=translated src=- shape=1fcd593a vocab=30624862
-/
theorem phase_hasDerivAt (p : ℕ) (G : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (phaseOnRay p G θ ℓ)
      ((((1/(p : ℝ)) * r ^ (1/(p : ℝ)-1) : ℝ) : ℂ) *
        Complex.exp (((θ + 2 * Real.pi * (ℓ : ℝ)) / (p : ℝ) : ℝ) * Complex.I) *
        G.derivative.eval (rootOnRay p θ ℓ r)) r := by
  have hh := ((Real.hasDerivAt_rpow_const (p := 1/(p : ℝ)) (Or.inl hr.ne')).ofReal_comp).mul_const
    (Complex.exp (((θ + 2 * Real.pi * (ℓ : ℝ)) / (p : ℝ) : ℝ) * Complex.I))
  exact (G.hasDerivAt (rootOnRay p θ ℓ r)).scomp r hh

end WasowPhaseOrdering

