import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.Statement
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact norming polynomials and the harmonic scale

The classical sharp proof must produce logarithmic mass from mesoscopic
indices.  This file formalizes two source-transparent pieces of that route:

* the exact dual/norming polynomial for the Lebesgue function; and
* the elementary comparison `log n ≤ H_(n-1)`.

No lower bound for arbitrary nodes is assumed here.
-/

namespace Erdos1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- A `±1` sign chosen so that `interpolationSign x * x = |x|`.
We choose `+1` at zero; this makes every nodal value have absolute value
exactly one.-/
def interpolationSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

/--
@isnad1 id=eq.0h1v.s4.4604809dfb89 from=translated src=- shape=38becc55 vocab=87aec7cf
-/
@[simp]
lemma abs_interpolationSign (x : ℝ) : |interpolationSign x| = 1 := by
  unfold interpolationSign
  split_ifs <;> norm_num

/--
@isnad1 id=eq.0h1v.s4.f11189def377 from=translated src=- shape=9a232c61 vocab=b98bdb50
-/
lemma interpolationSign_mul_self (x : ℝ) : interpolationSign x * x = |x| := by
  unfold interpolationSign
  split_ifs with hx
  · simp [abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [abs_of_nonpos hx']

/-- The Lagrange interpolant of the signs of the fundamental functions at
`t`.  It is a degree-below-`n` polynomial with nodal absolute values exactly
one and value exactly the Lebesgue function at `t`.-/
def normingPolynomial {n : ℕ} (nodes : NodeFamily n) (t : ℝ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ nodes.point
    (fun k ↦ interpolationSign (lagrangeFundamental nodes k t))

/--
@isnad1 id=lt.0h3v.s4.a16d24a1b4f4 from=translated src=- shape=7a7bc91c vocab=06504e9c
-/
lemma degree_normingPolynomial_lt {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    (normingPolynomial nodes t).degree < n := by
  simpa only [normingPolynomial, Finset.card_univ, Fintype.card_fin] using
    (Lagrange.degree_interpolate_lt
      (s := Finset.univ)
      (r := fun k ↦ interpolationSign (lagrangeFundamental nodes k t))
      nodes.injective.injOn)

/--
@isnad1 id=eq.0h4v.s4.f3dc4b7694c6 from=translated src=- shape=e19725a5 vocab=a4c6ef39
-/
@[simp]
lemma normingPolynomial_eval_node {n : ℕ} (nodes : NodeFamily n) (t : ℝ)
    (k : Fin n) :
    (normingPolynomial nodes t).eval (nodes.point k) =
      interpolationSign (lagrangeFundamental nodes k t) := by
  simpa only [normingPolynomial] using
    (Lagrange.eval_interpolate_at_node
      (r := fun j ↦ interpolationSign (lagrangeFundamental nodes j t))
      nodes.injective.injOn (Finset.mem_univ k))

/--
@isnad1 id=eq.0h4v.s5.36b84d6f9da3 from=translated src=- shape=0dc20a33 vocab=e2de400f
-/
@[simp]
lemma abs_normingPolynomial_eval_node {n : ℕ} (nodes : NodeFamily n) (t : ℝ)
    (k : Fin n) :
    |(normingPolynomial nodes t).eval (nodes.point k)| = 1 := by
  rw [normingPolynomial_eval_node, abs_interpolationSign]

/--
@isnad1 id=eq.0h4v.s5.4609e1f71419 from=translated src=- shape=a49a7c94 vocab=43f310a2
-/
lemma normingPolynomial_eval_eq_sum {n : ℕ} (nodes : NodeFamily n) (t u : ℝ) :
    (normingPolynomial nodes t).eval u =
      ∑ k : Fin n, interpolationSign (lagrangeFundamental nodes k t) *
        lagrangeFundamental nodes k u := by
  classical
  simp only [normingPolynomial, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  change interpolationSign (lagrangeFundamental nodes k t) *
    (lagrangeBasis nodes k).eval u = _
  rw [lagrangeBasis_eval]

/-- The norming polynomial realizes the Lebesgue function exactly.
@isnad1 id=eq.0h3v.s4.f3bc23116a6a from=translated src=- shape=8caa6e88 vocab=82da2b46
-/
lemma normingPolynomial_eval_self {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    (normingPolynomial nodes t).eval t = lebesgueFunction nodes t := by
  rw [normingPolynomial_eval_eq_sum, lebesgueFunction]
  apply Finset.sum_congr rfl
  intro k _
  exact interpolationSign_mul_self _

/--
@isnad1 id=le.0h3v.s4.789404cf8afa from=translated src=- shape=33fe603d vocab=1c30ade8
-/
lemma lebesgueFunction_nonneg {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    0 ≤ lebesgueFunction nodes t := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- At each point, the Lebesgue function is realized by a polynomial whose
nodal absolute values are one.
@isnad1 id=polynomi.2h4v.s5.32b7c2587765 from=translated src=- shape=3d6ed4a7 vocab=6c874e25
-/
lemma normingPolynomial_is_certificate {n : ℕ} (nodes : NodeFamily n)
    {A t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hA : A < lebesgueFunction nodes t) :
    PolynomialCertificate nodes A := by
  refine ⟨normingPolynomial nodes t, t, ht, degree_normingPolynomial_lt nodes t,
    fun k ↦ (abs_normingPolynomial_eval_node nodes t k).le, ?_⟩
  rw [normingPolynomial_eval_self, abs_of_nonneg (lebesgueFunction_nonneg nodes t)]
  exact hA

/-- The polynomial certificate interface is exact, not merely sufficient.
@isnad1 id=iff.0h3v.s5.e966acf0676e from=translated src=- shape=bbc6aed2 vocab=6c874e25
-/
lemma polynomialCertificate_iff_exists_point {n : ℕ} (nodes : NodeFamily n) (A : ℝ) :
    PolynomialCertificate nodes A ↔
      ∃ t ∈ Set.Icc (-1 : ℝ) 1, A < lebesgueFunction nodes t := by
  constructor
  · rintro ⟨p, t, ht, hpdeg, hpnodes, hlarge⟩
    exact ⟨t, ht, hlarge.trans_le
      (abs_eval_le_lebesgueFunction nodes p hpdeg t hpnodes)⟩
  · rintro ⟨t, ht, hlarge⟩
    exact normingPolynomial_is_certificate nodes ht hlarge

/-- Equivalently, polynomial certificates characterize strict lower bounds
for the full-interval Lebesgue constant.
@isnad1 id=iff.0h3v.s5.5b40419afe86 from=translated src=- shape=aafbf425 vocab=f0e65d23
-/
lemma polynomialCertificate_iff_lt_lebesgueOn {n : ℕ}
    (nodes : NodeFamily n) (A : ℝ) :
    PolynomialCertificate nodes A ↔ A < lebesgueOn nodes (-1) 1 := by
  rw [polynomialCertificate_iff_exists_point,
    lt_lebesgueOn_iff nodes (by norm_num)]

/-- The real-valued harmonic scale used by mesoscopic row sums.-/
def realHarmonic (n : ℕ) : ℝ :=
  (harmonic n : ℝ)

/-- The elementary sharp-leading-coefficient comparison
`log n ≤ H_(n-1)` for positive `n`.
@isnad1 id=le.1h1v.s5.6cd2d5b82add from=translated src=- shape=8b12c17b vocab=f260357e
-/
lemma log_nat_le_realHarmonic_pred {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ realHarmonic (n - 1) := by
  have h := log_add_one_le_harmonic (n - 1)
  simpa only [realHarmonic, Nat.sub_add_cancel hn] using h

/-- A harmonic-size certificate is the precise finite input from which the
sharp logarithmic coefficient follows after absorbing a uniform constant.-/
def HarmonicCertificate {n : ℕ} (nodes : NodeFamily n) (C : ℝ) : Prop :=
  PolynomialCertificate nodes
    ((2 / Real.pi) * realHarmonic (n - 1) - C)

end

end ClassicalBound
end Erdos1153
