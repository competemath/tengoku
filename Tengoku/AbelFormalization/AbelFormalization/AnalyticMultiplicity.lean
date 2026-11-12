import Tengoku.AbelFormalization.AbelFormalization.HermiteNodeBounds
import Tengoku.Seed.Analysis.Analytic.Order
import Tengoku.Seed.Analysis.Analytic.Polynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Algebra.Polynomial.FieldDivision
import Tengoku.Seed.RingTheory.Coprime.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Vanishing jets of divisible analytic remainders

Local analytic divisibility by `(z-ξ)^m` forces every derivative of order below
`m` to vanish. Applied to a polynomial interpolation remainder, this gives the
jet equalities, including the sum of multiplicities at colliding nodes.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

namespace AbelFormalization

/-- A local analytic power factor forces all lower derivatives to vanish.
Analyticity of `f` follows from the local factorization and is not an added
hypothesis.
@isnad1 id=eq.3h5v.s7.e3f43418c384 from=translated src=- shape=d438ae3e vocab=9a85eaba
-/
theorem iteratedDeriv_eq_zero_of_analytic_factor {f h : ℂ → ℂ} {ξ : ℂ} {m r : ℕ}
    (hh : AnalyticAt ℂ h ξ)
    (he : f =ᶠ[𝓝 ξ] fun z => (z - ξ) ^ m * h z) (hr : r < m) :
    iteratedDeriv r f ξ = 0 := by
  have hp : AnalyticAt ℂ (fun z => (z - ξ) ^ m * h z) ξ :=
    ((analyticAt_id.sub analyticAt_const).pow m).mul hh
  have hf : AnalyticAt ℂ f ξ := hp.congr he.symm
  have ho : (m : ℕ∞) ≤ analyticOrderAt f ξ :=
    (natCast_le_analyticOrderAt hf).mpr ⟨h, hh, by
      filter_upwards [he] with z hz
      simpa only [smul_eq_mul] using hz⟩
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp ho r hr

/-- Two analytic functions have the same lower jets if their local difference
contains the specified power factor.
@isnad1 id=eq.5h6v.s7.8a3ff11f690a from=translated src=- shape=bc57db34 vocab=9a85eaba
-/
theorem iteratedDeriv_eq_of_analytic_factor {f g h : ℂ → ℂ} {ξ : ℂ} {m r : ℕ}
    (hf : AnalyticAt ℂ f ξ) (hg : AnalyticAt ℂ g ξ) (hh : AnalyticAt ℂ h ξ)
    (he : (fun z => f z - g z) =ᶠ[𝓝 ξ] fun z => (z - ξ) ^ m * h z)
    (hr : r < m) : iteratedDeriv r f ξ = iteratedDeriv r g ξ := by
  have hz := iteratedDeriv_eq_zero_of_analytic_factor hh he hr
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt] at hz
  exact sub_eq_zero.mp hz

/--
@isnad1 id=analytic.0h2v.s5.34cc29ff9a05 from=translated src=- shape=846cab93 vocab=84d1cbdb
-/
theorem polynomial_eval_analyticAt (P : ℂ[X]) (ξ : ℂ) :
    AnalyticAt ℂ (fun z => P.eval z) ξ :=
  AnalyticOnNhd.eval_polynomial P ξ (Set.mem_univ ξ)

/-- A polynomial-divisible analytic remainder gives the interpolation jet
equalities at each divisor root.
@isnad1 id=eq.5h7v.s8.e02e7dbc1829 from=translated src=- shape=eb644a3b vocab=f214fb41
-/
theorem iteratedDeriv_eq_of_divisible_analytic_remainder
    {f h : ℂ → ℂ} {P Q : ℂ[X]} {ξ : ℂ} {m r : ℕ}
    (hf : AnalyticAt ℂ f ξ) (hh : AnalyticAt ℂ h ξ)
    (hdiv : (X - C ξ) ^ m ∣ Q)
    (he : (fun z => f z - P.eval z) =ᶠ[𝓝 ξ] fun z => Q.eval z * h z)
    (hr : r < m) : iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ := by
  obtain ⟨R, hQ⟩ := hdiv
  apply iteratedDeriv_eq_of_analytic_factor hf (polynomial_eval_analyticAt P ξ)
    ((polynomial_eval_analyticAt R ξ).mul hh) _ hr
  filter_upwards [he] with z hz
  rw [hz, hQ, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  simp only [Pi.mul_apply]
  ring

/-- The full multiplicity at a repeated node is the sum of all its supplied
multiplicities. A node-polynomial remainder matches that entire jet.
@isnad1 id=eq.4h8v.s7.423ad5fc80d7 from=translated src=- shape=fc52d4bb vocab=3a1044e0
-/
theorem iteratedDeriv_eq_of_nodePolynomial_remainder {ι : Type*} [Fintype ι]
    {f h : ℂ → ℂ} {P : ℂ[X]} (δ : ι → ℂ) (m : ι → ℕ) {ξ : ℂ} {r : ℕ}
    (hf : AnalyticAt ℂ f ξ) (hh : AnalyticAt ℂ h ξ)
    (he : (fun z => f z - P.eval z) =ᶠ[𝓝 ξ]
      fun z => (nodePolynomial δ m).eval z * h z)
    (hr : r < nodeMultiplicity δ m ξ) :
    iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ :=
  iteratedDeriv_eq_of_divisible_analytic_remainder hf hh
    (grouped_node_factor_dvd δ m ξ) he hr

/-- Analytic derivatives of polynomial evaluation agree with iterates of the
formal polynomial derivative.
@isnad1 id=eq.0h2v.s7.922da02cfa75 from=translated src=- shape=34f0c3fa vocab=2b5bfa82
-/
theorem iteratedDeriv_polynomial_eval (P : ℂ[X]) (r : ℕ) :
    iteratedDeriv r (fun z => P.eval z) =
      fun z => (Polynomial.derivative^[r] P).eval z := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ',
      show deriv (fun z => P.eval z) = (fun z => P.derivative.eval z) from
        funext fun z => P.deriv, ih]
    rfl

/-- Vanishing polynomial jets imply divisibility by the corresponding power
of a linear factor.
@isnad1 id=dvd.1h3v.s7.b11cb93e6dee from=translated src=- shape=1900695d vocab=fafd8733
-/
theorem polynomial_factor_dvd_of_iteratedDeriv_zero {P : ℂ[X]} {ξ : ℂ} {m : ℕ}
    (hjets : ∀ r < m, iteratedDeriv r (fun z => P.eval z) ξ = 0) :
    (X - C ξ) ^ m ∣ P := by
  by_cases hP : P = 0
  · simp [hP]
  cases m with
  | zero => simp
  | succ k =>
    apply (Polynomial.le_rootMultiplicity_iff hP).mp
    apply Nat.succ_le_iff.mpr
    apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hP
    intro r hr
    have hz := hjets r (Nat.lt_succ_of_le hr)
    rwa [iteratedDeriv_polynomial_eval] at hz

open scoped Classical in
/-- The node polynomial can be grouped over its distinct node values.
@isnad1 id=eq.0h3v.s7.06a8da2540df from=translated src=- shape=33b101bc vocab=c50bcda5
-/
theorem nodePolynomial_eq_prod_grouped {ι : Type*} [Fintype ι]
    (δ : ι → ℂ) (m : ι → ℕ) :
    nodePolynomial δ m =
      ∏ ξ ∈ Finset.univ.image δ, (X - C ξ) ^ nodeMultiplicity δ m ξ := by
  classical
  unfold nodePolynomial
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image δ)
    (fun i hi => Finset.mem_image_of_mem δ hi)
    (fun i => (X - C (δ i)) ^ m i)]
  apply Finset.prod_congr rfl
  intro ξ _
  calc
    _ = ∏ i ∈ Finset.univ.filter (fun i => δ i = ξ), (X - C ξ) ^ m i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- Jets at the distinct node values, with multiplicities added at collisions,
force divisibility by the full node polynomial.
@isnad1 id=dvd.1h4v.s6.f38e67ade2f2 from=translated src=- shape=81513392 vocab=5a02dd58
-/
theorem nodePolynomial_dvd_of_iteratedDeriv_zero {ι : Type*} [Fintype ι]
    (δ : ι → ℂ) (m : ι → ℕ) {P : ℂ[X]}
    (hjets : ∀ ξ r, r < nodeMultiplicity δ m ξ →
      iteratedDeriv r (fun z => P.eval z) ξ = 0) :
    nodePolynomial δ m ∣ P := by
  classical
  rw [nodePolynomial_eq_prod_grouped]
  apply Finset.prod_dvd_of_coprime
  · intro ξ _ η _ hne
    exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id hne).pow
  · intro ξ _
    exact polynomial_factor_dvd_of_iteratedDeriv_zero (hjets ξ)

/-- Polynomial interpolation is unique below the total multiplicity. At
colliding nodes the derivative conditions use the sum of the multiplicities.
The `degree` formulation includes the zero polynomial and total multiplicity
zero.
@isnad1 id=eq.3h5v.s7.a466d19311e5 from=translated src=- shape=a889966d vocab=10de2267
-/
theorem polynomial_eq_of_grouped_jets {ι : Type*} [Fintype ι]
    (δ : ι → ℂ) (m : ι → ℕ) {P₁ P₂ : ℂ[X]}
    (hdegree₁ : P₁.degree < (totalMultiplicity m : WithBot ℕ))
    (hdegree₂ : P₂.degree < (totalMultiplicity m : WithBot ℕ))
    (hjets : ∀ ξ r, r < nodeMultiplicity δ m ξ →
      iteratedDeriv r (fun z => P₁.eval z) ξ =
        iteratedDeriv r (fun z => P₂.eval z) ξ) :
    P₁ = P₂ := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt
    (nodePolynomial_dvd_of_iteratedDeriv_zero δ m ?_)
  · rw [nodePolynomial_degree]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le P₁ P₂) (max_lt hdegree₁ hdegree₂)
  · intro ξ r hr
    simp only [eval_sub]
    rw [iteratedDeriv_fun_sub (polynomial_eval_analyticAt P₁ ξ).contDiffAt
      (polynomial_eval_analyticAt P₂ ξ).contDiffAt, hjets ξ r hr, sub_self]

end AbelFormalization
