module

public import Tengoku
public import Tengoku.GroebnerProj.Groebner.ToMathlib.PropLemma
public import Tengoku.GroebnerProj.Groebner.ToMathlib.MvPolynomial

attribute [local simp] and_imp_iff_and imp_and_iff_and

open MvPolynomial
namespace MonomialOrder
variable {σ : Type*} {m : MonomialOrder σ}

/- S-polynomial merged:
- https://github.com/leanprover-community/mathlib4/pull/32344,
- https://github.com/leanprover-community/mathlib4/pull/32788. -/

@[expose] public section

section misc

variable {R : Type*} [CommSemiring R] (f g : MvPolynomial σ R)

-- merged: https://github.com/leanprover-community/mathlib4/pull/34765
/--
@isnad1 id=eq.0h5v.s6.5e18b1a0fd9d from=translated src=- shape=c8386eb8 vocab=aa9c9c13
-/
@[deprecated (since := "2026-08-16")]
alias leadingCoeff_mul' := leadingCoeff_mul

-- merged: https://github.com/leanprover-community/mathlib4/pull/34758
/--
@isnad1 id=le.0h5v.s8.20674a85d63f from=translated src=- shape=0f86044a vocab=1ffd0c3f
-/
@[deprecated (since := "2026-08-16")]
alias degree_mul_le' := toSyn_degree_mul_le

/--
@isnad1 id=eq.2h9v.s10.38822e1cdb17 from=translated src=- shape=0c1cbb9d vocab=73049ed3
-/
lemma sPolynomial_monomial_mul_of_mem_nonZeroDivisors {R} [CommRing R]
    {p₁ p₂ : MvPolynomial σ R}
    (hp₁ : m.leadingCoeff p₁ ∈ nonZeroDivisors _)
    (hp₂ : m.leadingCoeff p₂ ∈ nonZeroDivisors _)
    (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0
  · (obtain rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul_of_right_mem_nonZeroDivisors hm1 hp₁,
    m.degree_mul_of_right_mem_nonZeroDivisors hm2 hp₂,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul_monomial,
    m.leadingCoeff_mul_of_right_mem_nonZeroDivisors hp₁,
    m.leadingCoeff_mul_of_right_mem_nonZeroDivisors hp₂,
    m.leadingCoeff_monomial, degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_eq_add_tsub le_sup_left, tsub_add_eq_add_tsub le_sup_right,
    add_comm d₁, add_comm d₂, add_tsub_add_eq_tsub_right, add_tsub_add_eq_tsub_right]

/--
@isnad1 id=eq.2h9v.s10.6925e3f3675e from=translated src=- shape=4237b139 vocab=18e2e516
-/
lemma sPolynomial_monomial_mul_of_mem_nonZeroDivisors' {R} [CommRing R]
    {p₁ p₂ : MvPolynomial σ R}
    (hp₁ : m.leadingCoeff p₁ ∈ nonZeroDivisors _)
    (hp₂ : m.leadingCoeff p₂ ∈ nonZeroDivisors _)
    (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial (monomial d₁ c₁ * p₁) (monomial d₂ c₂ * p₂) =
      monomial (m.degree (monomial d₁ c₁ * p₁) ⊔ m.degree (monomial d₂ c₂ * p₂) -
          m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0
  · (obtain rfl | rfl := H) <;> simp
  simp [H, hp₁, hp₂, degree_mul_of_right_mem_nonZeroDivisors,
    sPolynomial_monomial_mul_of_mem_nonZeroDivisors, degree_monomial]

/--
@isnad1 id=eq.1h5v.s7.9048055be1f6 from=translated src=- shape=be61792e vocab=8793bbf0
-/
lemma leadingCoeff_mul_of_left_mem_nonZeroDivisors' {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

/--
@isnad1 id=eq.1h5v.s7.8ed7c4c9b715 from=translated src=- shape=bac8e022 vocab=8793bbf0
-/
lemma leadingCoeff_mul_of_right_mem_nonZeroDivisors' {f g : MvPolynomial σ R}
    (hg : m.leadingCoeff g ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  simp only [leadingCoeff, degree_mul_of_right_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

/--
@isnad1 id=or.2h6v.s9.d9d428d810ee from=translated src=- shape=b5e2678f vocab=fbdb0bda
-/
lemma support_add_of_leadingTerm_add_leadingTerm_eq_zero
    {p q : MvPolynomial σ R}
    (h : m.leadingTerm p + m.leadingTerm q = 0) :
    ∀ a ∈ (p + q).support,
      (a ∈ p.support ∧ a ≺[m] m.degree p) ∨
      (a ∈ q.support ∧ a ≺[m] m.degree q) := by
  classical
  intro a ha
  wlog! +distrib hpq : p ≠ 0 ∧ q ≠ 0
  · rcases hpq with h' | h'
    · simp [h'] at h
      simp [h, h'] at ha
    · simp [h'] at h
      simp [h, h'] at ha
  unfold leadingTerm at h
  by_cases! hpq' : m.degree p ≠ m.degree q
  · apply congrArg (·.coeff (m.degree q)) at h
    simp [hpq', hpq] at h
  rw [hpq', ← map_add, monomial_eq_zero] at h
  unfold leadingCoeff at h
  rcases Finset.mem_union.mp <| support_add (p := p) (q := q) ha with h' | h'
  on_goal 1 => left
  on_goal 2 => right
  all_goals
    exists h'
    apply lt_of_le_of_ne (m.le_degree_of_mem_support h')
    by_contra!
    rw [m.toSyn.apply_eq_iff_eq] at this
    subst this
    simp [hpq' ▸ h, hpq'] at ha

-- @[simp]
-- lemma leadingTerm_neg {R} [CommRing R] (p : MvPolynomial σ R) :
--     m.leadingTerm (-p) = - m.leadingTerm p := by
--   simp [leadingTerm]

/--
@isnad1 id=or.2h6v.s9.2f9c004adb1c from=translated src=- shape=b114fc99 vocab=a9ea4cfa
-/
lemma support_sub_of_leadingTerm_eq_leadingTerm {R} [CommRing R]
    {p q : MvPolynomial σ R}
    (h : m.leadingTerm p = m.leadingTerm q) :
    ∀ a ∈ (p - q).support,
      (a ∈ p.support ∧ a ≺[m] m.degree p) ∨
      (a ∈ q.support ∧ a ≺[m] m.degree q) := by
  classical
  convert m.support_add_of_leadingTerm_add_leadingTerm_eq_zero (p := p) (q := -q) ?_
  · simp [-MvPolynomial.mem_support_iff, ← sub_eq_add_neg, degree_neg, support_neg]
  simp [h]

end misc

section killCompl

/--
@isnad1 id=le.1h6v.s9.448f97465531 from=translated src=- shape=6bb77dd7 vocab=cf4c9942
-/
lemma degree_rename_killCompl_le_degree {σ' R : Type*} [CommSemiring R]
    {f : σ' → σ} (hf : f.Injective) {p : MvPolynomial σ R} :
    m.degree ((p.killCompl hf).rename f) ≼[m] m.degree p :=
  m.degree_le_degree_of_support_subset (support_rename_killCompl_subset hf)

end killCompl

section WithBotDegree

section Semiring

variable {R : Type*} [CommSemiring R] (f g : MvPolynomial σ R)

/--
@isnad1 id=le.0h5v.s9.6e44b3a466a9 from=translated src=- shape=652a36fa vocab=48c78f81
-/
@[deprecated (since := "2026-08-16")]
alias withBotDegree_mul_le' := toWithBotSyn_withBotDegree_mul_le

/--
@isnad1 id=iff.0h5v.s7.88e3caff2b3b from=translated src=- shape=78ec4b97 vocab=0c904c44
-/
lemma withBotDegree_le_withBotDegree_iff' :
    m.withBotDegree f ≤ m.withBotDegree g ↔
      (m.degree f ≤ m.degree g ∧ (g = 0 → f = 0)) := by
  classical
  wlog! +distrib h : f ≠ 0 ∧ g ≠ 0
  · rcases h with h | h
    · simp [h]
    · simp_rw [h]
      aesop
  simp [m.withBotDegree_eq, h]

/--
@isnad1 id=le.1h6v.s9.3646711999f2 from=translated src=- shape=7499534e vocab=16b71fd9
-/
lemma withBotDegree_rename_killCompl_le_withBotDegree {σ'} {f : σ' → σ}
    (hf : f.Injective) (p : MvPolynomial σ R) :
    m.withBotDegree ((p.killCompl hf).rename f) ≼'[m] m.withBotDegree p :=
  m.withBotDegree_le_withBotDegree_of_support_subset (support_rename_killCompl_subset hf)

end Semiring

end WithBotDegree

end

end MonomialOrder
