import Tengoku.NsP23.P23.Semigroup.FourBaseBudget
import Tengoku.NsP23.P23.Semigroup.AperyQuotient
import Tengoku.Seed.Algebra.MvPolynomial.Basic
import Tengoku.Seed.Algebra.MvPolynomial.CommRing
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Connected
import Tengoku.Seed.RingTheory.Ideal.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genuine toric presentation of a four-generated numerical semigroup

All polynomial objects in this file are the actual four-variable polynomial
ring.  The toric ideal is defined as the kernel of the evaluation map.
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

open FourGeneratedNumericalSemigroup

variable {k : Type*} [Field k]

abbrev FourPoly (k : Type*) [Field k] := MvPolynomial (Fin 4) k

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

/-- The genuine four-variable map `X_i ↦ t^(n_i)`.-/
def semigroupPolyMap : FourPoly k →ₐ[k] SemigroupAlgebra (k := k) D :=
  MvPolynomial.aeval fun i => T (k := k) D (D.generator i)

private theorem generator_product (u : Fin 4 →₀ ℕ) :
    u.prod (fun i e => (T (k := k) D (D.generator i)) ^ e) =
      T (k := k) D ⟨D.weightedDegree u, (D.mem_Gamma_iff _).2 ⟨u, rfl⟩⟩ := by
  classical
  induction u using Finsupp.induction with
  | zero =>
      rw [show (⟨D.weightedDegree 0, (D.mem_Gamma_iff _).2 ⟨0, rfl⟩⟩ : D.Gamma) = 0 by
        apply Subtype.ext
        simp]
      exact T_zero D
  | @single_add i e u hi he ih =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      have hsingle :
          (Finsupp.single i e).prod (fun i e => (T (k := k) D (D.generator i)) ^ e) =
            T (k := k) D (e • D.generator i) := by
        simp [he, T, AddMonoidAlgebra.single_pow]
      rw [hsingle, ih]
      rw [T_add]
      apply congrArg (T (k := k) D)
      apply Subtype.ext
      simp [generator, weightedDegreeOf_add, weightedDegreeOf, Finsupp.single_apply,
        Finset.sum_eq_single i]

@[simp] theorem semigroupPolyMap_monomial (u : Fin 4 →₀ ℕ) (r : k) :
    D.semigroupPolyMap (MvPolynomial.monomial u r) =
      r • T (k := k) D ⟨D.weightedDegree u, (D.mem_Gamma_iff _).2 ⟨u, rfl⟩⟩ := by
  rw [semigroupPolyMap, MvPolynomial.aeval_monomial, D.generator_product]
  simp [Algebra.smul_def]

theorem semigroupPolyMap_surjective : Function.Surjective (D.semigroupPolyMap (k := k)) := by
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of s =>
      rcases (D.mem_Gamma_iff s.1).1 s.2 with ⟨u, hu⟩
      refine ⟨MvPolynomial.monomial u 1, ?_⟩
      rw [D.semigroupPolyMap_monomial]
      simp only [one_smul]
      apply congrArg (T (k := k) D)
      exact Subtype.ext hu
  | add x y hx hy =>
      rcases hx with ⟨p, rfl⟩
      rcases hy with ⟨q, rfl⟩
      exact ⟨p + q, map_add _ _ _⟩
  | smul r x hx =>
      rcases hx with ⟨p, rfl⟩
      exact ⟨r • p, map_smul _ _ _⟩

/-- The toric ideal, independently defined as the kernel of the genuine map.-/
def toricIdeal : Ideal (FourPoly k) :=
  RingHom.ker (D.semigroupPolyMap (k := k)).toRingHom

/-- The polynomial monomial represented by a factorization vertex.-/
def fiberMonomial {d : ℕ} (u : D.FactorizationAt d) : FourPoly k :=
  MvPolynomial.monomial u.1 1

/-- The binomial difference between two vertices of one factorization fiber.-/
def fiberBinomial {d : ℕ} (u v : D.FactorizationAt d) : FourPoly k :=
  D.fiberMonomial (k := k) u - D.fiberMonomial (k := k) v

@[simp] theorem semigroupPolyMap_fiberMonomial {d : ℕ} (u : D.FactorizationAt d) :
    D.semigroupPolyMap (D.fiberMonomial (k := k) u) =
      T (k := k) D ⟨d, (D.mem_Gamma_iff _).2 ⟨u.1, D.factorizationAt_degree u⟩⟩ := by
  rw [fiberMonomial, D.semigroupPolyMap_monomial]
  simp only [one_smul]
  apply congrArg (T (k := k) D)
  exact Subtype.ext (D.factorizationAt_degree u)

theorem fiberBinomial_mem_toricIdeal {d : ℕ} (u v : D.FactorizationAt d) :
    D.fiberBinomial (k := k) u v ∈ D.toricIdeal (k := k) := by
  change D.semigroupPolyMap (D.fiberBinomial (k := k) u v) = 0
  simp [fiberBinomial]

@[simp] theorem fiberBinomial_self {d : ℕ} (u : D.FactorizationAt d) :
    D.fiberBinomial (k := k) u u = 0 := by simp [fiberBinomial]

theorem fiberBinomial_swap {d : ℕ} (u v : D.FactorizationAt d) :
    D.fiberBinomial (k := k) u v = -D.fiberBinomial (k := k) v u := by
  simp [fiberBinomial, sub_eq_add_neg, add_comm]

theorem fiberBinomial_add {d : ℕ} (u v w : D.FactorizationAt d) :
    D.fiberBinomial (k := k) u v + D.fiberBinomial (k := k) v w =
      D.fiberBinomial (k := k) u w := by
  simp [fiberBinomial]

/-- All genuine same-fiber binomials.-/
def fiberBinomialSet : Set (FourPoly k) :=
  {p | ∃ (d : ℕ) (u v : D.FactorizationAt d), p = D.fiberBinomial (k := k) u v}

theorem span_fiberBinomials_le_toricIdeal :
    Ideal.span (D.fiberBinomialSet (k := k)) ≤ D.toricIdeal (k := k) := by
  rw [Ideal.span_le]
  rintro p ⟨d, u, v, rfl⟩
  exact D.fiberBinomial_mem_toricIdeal u v

/-- Any exponent vector is canonically a vertex in its own weighted fiber.-/
def exponentFactorization (u : Fin 4 →₀ ℕ) : D.FactorizationAt (D.weightedDegree u) :=
  ⟨u, D.mem_factorizations.mpr rfl⟩

/-- Coefficient of the semigroup monomial of degree `weightedDegree u₀` after
evaluation.  It is exactly the sum of source coefficients in that fiber.-/
theorem coeff_semigroupPolyMap (p : FourPoly k) (u₀ : Fin 4 →₀ ℕ) :
    (D.semigroupPolyMap p).coeff
        ⟨D.weightedDegree u₀, (D.mem_Gamma_iff _).2 ⟨u₀, rfl⟩⟩ =
      ∑ u ∈ p.support with D.weightedDegree u = D.weightedDegree u₀,
        MvPolynomial.coeff u p := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum, D.semigroupPolyMap_monomial, T, Finset.sum_apply,
    Finset.smul_sum]
  simp [Finsupp.single_apply, Subtype.ext_iff, Finset.sum_filter]

private theorem exists_other_same_degree_of_mem_toricIdeal
    {p : FourPoly k} (hp : p ∈ D.toricIdeal (k := k))
    {u : Fin 4 →₀ ℕ} (hu : u ∈ p.support) :
    ∃ v ∈ p.support, D.weightedDegree v = D.weightedDegree u ∧ v ≠ u := by
  classical
  have hsum :
      (∑ v ∈ p.support with D.weightedDegree v = D.weightedDegree u,
        MvPolynomial.coeff v p) = 0 := by
    change D.semigroupPolyMap p = 0 at hp
    have h := congrArg
      (fun f : SemigroupAlgebra (k := k) D =>
        f.coeff ⟨D.weightedDegree u, (D.mem_Gamma_iff _).2 ⟨u, rfl⟩⟩) hp
    rw [D.coeff_semigroupPolyMap] at h
    simpa using h
  by_contra h
  push_neg at h
  have hfilter :
      p.support.filter (fun v => D.weightedDegree v = D.weightedDegree u) = {u} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hdeg⟩
      by_contra hvu
      exact hvu (h v hv hdeg)
    · rintro rfl
      exact ⟨hu, rfl⟩
  rw [hfilter] at hsum
  simp only [Finset.sum_singleton] at hsum
  exact (MvPolynomial.mem_support_iff.mp hu) hsum

/-- Every element of the independently defined kernel is generated by genuine
same-fiber binomials.  The proof removes one support monomial at a time; the
kernel coefficient equation supplies a second monomial in the same fiber.-/
theorem mem_span_fiberBinomials_of_mem_toricIdeal
    (p : FourPoly k) (hp : p ∈ D.toricIdeal (k := k)) :
    p ∈ Ideal.span (D.fiberBinomialSet (k := k)) := by
  classical
  by_cases hp0 : p = 0
  · simpa [hp0]
  have hsupp : p.support.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr fun h =>
      hp0 (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨u, hu⟩ := hsupp
  obtain ⟨v, hv, hdeg, hvu⟩ :=
    D.exists_other_same_degree_of_mem_toricIdeal hp hu
  let fu : D.FactorizationAt (D.weightedDegree u) := D.exponentFactorization u
  let fv : D.FactorizationAt (D.weightedDegree u) :=
    ⟨v, D.mem_factorizations.mpr hdeg⟩
  let c := MvPolynomial.coeff u p
  let q := p - (MvPolynomial.monomial u c - MvPolynomial.monomial v c)
  have hqker : q ∈ D.toricIdeal (k := k) := by
    apply Ideal.sub_mem _ hp
    have hb := D.fiberBinomial_mem_toricIdeal (k := k) fu fv
    have hscaled : c • D.fiberBinomial (k := k) fu fv ∈ D.toricIdeal (k := k) := by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hb
    simpa [q, fu, fv, c, fiberBinomial, fiberMonomial, exponentFactorization, smul_sub,
      MvPolynomial.smul_monomial, smul_eq_mul] using hscaled
  have hsubset : q.support ⊆ p.support.erase u := by
    intro x hx
    have hraw := MvPolynomial.support_sub_monomial_sub_monomial_subset
      p u v c hvu.symm (by rfl) hx
    rcases Finset.mem_union.mp hraw with hx' | hxv
    · exact hx'
    · have hxv' : x = v := Finset.mem_singleton.mp hxv
      subst x
      exact Finset.mem_erase.mpr ⟨hvu, hv⟩
  have hcard : q.support.card < p.support.card :=
    lt_of_le_of_lt (Finset.card_le_card hsubset) (Finset.card_erase_lt_of_mem hu)
  have hqspan := mem_span_fiberBinomials_of_mem_toricIdeal q hqker
  have hbspan : D.fiberBinomial (k := k) fu fv ∈
      Ideal.span (D.fiberBinomialSet (k := k)) := by
    apply Ideal.subset_span
    exact ⟨D.weightedDegree u, fu, fv, rfl⟩
  have hscaled : c • D.fiberBinomial (k := k) fu fv ∈
      Ideal.span (D.fiberBinomialSet (k := k)) := by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hbspan
  have hbin : MvPolynomial.monomial u c - MvPolynomial.monomial v c ∈
      Ideal.span (D.fiberBinomialSet (k := k)) := by
    simpa [fu, fv, c, fiberBinomial, fiberMonomial, exponentFactorization, smul_sub,
      MvPolynomial.smul_monomial, smul_eq_mul] using hscaled
  have hpq : p = q + (MvPolynomial.monomial u c - MvPolynomial.monomial v c) := by
    simp [q]
  rw [hpq]
  exact Ideal.add_mem _ hqspan hbin
termination_by p.support.card
decreasing_by exact hcard

/-- Exact kernel presentation by all same-fiber binomials.-/
theorem toricIdeal_eq_span_fiberBinomials :
    D.toricIdeal (k := k) = Ideal.span (D.fiberBinomialSet (k := k)) := by
  apply le_antisymm
  · intro p hp
    exact D.mem_span_fiberBinomials_of_mem_toricIdeal p hp
  · exact D.span_fiberBinomials_le_toricIdeal

/-- Binomial consequences generated in strictly smaller weighted degree.-/
def lowerToricIdeal (d : ℕ) : Ideal (FourPoly k) :=
  Ideal.span {p | ∃ (e : ℕ) (_ : e < d) (u v : D.FactorizationAt e),
    p = D.fiberBinomial (k := k) u v}

theorem lowerToricIdeal_mono {e d : ℕ} (hed : e ≤ d) :
    D.lowerToricIdeal (k := k) e ≤ D.lowerToricIdeal (k := k) d := by
  unfold lowerToricIdeal
  rw [Ideal.span_le]
  rintro p ⟨f, hfe, u, v, rfl⟩
  apply Ideal.subset_span
  exact ⟨f, lt_of_lt_of_le hfe hed, u, v, rfl⟩

theorem lowerToricIdeal_le_toricIdeal (d : ℕ) :
    D.lowerToricIdeal (k := k) d ≤ D.toricIdeal (k := k) := by
  unfold lowerToricIdeal
  rw [Ideal.span_le]
  rintro p ⟨e, he, u, v, rfl⟩
  exact D.fiberBinomial_mem_toricIdeal u v

/-- Remove one occurrence of a common variable from a factorization.-/
def removeFactor (_D : FourGeneratedNumericalSemigroup)
    (u : Fin 4 →₀ ℕ) (j : Fin 4) : Fin 4 →₀ ℕ :=
  u - Finsupp.single j 1

theorem removeFactor_add_single {u : Fin 4 →₀ ℕ} {j : Fin 4} (hj : 0 < u j) :
    D.removeFactor u j + Finsupp.single j 1 = u := by
  exact Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hj)

theorem weightedDegree_removeFactor {u : Fin 4 →₀ ℕ} {j : Fin 4} (hj : 0 < u j) :
    D.weightedDegree (D.removeFactor u j) + D.n j = D.weightedDegree u := by
  have h := congrArg D.weightedDegree (D.removeFactor_add_single hj)
  simpa [weightedDegreeOf_add, D.weightedDegree_single] using h

/-- Lower-degree vertex obtained by cancelling one common variable.-/
def lowerFactorization {d : ℕ} (u : D.FactorizationAt d) (j : Fin 4)
    (hj : 0 < u.1 j) : D.FactorizationAt (d - D.n j) := by
  refine ⟨D.removeFactor u.1 j, D.mem_factorizations.mpr ?_⟩
  have hdeg := D.weightedDegree_removeFactor hj
  rw [D.factorizationAt_degree u] at hdeg
  omega

theorem lowerFactorization_degree_lt {d : ℕ} (u : D.FactorizationAt d)
    (j : Fin 4) (hj : 0 < u.1 j) : d - D.n j < d := by
  have hweight := D.weightedDegree_removeFactor hj
  rw [D.factorizationAt_degree u] at hweight
  have hn := D.positive j
  omega

theorem fiberMonomial_remove_mul {d : ℕ} (u : D.FactorizationAt d)
    (j : Fin 4) (hj : 0 < u.1 j) :
    MvPolynomial.X j * D.fiberMonomial (k := k) (D.lowerFactorization u j hj) =
      D.fiberMonomial (k := k) u := by
  rw [fiberMonomial, fiberMonomial, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  simp only [one_mul]
  change MvPolynomial.monomial (Finsupp.single j 1 + D.removeFactor u.1 j) 1 = _
  rw [show Finsupp.single j 1 + D.removeFactor u.1 j = u.1 by
    rw [add_comm, D.removeFactor_add_single hj]]

theorem fiberBinomial_remove_mul {d : ℕ} (u v : D.FactorizationAt d)
    (j : Fin 4) (hu : 0 < u.1 j) (hv : 0 < v.1 j) :
    MvPolynomial.X j * D.fiberBinomial (k := k)
      (D.lowerFactorization u j hu) (D.lowerFactorization v j hv) =
      D.fiberBinomial (k := k) u v := by
  simp only [fiberBinomial, mul_sub]
  rw [D.fiberMonomial_remove_mul u j hu, D.fiberMonomial_remove_mul v j hv]

theorem fiberBinomial_mem_lower_of_overlap {d : ℕ} (u v : D.FactorizationAt d)
    (h : D.FactorizationOverlap u v) :
    D.fiberBinomial (k := k) u v ∈ D.lowerToricIdeal (k := k) d := by
  rcases h with ⟨j, hu, hv⟩
  rw [← D.fiberBinomial_remove_mul u v j hu hv]
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  exact ⟨d - D.n j, D.lowerFactorization_degree_lt u j hu,
    D.lowerFactorization u j hu, D.lowerFactorization v j hv, rfl⟩

theorem fiberBinomial_mem_lower_of_adj {d : ℕ} {u v : D.FactorizationAt d}
    (h : (D.factorizationGraph d).Adj u v) :
    D.fiberBinomial (k := k) u v ∈ D.lowerToricIdeal (k := k) d :=
  D.fiberBinomial_mem_lower_of_overlap u v ((D.factorizationGraph_adj u v).mp h).2

theorem fiberBinomial_mem_lower_of_reachable {d : ℕ} {u v : D.FactorizationAt d}
    (h : (D.factorizationGraph d).Reachable u v) :
    D.fiberBinomial (k := k) u v ∈ D.lowerToricIdeal (k := k) d := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => simp
  | tail hreach hadj ih =>
      rw [← D.fiberBinomial_add]
      exact Ideal.add_mem _ ih (D.fiberBinomial_mem_lower_of_adj hadj)

theorem fiberBinomial_mem_lower_of_sameComponent {d : ℕ} {u v : D.FactorizationAt d}
    (h : D.componentOf u = D.componentOf v) :
    D.fiberBinomial (k := k) u v ∈ D.lowerToricIdeal (k := k) d :=
  D.fiberBinomial_mem_lower_of_reachable ((D.componentOf_eq_iff_reachable u v).mp h)

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
