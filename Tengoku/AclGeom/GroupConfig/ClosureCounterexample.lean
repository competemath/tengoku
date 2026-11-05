/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.GroupConfig.Constructible.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded-degree membership in the base field is not constructible

Blueprint `sources/group_configuration/10-descent.tex`, `rem:descent-limits`, refuted on #31.
The original remark asserted that, once a degree bound is fixed, statements `u ∈ acl(k, e, v)` are
constructible relations over `k` in the ambient tuples. This fails already for empty parameters
and degree bound one:

* the elements of `K` satisfying a nonzero polynomial over `k` of degree at most one are exactly
  the elements of `k` (`GroupConfig.setOf_exists_natDegree_le_one_aeval_eq_zero`);
* a subset of the line that is constructible over `k` is finite or cofinite
  (`GroupConfig.IsConstructibleOver.finite_or_finite_compl`);
* an infinite field `k` with an element `t ∈ K` outside it is neither finite nor cofinite in `K`,
  since `t + c ∉ k` for every `c ∈ k` (`GroupConfig.not_isConstructibleOver_range_algebraMap`).

Together: the degree-one membership relation is not constructible over `k`
(`GroupConfig.not_isConstructibleOver_setOf_exists_natDegree_le_one`).

The source setting satisfies these hypotheses: `k` is algebraically closed, hence infinite, and the
universal domain `K` has infinite transcendence degree over `k`. The coefficients of the witness
polynomials range over the subfield `k`; ambient quantification of coefficients does not
restrict them to `k`. The satisfaction of fixed witness formulas, with their coefficients and
nonvanishing conditions, is constructible; a degree bound alone cannot replace that choice.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the refutation of the uniform bounded-degree claim of `rem:descent-limits` is
complete.
-/

namespace GroupConfig

open Set

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A subset of the line that is constructible over `k` is finite or cofinite. Only this
implication holds in general: the singleton of an element transcendental over `k` is not
constructible over `k`. Named consumer: `GroupConfig.not_isConstructibleOver_range_algebraMap`.-/
theorem IsConstructibleOver.finite_or_finite_compl {s : Set (Fin 1 → K)}
    (hs : IsConstructibleOver k s) : s.Finite ∨ sᶜ.Finite := by
  classical
  obtain ⟨cells, hcells⟩ := isConstructibleOver_iff_exists_polynomial_data.1 hs
  -- Evaluation at a point of the line factors through one-variable polynomials.
  let φ : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k := MvPolynomial.aeval fun _ ↦ Polynomial.X
  have hφ (u : Fin 1 → K) (g : MvPolynomial (Fin 1) k) :
      MvPolynomial.aeval u g = Polynomial.aeval (u 0) (φ g) := by
    have h : (MvPolynomial.aeval u : MvPolynomial (Fin 1) k →ₐ[k] K) =
        (Polynomial.aeval (u 0)).comp φ := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      rw [Subsingleton.elim i 0]
      simp [φ]
    exact DFunLike.congr_fun h g
  -- A nonzero polynomial has finitely many roots on the line.
  have hroots (p : Polynomial k) (hp : p ≠ 0) :
      {u : Fin 1 → K | Polynomial.aeval (u 0) p = 0}.Finite := by
    refine ((p.rootSet_finite K).image fun x _ ↦ x).subset fun u hu ↦
      ⟨u 0, Polynomial.mem_rootSet.2 ⟨hp, hu⟩, funext fun i ↦ ?_⟩
    rw [Subsingleton.elim i 0]
  let Z : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin 1) k) → Set (Fin 1 → K) :=
    fun cell ↦ {u | (∀ i, MvPolynomial.aeval u (cell.g i) = 0) ∧ MvPolynomial.aeval u cell.f ≠ 0}
  -- Each cell is finite or cofinite.
  have hcell (cell) : (Z cell).Finite ∨ (Z cell)ᶜ.Finite := by
    by_cases hg : ∃ i, φ (cell.g i) ≠ 0
    · obtain ⟨i, hi⟩ := hg
      exact Or.inl ((hroots _ hi).subset fun u hu ↦ (hφ u _).symm.trans (hu.1 i))
    · push Not at hg
      by_cases hf : φ cell.f = 0
      · refine Or.inl (finite_empty.subset fun u hu ↦ hu.2 ?_)
        rw [hφ, hf, map_zero]
      · refine Or.inr ((hroots _ hf).subset fun u hu ↦ ?_)
        rw [mem_ofPred_eq, ← hφ]
        by_contra hne
        exact hu ⟨fun i ↦ by rw [hφ, hg i, map_zero], hne⟩
  have hs' : s = ⋃ cell ∈ (cells : Set _), Z cell := by
    ext u
    simp only [hcells, mem_iUnion, Finset.mem_coe, exists_prop, Z, mem_ofPred_eq]
  by_cases hall : ∀ cell ∈ (cells : Set _), (Z cell).Finite
  · rw [hs']
    exact Or.inl (cells.finite_toSet.biUnion hall)
  · push Not at hall
    obtain ⟨cell, hc, hinf⟩ := hall
    refine Or.inr (((hcell cell).resolve_left hinf).subset (compl_subset_compl.2 ?_))
    rw [hs']
    exact subset_biUnion_of_mem hc

/-- `rem:descent-limits` (refuted on #31): for an infinite field `k` and an element `t` of `K`
outside `k`, the elements of `k` do not form a constructible subset of the line over `k`.-/
theorem not_isConstructibleOver_range_algebraMap [Infinite k] {t : K}
    (ht : t ∉ range (algebraMap k K)) :
    ¬ IsConstructibleOver k {u : Fin 1 → K | u 0 ∈ range (algebraMap k K)} := by
  intro h
  let e : K → Fin 1 → K := fun x _ ↦ x
  have he : Function.Injective e := fun x y hxy ↦ congrFun hxy 0
  rcases h.finite_or_finite_compl with hfin | hfin
  · -- The base field is infinite.
    refine infinite_range_of_injective (he.comp (algebraMap k K).injective) (hfin.subset ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · -- Its complement contains every `t + c`.
    refine infinite_range_of_injective (f := fun c : k ↦ e (t + algebraMap k K c))
      (fun c d hcd ↦ (algebraMap k K).injective (add_left_cancel (he hcd))) (hfin.subset ?_)
    rintro _ ⟨c, rfl⟩ ⟨d, hd⟩
    change algebraMap k K d = t + algebraMap k K c at hd
    exact ht ⟨d - c, by rw [map_sub, hd, add_sub_cancel_right]⟩

/-- `rem:descent-limits`, degree bound one and empty parameters: the elements of `K` satisfying a
nonzero polynomial over `k` of degree at most one are exactly the elements of `k`.-/
theorem setOf_exists_natDegree_le_one_aeval_eq_zero :
    {u : Fin 1 → K | ∃ P : Polynomial k, P ≠ 0 ∧ P.natDegree ≤ 1 ∧ Polynomial.aeval (u 0) P = 0} =
      {u | u 0 ∈ range (algebraMap k K)} := by
  ext u
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨P, hP, hdeg, hu⟩
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg] at hP hu
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] at hu
    by_cases h1 : P.coeff 1 = 0
    · rw [h1, map_zero, zero_mul, zero_add] at hu
      rw [h1, map_zero, zero_mul, zero_add, ne_eq, Polynomial.C_eq_zero] at hP
      exact absurd ((algebraMap k K).injective (hu.trans (map_zero _).symm)) hP
    · refine ⟨-P.coeff 0 / P.coeff 1, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff ((map_ne_zero _).2 h1)]
      linear_combination -hu
  · rintro ⟨c, hc⟩
    refine ⟨Polynomial.X - Polynomial.C c, Polynomial.X_sub_C_ne_zero c,
      (Polynomial.natDegree_X_sub_C c).le, ?_⟩
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hc, sub_self]

/-- `rem:descent-limits` (refuted on #31), degree bound one and empty parameters: for an infinite
field `k` and an element `t` of `K` outside `k`, membership in `acl(k)` witnessed by a nonzero
polynomial over `k` of degree at most one is not a constructible relation over `k`.-/
theorem not_isConstructibleOver_setOf_exists_natDegree_le_one [Infinite k] {t : K}
    (ht : t ∉ range (algebraMap k K)) :
    ¬ IsConstructibleOver k {u : Fin 1 → K | ∃ P : Polynomial k, P ≠ 0 ∧ P.natDegree ≤ 1 ∧
      Polynomial.aeval (u 0) P = 0} := by
  rw [setOf_exists_natDegree_le_one_aeval_eq_zero]
  exact not_isConstructibleOver_range_algebraMap ht

end GroupConfig
