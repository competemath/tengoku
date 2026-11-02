/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Flat.EquationalCriterion
import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route E27: a regular element of `m_A R` cannot have a flat quotient

If `R` is an `A`-algebra, `I ⊂ A` a proper-extension ideal (`I R ≠ R`), `g ∈ I R` a non-zero-divisor
of `R` and `R / (g)` is flat over `A`, we get a contradiction.  (Equational criterion: the
relation `g = ∑ aᵢ rᵢ = 0` in `R/(g)` is trivial, and lifting it yields `g (1 - t) = 0` with
`t ∈ I R`.)  Used for `w ∉ j(P(D))`: `O_{P(D),q} = O_{P(B),w}/(g)` is `O_{X,v}`-flat and
`m_w = m_v O_w`.
-/
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry.Chow.M7
namespace E27

open Module

theorem false_of_flat_quotient_regular {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (I : Ideal A) (g : R) (hg : g ∈ I.map (algebraMap A R)) (hreg : IsSMulRegular R g)
    (hI : I.map (algebraMap A R) ≠ ⊤) (hflat : Module.Flat A (R ⧸ Ideal.span {g})) : False := by
  classical
  -- represent `g = ∑ aᵢ rᵢ` with `aᵢ ∈ I`
  have hg' : g ∈ Submodule.span R ((algebraMap A R) '' (I : Set A)) := by
    rw [Ideal.map] at hg
    exact hg
  obtain ⟨l, hl, hlg⟩ := (Finsupp.mem_span_image_iff_linearCombination R
    (v := algebraMap A R) (s := (I : Set A))).mp hg'
  set ι := l.support with hι
  let f : ι → A := fun i => (i : A)
  let x : ι → R ⧸ Ideal.span {g} := fun i => Ideal.Quotient.mk _ (l i)
  have hsum : ∑ i, f i • x i = 0 := by
    have h1 : ∑ i : ι, f i • x i = Ideal.Quotient.mk (Ideal.span {g}) (∑ i : ι, l i * algebraMap A R i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [f, x, Algebra.smul_def, map_mul]
      rw [mul_comm]
      rfl
    rw [h1]
    have h2 : ∑ i : ι, l i * algebraMap A R i = g := by
      rw [← hlg, Finsupp.linearCombination_apply, Finsupp.sum]
      simp only [smul_eq_mul]
      exact Finset.sum_coe_sort l.support (fun a => l a * algebraMap A R a)
    rw [h2]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)
  obtain ⟨k, a, y, hx, ha⟩ := (by haveI := hflat; exact Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) hsum)
  -- lift the `y j`
  choose ŷ hŷ using fun j => Ideal.Quotient.mk_surjective (y j)
  -- `l i - ∑ j, a i j • ŷ j ∈ (g)`
  have hc : ∀ i : ι, ∃ c : R, l i = ∑ j, algebraMap A R (a i j) * ŷ j + c * g := by
    intro i
    have h1 : Ideal.Quotient.mk (Ideal.span {g}) (l i - ∑ j, algebraMap A R (a i j) * ŷ j) = 0 := by
      rw [map_sub, map_sum]
      have := hx i
      simp only [x] at this
      rw [this]
      rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, ← hŷ j, map_mul]
      rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    exact ⟨c, by rw [hc]; ring⟩
  choose c hc using hc
  -- `g (1 - t) = 0`
  set t : R := ∑ i : ι, algebraMap A R (f i) * c i with ht
  have htI : t ∈ I.map (algebraMap A R) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hl i.2))
  have hgt : g = t * g := by
    have e1 : g = ∑ i : ι, l i * algebraMap A R (f i) := by
      rw [← hlg, Finsupp.linearCombination_apply, Finsupp.sum]
      simp only [smul_eq_mul, f]
      exact (Finset.sum_coe_sort l.support (fun a => l a * algebraMap A R a)).symm
    have e2 : ∑ i : ι, l i * algebraMap A R (f i) =
        ∑ i : ι, ∑ j, algebraMap A R (f i * a i j) * ŷ j + t * g := by
      have : ∀ i : ι, l i * algebraMap A R (f i) =
          ∑ j, algebraMap A R (f i * a i j) * ŷ j + (algebraMap A R (f i) * c i) * g := by
        intro i
        rw [hc i, add_mul, Finset.sum_mul]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]; ring
        · ring
      simp only [this, Finset.sum_add_distrib]
      rw [ht, Finset.sum_mul]
    have e3 : ∑ i : ι, ∑ j, algebraMap A R (f i * a i j) * ŷ j = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_mul, ← map_sum, ha j, map_zero, zero_mul]
    exact e1.trans (e2.trans (by rw [e3, zero_add]))
  have h1t : (1 - t) * g = 0 := by rw [sub_mul, one_mul, ← hgt, sub_self]
  have h1 : 1 - t = 0 := hreg (by simpa [mul_comm, smul_eq_mul] using h1t.trans (mul_zero g).symm)
  have : (1 : R) = t := sub_eq_zero.mp h1
  exact hI ((Ideal.eq_top_iff_one _).mpr (this ▸ htI))

end E27
end AlgebraicGeometry.Chow.M7
