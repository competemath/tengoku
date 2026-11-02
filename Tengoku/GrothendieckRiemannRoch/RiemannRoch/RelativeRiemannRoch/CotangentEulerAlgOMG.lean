/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts
import Tengoku.Seed.CategoryTheory.Limits.Shapes.Kernels
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# OMG: the chartwise split-kernel argument for the Euler sequence (abstract form)

A purely categorical statement: `ψ : Ω ⟶ B` into a "coordinate" object `B = ⊕_{j<m} L`, with
`d : B ⟶ Q` the Euler map `(s_j) ↦ ∑ x_j s_j`, such that the non-pivot components of `ψ`
(contractions) are the coframe of a free `Ω`, `x_a` is invertible, and the contractions satisfy
the Euler relation, has `ψ` as a kernel of `d`: `kernel.lift d ψ` is an isomorphism.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace SchemeProjectiveSpace
namespace OMG

section Split

variable {D : Type*} [Category D] [Preadditive D]

/-- **Split-kernel criterion.**-/
theorem isIso_kernelLift_of_split {A B Q : D} (ψ : A ⟶ B) (d : B ⟶ Q) (ρ : B ⟶ A)
    [HasKernel d] (hψd : ψ ≫ d = 0) (hψρ : ψ ≫ ρ = 𝟙 A)
    (hρ : ∀ {T : D} (f : T ⟶ B), f ≫ d = 0 → f ≫ ρ ≫ ψ = f) :
    IsIso (kernel.lift d ψ hψd) := by
  refine ⟨⟨kernel.ι d ≫ ρ, ?_, ?_⟩⟩
  · rw [← Category.assoc]
    have : kernel.lift d ψ hψd ≫ kernel.ι d = ψ := kernel.lift_ι _ _ _
    rw [this, hψρ]
  · apply (cancel_mono (kernel.ι d)).1
    rw [Category.assoc, Category.assoc, Category.id_comp, kernel.lift_ι]
    exact hρ (kernel.ι d) (kernel.condition d)

/-- Reindexing of the sum over the non-pivot coordinates.-/
theorem sum_range_split {M : Type*} [AddCommMonoid M] {I : Type*} [Fintype I] [DecidableEq I]
    (m a : ℕ) (ha : a < m) (e : I → ℕ) (he : ∀ k, e k < m) (hea : ∀ k, e k ≠ a)
    (hinj : Function.Injective e) (hsurj : ∀ j, j < m → j ≠ a → ∃ k, e k = j) (F : ℕ → M) :
    ∑ j ∈ Finset.range m, F j = F a + ∑ k : I, F (e k) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 ha)]
  congr 1
  have h : (Finset.range m).erase a = Finset.univ.image e := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hja, hjm⟩
      exact hsurj j hjm hja
    · rintro ⟨k, rfl⟩
      exact ⟨hea k, he k⟩
  rw [h, Finset.sum_image (fun x _ y _ h ↦ hinj h)]

/-- **Chartwise split kernel (abstract form).**-/
theorem isIso_kernelLift_chart {Om B Lm Lm' Q Un : D} {I : Type*} [Fintype I] [DecidableEq I]
    (m a : ℕ) (ha : a < m) (e : I → ℕ) (he : ∀ k, e k < m) (hea : ∀ k, e k ≠ a)
    (hinj : Function.Injective e) (hsurj : ∀ j, j < m → j ≠ a → ∃ k, e k = j)
    (pr : ℕ → (B ⟶ Lm)) (inj : ℕ → (Lm ⟶ B))
    (hsum : ∑ j ∈ Finset.range m, pr j ≫ inj j = 𝟙 B)
    (ψ : Om ⟶ B) (τ : Lm ≅ Un) (co : I → (Om ⟶ Un)) (fr : I → (Un ⟶ Om))
    (hfr : ∀ i j, fr i ≫ co j = if i = j then 𝟙 Un else 0)
    (hco : ∑ k, co k ≫ fr k = 𝟙 Om)
    (hbr : ∀ k, ψ ≫ pr (e k) ≫ τ.hom = co k)
    (x : ℕ → (Lm ⟶ Lm')) (heuler : ∑ j ∈ Finset.range m, (ψ ≫ pr j) ≫ x j = 0)
    (hxa : IsIso (x a))
    (d : B ⟶ Q) (w : Q ≅ Lm') (hd : d ≫ w.hom = ∑ j ∈ Finset.range m, pr j ≫ x j)
    [HasKernel d] (hψd : ψ ≫ d = 0) :
    IsIso (kernel.lift d ψ hψd) := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : B ⟶ Om, ρ = ∑ k, pr (e k) ≫ τ.hom ≫ fr k := ⟨_, rfl⟩
  have hA : ∀ k, ρ ≫ ψ ≫ pr (e k) = pr (e k) := by
    intro k
    have h1 : ψ ≫ pr (e k) = co k ≫ τ.inv := by
      rw [← hbr k]; simp
    rw [h1, hρdef, Preadditive.sum_comp]
    rw [Finset.sum_eq_single k]
    · rw [Category.assoc, Category.assoc, ← Category.assoc (fr k), hfr k k]
      simp
    · intro k' _ hk'
      rw [Category.assoc, Category.assoc, ← Category.assoc (fr k'), hfr k' k, ite_eq_right hk']
      simp
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hψρ : ψ ≫ ρ = 𝟙 Om := by
    calc ψ ≫ ρ = ∑ k, co k ≫ fr k := by
          rw [hρdef, Preadditive.comp_sum]
          refine Finset.sum_congr rfl (fun k _ ↦ ?_)
          rw [← hbr k]; simp only [Category.assoc]
      _ = 𝟙 Om := hco
  refine isIso_kernelLift_of_split ψ d ρ hψd hψρ (fun {T} f hf ↦ ?_)
  have hsumf : ∑ j ∈ Finset.range m, (f ≫ pr j) ≫ x j = 0 := by
    have h1 : f ≫ d ≫ w.hom = f ≫ ∑ j ∈ Finset.range m, pr j ≫ x j := by rw [hd]
    rw [← Category.assoc, hf, zero_comp, Preadditive.comp_sum] at h1
    simp only [← Category.assoc] at h1
    exact h1.symm
  rw [sum_range_split m a ha e he hea hinj hsurj] at hsumf heuler
  have key : ∀ i, i < m → (f ≫ ρ ≫ ψ) ≫ pr i = f ≫ pr i := by
    intro i hi
    by_cases hia : i = a
    · subst hia
      haveI := hxa
      refine (cancel_mono (x i)).1 ?_
      have h2 : (f ≫ ρ) ≫ ((ψ ≫ pr i) ≫ x i + ∑ k : I, (ψ ≫ pr (e k)) ≫ x (e k)) = 0 := by
        rw [heuler, comp_zero]
      rw [Preadditive.comp_add, Preadditive.comp_sum] at h2
      have h3 : ∀ k : I, (f ≫ ρ) ≫ (ψ ≫ pr (e k)) ≫ x (e k) = (f ≫ pr (e k)) ≫ x (e k) := by
        intro k
        calc (f ≫ ρ) ≫ (ψ ≫ pr (e k)) ≫ x (e k) = f ≫ (ρ ≫ ψ ≫ pr (e k)) ≫ x (e k) := by
              simp only [Category.assoc]
          _ = (f ≫ pr (e k)) ≫ x (e k) := by rw [hA k, Category.assoc]
      rw [Finset.sum_congr rfl (fun k _ ↦ h3 k)] at h2
      simp only [Category.assoc] at h2 hsumf ⊢
      have h4 := h2.trans hsumf.symm
      exact add_right_cancel h4
    · obtain ⟨k, rfl⟩ : ∃ k, e k = i := hsurj i hi hia
      rw [Category.assoc, Category.assoc ρ ψ, hA k]
  have hf' : f = ∑ j ∈ Finset.range m, (f ≫ pr j) ≫ inj j := by
    conv_lhs => rw [← Category.comp_id f, ← hsum]
    rw [Preadditive.comp_sum]
    simp only [Category.assoc]
  conv_rhs => rw [hf']
  conv_lhs => rw [← Category.comp_id (f ≫ ρ ≫ ψ), ← hsum]
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl (fun j hj ↦ ?_)
  rw [← Category.assoc, key j (Finset.mem_range.1 hj)]

end Split

end OMG
end SchemeProjectiveSpace
