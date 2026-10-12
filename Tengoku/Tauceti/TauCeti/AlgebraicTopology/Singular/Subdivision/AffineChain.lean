/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.Singular.Subdivision.Basic

/-!
# Affine chains in convex spaces

An affine `k`-chain in a convex space `E` is a formal integral combination of `(k + 1)`-tuples of
points of `E`, the vertex tuples of affine `k`-simplices. This file equips affine chains with the
simplicial boundary, the push-forward along maps, the cone from a point and the barycentric
subdivision, and pushes affine chains of the standard simplex `Δᵐ` forward along a singular
`m`-simplex to singular chains with coefficients in an object of a preadditive category.

These are the linear chains of Hatcher's proof of excision: operators on singular chains, such as
the prism operator of barycentric subdivision, are defined on the standard simplex as affine
chains and transported to singular chains along singular simplices.

## Main definitions and results

* `TauCeti.AffineChain.boundary`: the boundary of affine chains, with
  `TauCeti.AffineChain.boundary_boundary`: `∂ ∂ = 0`.
* `TauCeti.AffineChain.map`: the push-forward along a map of vertices.
* `TauCeti.AffineChain.cone`: the cone from a point `b`, with
  `TauCeti.AffineChain.boundary_cone`: `∂ (b · c) = c - b · ∂ c` in positive degrees.
* `TauCeti.AffineChain.subdivision`: the barycentric subdivision, which commutes with the boundary
  (`TauCeti.AffineChain.boundary_subdivision`) and with affine maps
  (`TauCeti.AffineChain.map_subdivision`).
* `TauCeti.AffineChain.singularChain`: the push-forward of affine chains of `Δᵐ` along a singular
  `m`-simplex, compatible with the boundary, faces, subdivision and continuous maps.
* `TauCeti.AffineChain.singularChain_subdivision`: pushing forward commutes with subdivision.
* `TauCeti.AffineChain.singularChain_subdivision_iterate`: pushing forward commutes with iterated
  subdivision.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, step (1).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial Equiv AlgebraicTopology Finsupp

universe w v u

namespace TauCeti

namespace AffineChain

variable {E F G : Type*}

variable (E) in
/-- The simplicial boundary of formal integral combinations of `(k + 1)`-tuples of vertices: the
alternating sum of the tuples obtained by deleting one vertex. -/
def boundary (k : ℕ) : ((Fin (k + 2) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 1) → E) →₀ ℤ) :=
  linearCombination ℤ fun v ↦ ∑ i : Fin (k + 2), single (v ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ))

@[simp]
lemma boundary_single {k : ℕ} (v : Fin (k + 2) → E) (a : ℤ) :
    boundary E k (single v a) =
      ∑ i : Fin (k + 2), single (v ∘ i.succAbove) (a * (-1 : ℤ) ^ (i : ℕ)) := by
  simp [boundary, Finset.smul_sum, smul_single]

private lemma succ_succAbove_comp_succAbove {k : ℕ} {i j : Fin (k + 2)} (h : i ≤ j) :
    j.succ.succAbove ∘ i.succAbove = i.castSucc.succAbove ∘ j.succAbove :=
  congrArg (fun f ↦ ⇑(SimplexCategory.Hom.toOrderHom f))
    (SimplexCategory.δ_comp_δ h)

/-- The boundary of a boundary vanishes. -/
lemma boundary_boundary (k : ℕ) : boundary E k ∘ₗ boundary E (k + 1) = 0 := by
  refine lhom_ext' fun v ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, boundary_single, map_sum,
    LinearMap.zero_apply, one_mul, Function.comp_assoc]
  -- The terms indexed by `(i, j)` with `j < i` cancel against those indexed by `(j, i - 1)`,
  -- by the simplicial identity `succ_succAbove_comp_succAbove`; `g` is this pairing.
  rw [← Finset.sum_product']
  let g : Fin (k + 3) × Fin (k + 2) → Fin (k + 3) × Fin (k + 2) := fun p ↦
    if h : p.2.castSucc < p.1 then (p.2.castSucc, p.1.pred (Fin.ne_zero_of_lt h))
    else (p.2.succ, p.1.castLT (by have := p.2.2; simp [Fin.lt_def] at h; omega))
  have hgg : ∀ p, g (g p) = p := by
    rintro ⟨a, b⟩
    by_cases h : b.castSucc < a
    · have h' : ¬ (a.pred (Fin.ne_zero_of_lt h)).castSucc < b.castSucc := by
        simp [Fin.lt_def] at h ⊢; omega
      simp [g, h, h']
    · have h' : (a.castLT (by have := b.2; simp [Fin.lt_def] at h; omega)).castSucc < b.succ := by
        simp [Fin.lt_def] at h ⊢; omega
      simp only [g, h, h', dite_true, dite_false]
      ext <;> simp
  have key : ∀ p : Fin (k + 3) × Fin (k + 2), p.2.castSucc < p.1 →
      single (v ∘ p.1.succAbove ∘ p.2.succAbove) ((-1 : ℤ) ^ (p.1 : ℕ) * (-1) ^ (p.2 : ℕ)) +
      single (v ∘ (g p).1.succAbove ∘ (g p).2.succAbove)
        ((-1 : ℤ) ^ ((g p).1 : ℕ) * (-1) ^ ((g p).2 : ℕ)) = 0 := by
    rintro ⟨a, b⟩ h
    obtain ⟨a, rfl⟩ := Fin.exists_succ_eq.2 (Fin.ne_zero_of_lt h)
    have hba : b ≤ a := Fin.castSucc_lt_succ_iff.1 h
    simp only [g, h, dite_true, Fin.pred_succ]
    rw [succ_succAbove_comp_succAbove hba, ← single_add, Fin.val_succ,
      Fin.val_castSucc, pow_succ]
    ring_nf
    exact single_zero _
  refine Finset.sum_involution (fun p _ ↦ g p) (fun p _ ↦ ?_) (fun p _ _ ↦ ?_)
    (fun _ _ ↦ Finset.mem_univ _) (fun p _ ↦ hgg p)
  · by_cases h : p.2.castSucc < p.1
    · exact key p h
    · have h' : (g p).2.castSucc < (g p).1 := by
        simp only [g, h, dite_false]; simp [Fin.lt_def] at h ⊢; omega
      have := key (g p) h'
      rw [hgg] at this
      exact (add_comm _ _).trans this
  · intro hp
    by_cases h : p.2.castSucc < p.1
    · have := congrArg Prod.fst hp
      simp only [g, h, dite_true] at this
      exact (this ▸ h).false
    · have := congrArg Prod.fst hp
      simp only [g, h, dite_false] at this
      exact h (this ▸ Fin.castSucc_lt_succ)

/-- The vertex tuples pushed forward along a map `f : E → F`. -/
def map (f : E → F) (k : ℕ) : ((Fin (k + 1) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 1) → F) →₀ ℤ) :=
  lmapDomain ℤ ℤ (f ∘ ·)

@[simp]
lemma map_single (f : E → F) {k : ℕ} (v : Fin (k + 1) → E) (a : ℤ) :
    map f k (single v a) = single (f ∘ v) a := by
  simp [map]

lemma map_comp (g : F → G) (f : E → F) (k : ℕ) : map (g ∘ f) k = map g k ∘ₗ map f k := by
  ext v
  simp [Function.comp_assoc]

@[simp]
lemma map_id (k : ℕ) : map (id : E → E) k = LinearMap.id := by
  ext v
  simp

/-- The cone from a vertex `b`: the vertex `b` is put in front of every vertex tuple. -/
def cone (b : E) (k : ℕ) : ((Fin (k + 1) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 2) → E) →₀ ℤ) :=
  lmapDomain ℤ ℤ fun v : Fin (k + 1) → E ↦ (Fin.cons b v : Fin (k + 2) → E)

@[simp]
lemma cone_single (b : E) {k : ℕ} (v : Fin (k + 1) → E) (a : ℤ) :
    cone b k (single v a) = single (Fin.cons b v) a := by
  simp [cone]

section Subdivision

variable [ConvexSpace ℝ E] [ConvexSpace ℝ F]

/-- The vertex tuple of the standard `k`-simplex, as an affine `k`-chain of the standard
`k`-simplex. -/
def simplex (k : ℕ) : (Fin (k + 1) → StdSimplex ℝ (Fin (k + 1))) →₀ ℤ :=
  single StdSimplex.single 1

end Subdivision

section Singular

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X Y : TopCat.{w}}

variable {R}

end Singular

end AffineChain

end TauCeti
