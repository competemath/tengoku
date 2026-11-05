/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Closure.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ambient invariance of the relative algebraic closure

The opening line of the blueprint's descent proof (§9.1): the closure
relation on tuples from a subextension `N` is unchanged when computed in
the ambient field — `x ∈ racl k S` inside `N` iff `x ∈ racl k S` inside
`Ω`. Consequently the point geometry of `N/k` embeds in that of `Ω/k`.

The workhorse is the ambient-coefficient polynomial characterization of
closure membership, `mem_racl_iff_exists_poly`, which transports along the
inclusion `N.val` in both directions.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M5 descent, foundation).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Membership in `racl k S` via an ambient-coefficient annihilator: `x` is
in the closure iff some nonzero polynomial over `Ω` with coefficients in
`k(S)` vanishes at `x`.-/
theorem mem_racl_iff_exists_poly {S : Set Ω} {x : Ω} :
    x ∈ racl k S ↔ ∃ p : Polynomial Ω, p ≠ 0 ∧ p.eval x = 0 ∧
      ∀ n, p.coeff n ∈ adjoin k S := by
  constructor
  · intro hx
    obtain ⟨g, hg0, hgx⟩ := (mem_racl_iff k).1 hx
    refine ⟨g.map (algebraMap (adjoin k S) Ω), ?_, ?_, fun n ↦ ?_⟩
    · exact (Polynomial.map_ne_zero_iff
        (algebraMap (adjoin k S) Ω).injective).2 hg0
    · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hgx]
    · rw [Polynomial.coeff_map]
      exact (g.coeff n).2
  · rintro ⟨p, hp0, hpx, hpc⟩
    exact (mem_racl_iff k).2 (isAlgebraic_of_coeff_mem hp0 hpx hpc)

/-- **Ambient invariance of `racl`** (blueprint §9.1, opening line), in
embedding form: along any `k`-algebra embedding `ι : N →ₐ[k] Ω` of a
field `N`, closure membership is the same computed in `N` or in `Ω`.-/
theorem algHom_mem_racl_image_iff {N : Type*} [Field N] [Algebra k N]
    (ι : N →ₐ[k] Ω) {S : Set N} {x : N} :
    ι x ∈ racl k (⇑ι '' S) ↔ x ∈ racl k S := by
  have hinj : Function.Injective ι.toRingHom := ι.toRingHom.injective
  constructor
  · intro hx
    obtain ⟨p, hp0, hpx, hpc⟩ := mem_racl_iff_exists_poly.1 hx
    -- The coefficients lie in the image of `N`, so the annihilator lifts.
    have hadj : adjoin k (⇑ι '' S) = (adjoin k S).map ι :=
      (adjoin_map k S ι).symm
    have hN : ∀ n, p.coeff n ∈ Set.range ι.toRingHom := fun n ↦ by
      have h1 := hpc n
      rw [hadj] at h1
      obtain ⟨c₀, -, hc⟩ := h1
      exact ⟨c₀, hc⟩
    obtain ⟨q₀, hq₀⟩ := (Polynomial.mem_lifts (f := ι.toRingHom) p).1 <|
      (Polynomial.lifts_iff_coeff_lifts p).2 hN
    refine mem_racl_iff_exists_poly.2 ⟨q₀, ?_, ?_, fun n ↦ ?_⟩
    · intro h0
      rw [h0, Polynomial.map_zero] at hq₀
      exact hp0 hq₀.symm
    · have h1 : ι.toRingHom (q₀.eval x) = p.eval (ι x) := by
        rw [← hq₀, Polynomial.eval_map,
          show ι x = ι.toRingHom x from rfl, Polynomial.eval₂_at_apply]
      rw [hpx] at h1
      exact hinj (by rw [h1, map_zero])
    · have h1 : ι.toRingHom (q₀.coeff n) = p.coeff n := by
        rw [← hq₀, Polynomial.coeff_map]
      have h2 := hpc n
      rw [hadj] at h2
      obtain ⟨c₀, hc₀, hc⟩ := h2
      have h3 : c₀ = q₀.coeff n := hinj (hc.trans h1.symm)
      rwa [← h3]
  · intro hx
    obtain ⟨q₀, hq0, hqx, hqc⟩ :=
      (mem_racl_iff_exists_poly (S := S) (x := x)).1 hx
    refine mem_racl_iff_exists_poly.2
      ⟨q₀.map ι.toRingHom, ?_, ?_, fun n ↦ ?_⟩
    · exact (Polynomial.map_ne_zero_iff hinj).2 hq0
    · rw [Polynomial.eval_map, show ι x = ι.toRingHom x from rfl,
        Polynomial.eval₂_at_apply, hqx, map_zero]
    · rw [Polynomial.coeff_map]
      have h1 : ι.toRingHom (q₀.coeff n) ∈ (adjoin k S).map ι :=
        ⟨q₀.coeff n, hqc n, rfl⟩
      rwa [adjoin_map k S ι] at h1

/-- Equal relative algebraic closures of two generating sets remain equal
after embedding them in a larger ambient field.  This is weaker than
commuting `racl` with an embedding: the larger ambient field may contain
additional algebraic elements, but mutual algebraicity of the generators
is still preserved.-/
theorem algHom_racl_image_eq_of_racl_eq
    {N : Type*} [Field N] [Algebra k N]
    (ι : N →ₐ[k] Ω) {S T : Set N}
    (h : racl k S = racl k T) :
    racl k (⇑ι '' S) = racl k (⇑ι '' T) := by
  apply racl_congr_of_subset_racl
  · rintro _ ⟨x, hx, rfl⟩
    apply (algHom_mem_racl_image_iff ι).2
    rw [← h]
    exact subset_racl k S hx
  · rintro _ ⟨x, hx, rfl⟩
    apply (algHom_mem_racl_image_iff ι).2
    rw [h]
    exact subset_racl k T hx

/-- Ambient invariance in embedding form, singleton case.-/
theorem algHom_mem_racl_singleton_iff {N : Type*} [Field N] [Algebra k N]
    (ι : N →ₐ[k] Ω) {w x : N} :
    ι x ∈ racl k ({ι w} : Set Ω) ↔ x ∈ racl k ({w} : Set N) := by
  simpa [Set.image_singleton] using
    algHom_mem_racl_image_iff ι (S := ({w} : Set N)) (x := x)

/-- Equivariance of ambient closure membership along an embedding: a
`k`-automorphism of the source preserves interalgebraicity relations seen
through the embedding.-/
theorem algHom_mem_racl_singleton_map {N : Type*} [Field N] [Algebra k N]
    (ι : N →ₐ[k] Ω) (σ : N ≃ₐ[k] N) {z w : N}
    (h : ι z ∈ racl k ({ι w} : Set Ω)) :
    ι (σ z) ∈ racl k ({ι (σ w)} : Set Ω) := by
  rw [algHom_mem_racl_singleton_iff] at h ⊢
  simpa [Set.image_singleton] using mem_racl_map σ h

/-- **Base insensitivity of the closure** (blueprint §9.1: closures over
`k` and over `k̄` agree): enlarging the base field by elements algebraic
over it does not change `racl`.-/
theorem mem_racl_base_iff_of_algebraic {K₀ : IntermediateField k Ω}
    (halg : ∀ y ∈ K₀, IsAlgebraic k y) {S : Set Ω} {z : Ω} :
    z ∈ racl (↥K₀) S ↔ z ∈ racl k S := by
  constructor
  · intro hz
    -- Transport the annihilator to the `k`-closure of `↑K₀ ∪ S`, then
    -- absorb the algebraic generators.
    have h1 : IsAlgebraic (adjoin (↥K₀) S) z := (mem_racl_iff (↥K₀)).1 hz
    have h2 : z ∈ racl k ((K₀ : Set Ω) ∪ S) := by
      refine mem_racl_iff_exists_poly.2 ?_
      obtain ⟨p, hp0, hpz⟩ := h1
      refine ⟨p.map (algebraMap (adjoin (↥K₀) S) Ω),
        (Polynomial.map_ne_zero_iff
          (algebraMap (adjoin (↥K₀) S) Ω).injective).2 hp0,
        ?_, fun n ↦ ?_⟩
      · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hpz]
      · rw [Polynomial.coeff_map]
        have h3 : ((p.coeff n : ↥(adjoin (↥K₀) S)) : Ω) ∈
            (adjoin (↥K₀) S).restrictScalars k :=
          (mem_restrictScalars k).2 (p.coeff n).2
        rwa [restrictScalars_adjoin] at h3
    refine racl_le_of_subset_racl ?_ h2
    rintro y (hy | hy)
    · exact racl_mono (Set.empty_subset S)
        (mem_racl_empty_of_isAlgebraic (halg y hy))
    · exact subset_racl k S hy
  · intro hz
    exact racl_subset_racl_base K₀ S hz

/-- Pair independence is insensitive to algebraic base enlargement: an
independent pair over `k` stays independent over any subextension of
algebraic elements.-/
theorem algebraicIndependent_pair_base_of_algebraic
    {K₀ : IntermediateField k Ω} (halg : ∀ y ∈ K₀, IsAlgebraic k y)
    {x a : Ω} (hind : AlgebraicIndependent k ![x, a]) :
    AlgebraicIndependent (↥K₀) ![x, a] := by
  refine algebraicIndependent_pair ?_ ?_
  · rw [mem_racl_base_iff_of_algebraic halg]
    exact AlgebraicIndependent.notMem_racl_pair' hind
  · rw [mem_racl_base_iff_of_algebraic halg]
    exact AlgebraicIndependent.notMem_racl_pair hind

end

end AclGeom
