/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.Topology.Irreducible
import Tengoku.Seed.Topology.LocallyClosed
import Tengoku.Seed.Algebra.Group.End

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite actions with locally closed fibers on an irreducible point space

If left translations are homeomorphisms and a group is irreducible, any action with a
finite invariant orbit and locally closed orbit fibers fixes that orbit point. A finite
locally closed cover has an open member; translating that member gives an open stabilizer.
Intersecting two nonempty open translates forces every group element to stabilize the point.

Named consumer: the actual regular-action boundary theorem in `SchemePlaceFixed`. No joint
continuity of multiplication, abstract finite-index argument or characteristic hypothesis is used.

**Status:** proved; consumed by the actual connected regular-action fixed-boundary theorem.
-/

namespace AclGeom.FiniteAction

private theorem exists_open_of_finite_locallyClosed_cover {X ι : Type*}
    [TopologicalSpace X] [IrreducibleSpace X] (s : Finset ι) (F : ι → Set X)
    (hF : ∀ i ∈ s, IsLocallyClosed (F i)) (hcover : ∀ x, ∃ i ∈ s, x ∈ F i) :
    ∃ i ∈ s, IsOpen (F i) ∧ (F i).Nonempty := by
  classical
  let C := s.image fun i ↦ closure (F i)
  have hc : ∀ Z ∈ C, IsClosed Z := by
    intro Z hZ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hZ
    exact isClosed_closure
  have hcov : Set.univ ⊆ ⋃₀ (C : Set (Set X)) := by
    intro x _
    obtain ⟨i, hi, hxi⟩ := hcover x
    exact Set.mem_sUnion_of_mem (subset_closure hxi)
      (Finset.mem_image.2 ⟨i, hi, rfl⟩)
  obtain ⟨Z, hZ, hall⟩ := isIrreducible_iff_sUnion_isClosed.1
    (IrreducibleSpace.isIrreducible_univ X) C hc hcov
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hZ
  have hcl : closure (F i) = Set.univ := Set.univ_subset_iff.1 hall
  obtain ⟨U, Z, hU, hZ, he⟩ := hF i hi
  have hZu : Z = Set.univ := by
    apply Set.univ_subset_iff.1
    rw [← hcl]
    apply closure_minimal _ hZ
    rw [he]
    exact Set.inter_subset_right
  refine ⟨i, hi, ?_, ?_⟩
  · simpa only [he, hZu, Set.inter_univ] using hU
  · rw [← closure_nonempty_iff, hcl]
    exact Set.univ_nonempty

/-- A finite action with locally closed orbit fibers fixes its point on an irreducible
translation space. Named consumer: the actual affine-curve boundary in `SchemePlaceFixed`.
Only individual left translations are required to be homeomorphisms.
@isnad1 id=eq.4h7v.s8.7883bf5bb7e8 from=translated src=- shape=48c3c69c vocab=45e6efee
-/
theorem fixed_of_finite_locallyClosed_fibers {Γ α : Type*} [Group Γ] [TopologicalSpace Γ]
    [IrreducibleSpace Γ] (ρ : Γ →* Equiv.Perm α) (L : Γ → Γ ≃ₜ Γ)
    (hL : ∀ g h, L g h = g * h) (P : α) {B : Set α} (hB : B.Finite)
    (horbit : ∀ g, ρ g P ∈ B) (hfiber : ∀ Q ∈ B, IsLocallyClosed {g : Γ | ρ g P = Q})
    (g : Γ) : ρ g P = P := by
  classical
  obtain ⟨Q, _, hQopen, h, hh⟩ := exists_open_of_finite_locallyClosed_cover hB.toFinset
    (fun Q ↦ {x : Γ | ρ x P = Q})
    (fun Q hQ ↦ hfiber Q (hB.mem_toFinset.1 hQ))
    (fun x ↦ ⟨ρ x P, hB.mem_toFinset.2 (horbit x), rfl⟩)
  have hPopen : IsOpen {x : Γ | ρ x P = P} := by
    have he : (L h) ⁻¹' {x : Γ | ρ x P = Q} = {x : Γ | ρ x P = P} := by
      ext x
      change ρ (L h x) P = Q ↔ ρ x P = P
      rw [hL, ← hh, map_mul]
      change ρ h (ρ x P) = ρ h P ↔ ρ x P = P
      exact (ρ h).injective.eq_iff
    rw [← he]
    exact hQopen.preimage (L h).continuous
  have hpre : IsOpen ((L g) ⁻¹' {x : Γ | ρ x P = P}) :=
    hPopen.preimage (L g).continuous
  obtain ⟨x, hx, hgx⟩ := nonempty_preirreducible_inter hPopen hpre
    ⟨1, by simp⟩ ⟨g⁻¹, by simp [hL]⟩
  change ρ (L g x) P = P at hgx
  rw [hL, map_mul] at hgx
  change ρ g (ρ x P) = P at hgx
  rw [hx] at hgx
  exact hgx

end AclGeom.FiniteAction
