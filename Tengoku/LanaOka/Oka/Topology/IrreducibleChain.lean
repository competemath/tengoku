/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.JacobsonSpace
import Tengoku.Seed.Topology.LocallyFinite
import Tengoku.Seed.Topology.NoetherianSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chains of irreducible components in connected Jacobson spaces

Let `X` be a connected Jacobson space whose irreducible components form a locally finite family
(e.g. `X` is locally Noetherian). Then any two closed points `x, y` of `X` are linked by a chain
`x = x₀, x₁, …, xₙ = y` of closed points such that consecutive points `xᵢ, xᵢ₊₁` lie in a
common irreducible component.

Proof: let `S` be the union of the irreducible components containing a closed point linked to
`x`. Its complement is the union of the remaining components, because the intersection of two
components is closed, hence contains a closed point as soon as it is nonempty. Both are locally
finite unions of closed sets, hence closed, so `S` is clopen and contains `x`, thus `S = X`.

## Main results

- `locallyFinite_irreducibleComponents`: if every point has an open neighbourhood which is a
  Noetherian space, the irreducible components form a locally finite family.
- `JacobsonSpace.reflTransGen_irreducibleComponents`: the chain lemma.
-/

open Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- If every point of `X` has an open neighbourhood which is a Noetherian topological space, then
the irreducible components of `X` form a locally finite family. -/
theorem locallyFinite_irreducibleComponents
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ NoetherianSpace U) :
    LocallyFinite (fun Z : irreducibleComponents X ↦ (Z : Set X)) := by
  intro x
  obtain ⟨U, hU, hxU, hN⟩ := h x
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  have hemb : IsOpenEmbedding (Subtype.val : U → X) := hU.isOpenEmbedding_subtypeVal
  let g : {Z : irreducibleComponents X | ((Z : Set X) ∩ U).Nonempty} →
      irreducibleComponents U := fun Z ↦
    ⟨Subtype.val ⁻¹' (Z : Set X), preimage_mem_irreducibleComponents Z.1.2 hemb
      (by rw [Subtype.range_coe]; exact Z.2)⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨Z, hZ⟩, hZU⟩ ⟨⟨Z', hZ'⟩, hZ'U⟩ hgg
    have hgg' : Subtype.val ⁻¹' Z = (Subtype.val ⁻¹' Z' : Set U) := congrArg Subtype.val hgg
    have e : ∀ W : Set X, W ∈ irreducibleComponents X → (W ∩ U).Nonempty →
        closure (Subtype.val '' (Subtype.val ⁻¹' W : Set U)) = W := fun W hW hWU ↦
      closure_image_preimage_of_isPreirreducible _ hemb.isOpenMap W
        (by obtain ⟨y, hy, hyU⟩ := hWU; exact ⟨⟨y, hyU⟩, hy⟩) hW.1.2
        (isClosed_of_mem_irreducibleComponents W hW)
    have : Z = Z' := by rw [← e Z hZ hZU, ← e Z' hZ' hZ'U, hgg']
    subst this
    rfl
  have : Finite (irreducibleComponents U) := NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

/-- **Chain lemma.** In a connected Jacobson space whose irreducible components are locally
finite, any two closed points are linked by a chain of closed points in which consecutive points
lie in a common irreducible component. -/
theorem JacobsonSpace.reflTransGen_irreducibleComponents [JacobsonSpace X] [ConnectedSpace X]
    (hfin : LocallyFinite (fun Z : irreducibleComponents X ↦ (Z : Set X))) {x y : X}
    (hx : IsClosed {x}) (hy : IsClosed {y}) :
    Relation.ReflTransGen (fun a b : X ↦ IsClosed {a} ∧ IsClosed {b} ∧
      ∃ Z ∈ irreducibleComponents X, a ∈ Z ∧ b ∈ Z) x y := by
  set R := fun a b : X ↦ IsClosed {a} ∧ IsClosed {b} ∧
    ∃ Z ∈ irreducibleComponents X, a ∈ Z ∧ b ∈ Z
  -- `P Z`: the component `Z` contains a closed point linked to `x`.
  let P : irreducibleComponents X → Prop := fun Z ↦
    ∃ c ∈ (Z : Set X), IsClosed {c} ∧ Relation.ReflTransGen R x c
  classical
  let S : Set X := ⋃ Z, if P Z then (Z : Set X) else ∅
  let T : Set X := ⋃ Z, if P Z then ∅ else (Z : Set X)
  have hSc : IsClosed S := by
    refine (hfin.subset fun Z ↦ ?_).isClosed_iUnion fun Z ↦ ?_
    · split_ifs <;> simp
    · split_ifs
      exacts [isClosed_of_mem_irreducibleComponents _ Z.2, isClosed_empty]
  have hTc : IsClosed T := by
    refine (hfin.subset fun Z ↦ ?_).isClosed_iUnion fun Z ↦ ?_
    · split_ifs <;> simp
    · split_ifs
      exacts [isClosed_empty, isClosed_of_mem_irreducibleComponents _ Z.2]
  have hmemS : ∀ z, z ∈ S ↔ ∃ Z : irreducibleComponents X, P Z ∧ z ∈ (Z : Set X) := by
    intro z
    simp only [S, Set.mem_iUnion]
    refine ⟨fun ⟨Z, hz⟩ ↦ ?_, fun ⟨Z, hP, hz⟩ ↦ ⟨Z, by rwa [ite_eq_left hP]⟩⟩
    split_ifs at hz with hP
    exacts [⟨Z, hP, hz⟩, absurd hz (Set.notMem_empty _)]
  have hmemT : ∀ z, z ∈ T ↔ ∃ Z : irreducibleComponents X, ¬ P Z ∧ z ∈ (Z : Set X) := by
    intro z
    simp only [T, Set.mem_iUnion]
    refine ⟨fun ⟨Z, hz⟩ ↦ ?_, fun ⟨Z, hP, hz⟩ ↦ ⟨Z, by rwa [ite_eq_right hP]⟩⟩
    split_ifs at hz with hP
    exacts [absurd hz (Set.notMem_empty _), ⟨Z, hP, hz⟩]
  have hcomp : ∀ z : X, ∃ Z : irreducibleComponents X, z ∈ (Z : Set X) := fun z ↦
    ⟨⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩,
      mem_irreducibleComponent⟩
  have hST : Sᶜ = T := by
    ext z
    rw [Set.mem_compl_iff, hmemS, hmemT]
    constructor
    · intro hz
      obtain ⟨Z, hZ⟩ := hcomp z
      exact ⟨Z, fun hP ↦ hz ⟨Z, hP, hZ⟩, hZ⟩
    · rintro ⟨Z', hP', hz'⟩ ⟨Z, ⟨c, hcZ, hc, hxc⟩, hz⟩
      obtain ⟨d, ⟨hdZ, hdZ'⟩, hd⟩ := nonempty_inter_closedPoints (X := X)
        (show ((Z : Set X) ∩ Z').Nonempty from ⟨z, hz, hz'⟩)
        ((isClosed_of_mem_irreducibleComponents _ Z.2).inter
          (isClosed_of_mem_irreducibleComponents _ Z'.2)).isLocallyClosed
      exact hP' ⟨d, hdZ', hd, hxc.tail ⟨hc, hd, Z, Z.2, hcZ, hdZ⟩⟩
  have hSo : IsOpen S := by
    rw [← isClosed_compl_iff, hST]
    exact hTc
  have hxS : x ∈ S := by
    obtain ⟨Z, hZ⟩ := hcomp x
    exact (hmemS x).2 ⟨Z, ⟨x, hZ, hx, .refl⟩, hZ⟩
  have hSuniv : S = Set.univ := (isClopen_iff.mp ⟨hSc, hSo⟩).resolve_left
    (Set.nonempty_iff_ne_empty.mp ⟨x, hxS⟩)
  obtain ⟨Z, ⟨c, hcZ, hc, hxc⟩, hyZ⟩ := (hmemS y).1 (by rw [hSuniv]; trivial)
  exact hxc.tail ⟨hc, hy, Z, Z.2, hcZ, hyZ⟩
