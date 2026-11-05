/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Perfection.Lattice
import Tengoku.AclGeom.AclGeom.Closure.CrossBase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Naturality of chosen perfections

For arbitrary chosen perfections `π` of `K` and `ρ` of `L`, a field isomorphism `σ : K ≃+* L`
extends uniquely to `π.liftEquiv ρ σ : π.carrier ≃+* ρ.carrier` (Mathlib's
`IsPerfectClosure.equiv`).  The extension is functorial, carries perfected subfields to perfected
subfields (`σ(M^perf) = σ(M)^perf`), carries the perfected base `k^i` onto `l^i` when `σ` is
compatible with the bases, and intertwines the perfection order isomorphisms:
`σ(M^i) = σ(M)^i` (blueprint §Foundation III and §functorial formulation, (20.1)–(20.7)).  With
`σ` the identity, `liftEquiv` is the unique comparison `u_K` between two chosen perfections of `K`.

**Status:** the extension, uniqueness, groupoid laws and compatible-perfection naturality
are proved (#24 and the #10 carryover). The literal and Frobenius-quotient functors are proved in
`Functorial`; `Main` proves the public reconstruction theorem under the blueprint hypotheses.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Isomorphic fields have perfections with the same exponent.-/
theorem p_eq_of_ringEquiv (π : Perfection K) (ρ : Perfection L) (σ : K ≃+* L) : π.p = ρ.p := by
  have : ExpChar L π.p := expChar_of_injective_ringHom (f := σ.toRingHom) σ.injective π.p
  exact ExpChar.eq this ρ.expCharBase

/-- A ring isomorphism is `p`-radical.-/
theorem isPRadical_ringEquiv (σ : K ≃+* L) (p : ℕ) : IsPRadical σ.toRingHom p where
  pow_mem' x := ⟨0, σ.symm x, by simp⟩
  ker_le' x hx := by
    have hx0 : x = 0 := σ.injective (by simpa using hx)
    rw [hx0]
    exact Ideal.zero_mem _

variable (π : Perfection K) (ρ : Perfection L) (θ : Perfection M)

/-- The structure of a perfection of `L`, reindexed at the exponent of a perfection of an
isomorphic field.-/
theorem reindex (σ : K ≃+* L) :
    ∃ _ : ExpChar ρ.carrier π.p, ∃ _ : PerfectRing ρ.carrier π.p,
      IsPerfectClosure (ρ.incl.comp σ.toRingHom) π.p := by
  obtain ⟨h⟩ : Nonempty (π.p = ρ.p) := ⟨p_eq_of_ringEquiv π ρ σ⟩
  have e1 : ExpChar ρ.carrier π.p := h ▸ ρ.expCharCarrier
  have e2 : PerfectRing ρ.carrier π.p := by
    have := ρ.perfect
    convert this using 2
  have e3 : ExpChar L π.p := h ▸ ρ.expCharBase
  have e4 : IsPRadical ρ.incl π.p := by
    have := ρ.isPerfectClosure
    convert this using 2
  have := isPRadical_ringEquiv σ π.p
  exact ⟨e1, e2, IsPRadical.trans σ.toRingHom ρ.incl π.p⟩

/-- The isomorphism of chosen perfections extending a field isomorphism.-/
def liftEquiv (σ : K ≃+* L) : π.carrier ≃+* ρ.carrier :=
  haveI := (π.reindex ρ σ).1
  haveI := (π.reindex ρ σ).2.1
  haveI := (π.reindex ρ σ).2.2
  IsPerfectClosure.equiv π.incl (ρ.incl.comp σ.toRingHom) π.p

/-- The lift extends `σ` along the two inclusions.-/
@[simp] theorem liftEquiv_incl (σ : K ≃+* L) (x : K) :
    π.liftEquiv ρ σ (π.incl x) = ρ.incl (σ x) := by
  have := (π.reindex ρ σ).1
  have := (π.reindex ρ σ).2.1
  have := (π.reindex ρ σ).2.2
  exact IsPerfectClosure.equiv_comp_apply π.incl (ρ.incl.comp σ.toRingHom) π.p x

/-- Uniqueness: any ring map extending `σ` is the lift.-/
theorem liftEquiv_unique (σ : K ≃+* L) (f : π.carrier →+* ρ.carrier)
    (hf : ∀ x, f (π.incl x) = ρ.incl (σ x)) : f = (π.liftEquiv ρ σ).toRingHom := by
  have := (π.reindex ρ σ).1
  have := (π.reindex ρ σ).2.1
  have := (π.reindex ρ σ).2.2
  have hcomp : f.comp π.incl = ρ.incl.comp σ.toRingHom := RingHom.ext hf
  change f = (IsPerfectClosure.equiv π.incl (ρ.incl.comp σ.toRingHom) π.p).toRingHom
  rw [IsPerfectClosure.equiv_toRingHom, ← hcomp, PerfectRing.comp_lift]

/-- Extensionality: a ring isomorphism extending `σ` is the lift.-/
theorem liftEquiv_ext {σ : K ≃+* L} {e : π.carrier ≃+* ρ.carrier}
    (he : ∀ x, e (π.incl x) = ρ.incl (σ x)) : e = π.liftEquiv ρ σ :=
  RingEquiv.toRingHom_injective (π.liftEquiv_unique ρ σ e.toRingHom he)

/-- The lift of the identity is the identity.-/
theorem liftEquiv_refl : π.liftEquiv π (RingEquiv.refl K) = RingEquiv.refl _ :=
  (π.liftEquiv_ext π (σ := RingEquiv.refl K) (e := RingEquiv.refl _) fun _ ↦ rfl).symm

/-- Lifting is functorial: the lift of a composite is the composite of the lifts.-/
theorem liftEquiv_trans (σ : K ≃+* L) (τ : L ≃+* M) :
    π.liftEquiv θ (σ.trans τ) = (π.liftEquiv ρ σ).trans (ρ.liftEquiv θ τ) :=
  (π.liftEquiv_ext θ fun x ↦ by simp).symm

/-- The lift of the inverse is the inverse of the lift.-/
theorem liftEquiv_symm (σ : K ≃+* L) : (π.liftEquiv ρ σ).symm = ρ.liftEquiv π σ.symm :=
  ρ.liftEquiv_ext π fun x ↦ by
    rw [RingEquiv.symm_apply_eq, liftEquiv_incl, RingEquiv.apply_symm_apply]

/-- Perfected subfields are natural: `σ(M^perf) = σ(M)^perf`.-/
theorem perfSubfield_map (σ : K ≃+* L) (N : Subfield K) :
    (π.perfSubfield N).map (π.liftEquiv ρ σ).toRingHom =
      ρ.perfSubfield (N.map σ.toRingHom) := by
  have h := p_eq_of_ringEquiv π ρ σ
  ext y
  simp only [Subfield.mem_map, mem_perfSubfield_iff, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  constructor
  · rintro ⟨x, ⟨n, m, hm, hx⟩, rfl⟩
    refine ⟨n, σ m, ⟨m, hm, rfl⟩, ?_⟩
    rw [← h, ← map_pow, hx, liftEquiv_incl]
  · rintro ⟨n, _, ⟨m, hm, rfl⟩, hy⟩
    refine ⟨(π.liftEquiv ρ σ).symm y, ⟨n, m, hm, ?_⟩, by simp⟩
    apply (π.liftEquiv ρ σ).injective
    rw [map_pow, RingEquiv.apply_symm_apply, liftEquiv_incl, h, hy]

section Bases

variable {k l : Type*} [Field k] [Field l] [Algebra k K] [Algebra l L]

/-- A compatible field isomorphism carries the perfected base `k^i` onto `l^i`.-/
theorem basePerf_map {σ : K ≃+* L} (hσ : CrossBase.Compatible (k := k) (l := l) σ) :
    (π.basePerf k).map (π.liftEquiv ρ σ).toRingHom = ρ.basePerf l := by
  rw [basePerf, perfSubfield_map, basePerf]
  exact congrArg ρ.perfSubfield hσ

/-- The lift of a compatible isomorphism is compatible with the perfected bases.-/
theorem compatible_liftEquiv {σ : K ≃+* L} (hσ : CrossBase.Compatible (k := k) (l := l) σ) :
    CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) (π.liftEquiv ρ σ) := by
  unfold CrossBase.Compatible
  change (π.basePerf k).subtype.fieldRange.map _ = (ρ.basePerf l).subtype.fieldRange
  rw [Subfield.fieldRange_subtype, Subfield.fieldRange_subtype]
  exact π.basePerf_map ρ hσ

end Bases

end Perfection

end

end AclGeom
