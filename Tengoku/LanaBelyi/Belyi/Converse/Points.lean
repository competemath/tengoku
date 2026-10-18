/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.Seed.Analysis.Complex.Cardinality
import Tengoku.Seed.Algebra.Field.ULift
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.Classification
import Tengoku.Seed.RingTheory.Algebraic.Cardinality
import Tengoku.Seed.RingTheory.Jacobson.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Points of finitely generated algebras

Step (S4) of `references/converse-rie-design.md`.

## Main results

* `Belyi.Converse.nonempty_algHom_of_isAlgClosed`: a nontrivial finitely generated algebra over an
  algebraically closed field `k` has a `k`-point (Nullstellensatz).
* `Belyi.Converse.nonempty_ringHom_complex`: a field of characteristic zero algebraic over `ℚ`
  embeds into `ℂ`.
* `Belyi.Converse.countable_of_isAlgebraic_rat`: such a field is countable.
* `Belyi.Converse.exists_injective_algHom`: a finitely generated domain over a countable field `k`
  embeds into every uncountable algebraically closed field `Ω ⊇ k`.
* Instances `Uncountable ℂ`, `IsAlgClosed (ULift ℂ)`, so that the last result applies to
  `Ω := ULift ℂ`.
-/

universe u v

open Cardinal

namespace Belyi.Converse

/-- **Nullstellensatz**: a nontrivial finitely generated algebra over an algebraically closed field
has a rational point. -/
theorem nonempty_algHom_of_isAlgClosed (k : Type u) (A : Type v) [Field k] [IsAlgClosed k]
    [CommRing A] [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] :
    Nonempty (A →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)⟩

/-- A field of characteristic zero which is algebraic over `ℚ` embeds into `ℂ`. -/
theorem nonempty_ringHom_complex (k : Type u) [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] : Nonempty (k →+* ℂ) :=
  ⟨(IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom⟩

/-- A field of characteristic zero which is algebraic over `ℚ` is countable. -/
theorem countable_of_isAlgebraic_rat (k : Type u) [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] : Countable k := by
  rw [← Cardinal.mk_le_aleph0_iff]
  have := Algebra.IsAlgebraic.lift_cardinalMk_le_max ℚ k
  simpa using this

/-- Being algebraically closed transfers along ring isomorphisms between fields in possibly
different universes (`IsAlgClosed.of_ringEquiv` requires equal universes). -/
theorem isAlgClosed_of_ringEquiv {k : Type u} {k' : Type v} [Field k] [Field k']
    (e : k ≃+* k') [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : Polynomial.degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/-- An uncountable algebraically closed field over a countable field has an infinite transcendence
basis. -/
theorem infinite_of_isTranscendenceBasis {k Ω : Type u} [Field k] [Countable k] [Field Ω]
    [IsAlgClosed Ω] [Algebra k Ω] [Uncountable Ω] {t : Set Ω}
    (ht : IsTranscendenceBasis k ((↑) : t → Ω)) : Infinite t := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hle := IsAlgClosed.cardinal_le_max_transcendence_basis' _ ht
  have : #Ω ≤ ℵ₀ := hle.trans (by simp [Cardinal.mk_le_aleph0])
  exact not_countable (α := Ω) (Cardinal.mk_le_aleph0_iff.mp this)

end Belyi.Converse
