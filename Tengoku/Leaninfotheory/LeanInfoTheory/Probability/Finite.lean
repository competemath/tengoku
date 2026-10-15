/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku

/-!
# Finite real-mass lemmas for PMFs

This file adds small bridge lemmas from mathlib's `ENNReal`-valued `PMF`
masses to the real-valued finite sums used by Shannon entropy. The probability
object itself remains mathlib's `PMF`.
-/

namespace PMF

universe u v

open scoped BigOperators ENNReal

variable {α : Type u}

/-- Each atom of a `PMF` has nonnegative real mass.
@isnad1 id=le.0h3v.s4.2e6ac9dbf23e from=translated src=- shape=3edf1080 vocab=d262c41b
-/
theorem toReal_nonneg (p : PMF α) (a : α) : 0 <= (p a).toReal :=
  ENNReal.toReal_nonneg

/-- Each atom of a `PMF` has real mass at most one.
@isnad1 id=le.0h3v.s4.439f2d9dd929 from=translated src=- shape=514f9c5a vocab=d262c41b
-/
theorem toReal_le_one (p : PMF α) (a : α) : (p a).toReal <= 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one a)

/-- On a finite type, the real masses of a `PMF` sum to one.
@isnad1 id=eq.0h2v.s5.860e80102d13 from=translated src=- shape=821dc207 vocab=947d49fd
-/
theorem sum_toReal [Fintype α] (p : PMF α) : (∑ a, (p a).toReal) = 1 := by
  classical
  -- `ENNReal.toReal_sum` requires every finite summand to be different from `∞`.
  have hfinite : forall a, a ∈ (Finset.univ : Finset α) -> p a ≠ ∞ := by
    intro a _ha
    exact p.apply_ne_top a
  calc
    (∑ a, (p a).toReal) = (∑ a, p a).toReal := by
      simpa using
        (ENNReal.toReal_sum (s := Finset.univ) (f := fun a => p a) hfinite).symm
    _ = (1 : ENNReal).toReal := by
      -- A PMF has total `ENNReal` mass one; after the previous line we can convert that total.
      have hsum : (∑ a, p a) = (1 : ENNReal) := by
        simpa using p.tsum_coe
      rw [hsum]
    _ = 1 := by
      simp

/--
On a finite selector type, the real mass of a bind is the corresponding
finite weighted sum of real masses.
@isnad1 id=eq.0h5v.s6.9d6b61992455 from=translated src=- shape=6881cdf3 vocab=9e298f6d
-/
theorem bind_toReal_apply {α : Type u} {β : Type v} [Fintype α]
    (p : PMF α) (f : α -> PMF β) (b : β) :
    ((p.bind f) b).toReal =
      ∑ a, (p a).toReal * (f a b).toReal := by
  classical
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top b)

/--
The finite set of atoms to which a finite PMF assigns nonzero mass.

Its coercion to a set is `p.support`; this finset view is intended for finite
sums and support-cardinality arguments.
-/
noncomputable def supportFinset [Fintype α] (p : PMF α) : Finset α :=
  Finset.univ.filter fun a => p a ≠ 0

/-- Membership in `p.supportFinset` is membership in the set-valued PMF support.
@isnad1 id=iff.0h3v.s5.37d3e3415c92 from=translated src=- shape=ae4ae506 vocab=6d2e91eb
-/
@[simp]
theorem mem_supportFinset [Fintype α] (p : PMF α) (a : α) :
    a ∈ p.supportFinset ↔ a ∈ p.support := by
  simp [supportFinset, PMF.mem_support_iff]

/-- The finite support finset coerces to the set-valued PMF support.
@isnad1 id=eq.0h2v.s4.b0be98e4ab4c from=translated src=- shape=bc2b8d2b vocab=230dc051
-/
@[simp]
theorem coe_supportFinset [Fintype α] (p : PMF α) :
    (p.supportFinset : Set α) = p.support := by
  ext a
  simp

/-- The finite support finset has the set-theoretic support cardinality.
@isnad1 id=eq.0h2v.s4.0629ee268c12 from=translated src=- shape=1c8525c5 vocab=ac518922
-/
theorem supportFinset_card [Fintype α] (p : PMF α) :
    p.supportFinset.card = p.support.ncard := by
  rw [← Set.ncard_coe_finset, coe_supportFinset]

/-- The finite support finset of a PMF is nonempty.
@isnad1 id=nonempty.0h2v.s3.afdcd4cc4837 from=translated src=- shape=ed10201d vocab=e49cfc2d
-/
theorem supportFinset_nonempty [Fintype α] (p : PMF α) :
    p.supportFinset.Nonempty := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  exact ⟨a, (mem_supportFinset p a).2 ha⟩

/-- A PMF is pure at `a` exactly when its support is the singleton `{a}`. -/
theorem eq_pure_iff_support_eq_singleton (p : PMF α) (a : α) :
    p = PMF.pure a ↔ p.support = {a} := by
  constructor
  · intro h
    rw [h, PMF.support_pure]
  · intro h
    apply PMF.ext
    intro x
    by_cases hx : x = a
    · subst x
      rw [(p.apply_eq_one_iff a).2 h]
      simp
    · have hpx : p x = 0 := (p.apply_eq_zero_iff x).2 (by simpa [h] using hx)
      rw [hpx]
      simp [hx]

/--
If `f` is injective, pushing a PMF forward along `f` preserves the mass of each
source atom at its image.
@isnad1 id=eq.1h5v.s5.de275d3caf3c from=translated src=- shape=17680fe5 vocab=17c77a05
-/
theorem map_apply_of_injective {alpha : Type u} {beta : Type*}
    (p : PMF alpha) {f : alpha -> beta} (hf : Function.Injective f) (a : alpha) :
    p.map f (f a) = p a := by
  have hpre : f ⁻¹' ({f a} : Set beta) = ({a} : Set alpha) := by
    ext x
    constructor
    · intro hx
      exact hf (by simpa using hx)
    · intro hx
      rw [hx]
      rfl
  calc
    p.map f (f a) =
        (p.map f).toOuterMeasure ({f a} : Set beta) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := p.map f) (f a)).symm
    _ = p.toOuterMeasure (f ⁻¹' ({f a} : Set beta)) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure ({a} : Set alpha) := by
      rw [hpre]
    _ = p a := by
      exact PMF.toOuterMeasure_apply_singleton (p := p) a

/--
If a target atom is outside the range of a map, then the pushed-forward PMF
assigns zero mass to that atom.
@isnad1 id=eq.1h5v.s5.50311baaccbe from=translated src=- shape=3d1d5fc9 vocab=a78932c0
-/
theorem map_apply_eq_zero_of_notMem_range {alpha : Type u} {beta : Type*}
    (p : PMF alpha) {f : alpha -> beta} {b : beta} (hb : b ∉ Set.range f) :
    p.map f b = 0 := by
  have hpre : f ⁻¹' ({b} : Set beta) = (∅ : Set alpha) := by
    ext x
    constructor
    · intro hx
      exfalso
      exact hb ⟨x, by simpa using hx⟩
    · intro hx
      cases hx
  calc
    p.map f b =
        (p.map f).toOuterMeasure ({b} : Set beta) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := p.map f) b).symm
    _ = p.toOuterMeasure (f ⁻¹' ({b} : Set beta)) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure (∅ : Set alpha) := by
      rw [hpre]
    _ = 0 := by
      simp

/--
Pushing a PMF forward along an equivalence preserves the mass of each atom at
the renamed atom.
@isnad1 id=eq.0h5v.s6.45c64bda9179 from=translated src=- shape=cb800889 vocab=07e83c46
-/
theorem map_apply_equiv {alpha : Type u} {beta : Type*}
    (p : PMF alpha) (e : alpha ≃ beta) (a : alpha) :
    p.map e (e a) = p a :=
  map_apply_of_injective p e.injective a

end PMF
