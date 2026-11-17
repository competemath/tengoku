/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Seed.Algebra.Order.Antidiag.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive locally finite effective curve classes

An additive energy models intersection with a chosen ample divisor. Positivity
and finite bounded-energy sets make every fixed curve-class splitting finite.
-/

@[expose] public section

namespace AxiomaticGW

/-- A cancellative monoid of effective numerical curve classes with a positive
additive energy and finite bounded-energy subsets.-/
structure EffectiveCurveMonoid (B : Type*) [AddCancelCommMonoid B] where
  /-- Energy, or degree with respect to a chosen polarization.-/
  energy : B →+ ℕ
  /-- Only the zero curve class has zero energy.-/
  energy_eq_zero_iff : ∀ beta, energy beta = 0 ↔ beta = 0
  /-- There are finitely many effective classes below every energy bound.-/
  finite_energy_le : ∀ d, {beta | energy beta ≤ d}.Finite

namespace EffectiveCurveMonoid

variable {B : Type*} [AddCancelCommMonoid B]

/-- The finite set of effective classes below an energy bound.-/
noncomputable def bounded (D : EffectiveCurveMonoid B) (d : ℕ) : Finset B :=
  (D.finite_energy_le d).toFinset

/--
@isnad1 id=iff.0h4v.s6.ab7088344a8b from=translated src=- shape=45e1cf20 vocab=363d4027
-/
@[simp]
theorem mem_bounded (D : EffectiveCurveMonoid B) (d : ℕ) (beta : B) :
    beta ∈ D.bounded d ↔ D.energy beta ≤ d := by
  simp only [bounded, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- All additive splittings of a fixed effective class.-/
noncomputable def splittings (D : EffectiveCurveMonoid B) (beta : B) :
    Finset (B × B) := by
  classical
  exact (D.bounded (D.energy beta) ×ˢ D.bounded (D.energy beta)).filter
    (fun pair ↦ pair.1 + pair.2 = beta)

/--
@isnad1 id=iff.0h5v.s6.bfa0d67726ac from=translated src=- shape=1db62fa6 vocab=3bfe3f8f
-/
@[simp]
theorem mem_splittings (D : EffectiveCurveMonoid B) (beta₁ beta₂ beta : B) :
    (beta₁, beta₂) ∈ D.splittings beta ↔ beta₁ + beta₂ = beta := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro hsum
    have henergy := congrArg D.energy hsum
    simp only [map_add] at henergy
    have h₁ : D.energy beta₁ ≤ D.energy beta := by omega
    have h₂ : D.energy beta₂ ≤ D.energy beta := by omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨(D.mem_bounded _ _).mpr h₁,
      (D.mem_bounded _ _).mpr h₂⟩, hsum⟩

/--
@isnad1 id=eq.0h2v.s6.c9d2242caccb from=translated src=- shape=7235820a vocab=734ea893
-/
@[simp]
theorem splittings_zero (D : EffectiveCurveMonoid B) :
    D.splittings 0 = {(0, 0)} := by
  classical
  ext pair
  rcases pair with ⟨beta₁, beta₂⟩
  simp only [D.mem_splittings, Finset.mem_singleton]
  constructor
  · intro hsum
    have henergy := congrArg D.energy hsum
    simp only [map_add, map_zero, Nat.add_eq_zero_iff] at henergy
    have h₁ : beta₁ = 0 := (D.energy_eq_zero_iff beta₁).mp henergy.1
    have h₂ : beta₂ = 0 := (D.energy_eq_zero_iff beta₂).mp henergy.2
    simp only [h₁, h₂]
  · intro h
    cases h
    simp only [add_zero]

/-- The energy hypothesis supplies mathlib's finite-antidiagonal interface.-/
@[reducible] noncomputable def hasAntidiagonal (D : EffectiveCurveMonoid B) :
    Finset.HasAntidiagonal B where
  antidiagonal := D.splittings
  mem_antidiagonal := by
    intro beta pair
    rcases pair with ⟨beta₁, beta₂⟩
    exact D.mem_splittings beta₁ beta₂ beta

/-- Natural-number degree is the basic positive locally finite curve monoid.-/
def nat : EffectiveCurveMonoid ℕ where
  energy := AddMonoidHom.id ℕ
  energy_eq_zero_iff := by simp only [AddMonoidHom.id_apply, implies_true]
  finite_energy_le := fun d ↦ by
    change {n : ℕ | n ≤ d}.Finite
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range (d + 1)))
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    change n ≤ d at hn
    exact Nat.lt_succ_of_le hn

/--
@isnad1 id=eq.0h1v.s5.ea6dfa4c9cb9 from=translated src=- shape=4c0d0bb5 vocab=18b3c629
-/
@[simp]
theorem nat_energy (d : ℕ) : nat.energy d = d := rfl

end EffectiveCurveMonoid

end AxiomaticGW
