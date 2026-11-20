/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
public import Tengoku.Seed.RingTheory.KrullDimension.Field
public import Tengoku.Seed.RingTheory.KrullDimension.Regular
public import Tengoku.Seed.RingTheory.Regular.RegularSequence
public import Tengoku.Seed.LinearAlgebra.Dimension.OrzechProperty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Regular Local Ring is Domain

In this file, we prove that regular local ring is domain

# Main definition and results

* `isDomain_of_isRegularLocalRing` : a regular locla ring is domain

* `isRegular_of_span_eq_maximalIdeal` : for a regular local ring `R`, if a list of length equal to
  its dimension generates `maximalIdeal R`, it form a regular sequence.

-/

@[expose] public section
namespace Tengoku.ZanelloLc end Tengoku.ZanelloLc open Tengoku.ZanelloLc 
open IsLocalRing IsRegularLocalRing

variable (R : Type*) [CommRing R]

variable {R} in
/--
@isnad1 id=injectiv.0h3v.s7.fc494f5279f6 from=translated src=- shape=4a02d29c vocab=1f4489a6
-/
lemma IsLocalRing.ResidueField.map_injective [IsLocalRing R] {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    Function.Injective (ResidueField.map f) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  simpa only [map_eq_zero] using hx

variable {R} in
/--
@isnad1 id=bijectiv.1h3v.s8.487bd93629c0 from=translated src=- shape=d6d7e87b vocab=e1c1a778
-/
lemma IsLocalRing.ResidueField.map_bijective_of_surjective [IsLocalRing R] {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) (surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  refine ⟨ResidueField.map_injective f, ?_⟩
  unfold ResidueField.map
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact (Ideal.Quotient.mk_surjective (I := maximalIdeal S)).comp surj

/--
@isnad1 id=ex.0h1v.s4.d6bf901ef2a5 from=translated src=- shape=81131f7c vocab=9fd1cf2e
-/
lemma _root_.Tengoku.ZanelloLc.exist_nat_eq [FiniteRingKrullDim R] : ∃ n : ℕ, ringKrullDim R = n := by
  have : (ringKrullDim R).unbot ringKrullDim_ne_bot ≠ ⊤ := by
    by_contra eq
    rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
    exact ringKrullDim_ne_top eq
  use ((ringKrullDim R).unbot ringKrullDim_ne_bot).toNat
  exact (WithBot.coe_unbot (ringKrullDim R) ringKrullDim_ne_bot).symm.trans
    (WithBot.coe_inj.mpr (ENat.natCast_toNat this).symm)

end
-- Tengoku: root names of this library moved to Tengoku.ZanelloLc so they do not collide with other libraries (generated)
