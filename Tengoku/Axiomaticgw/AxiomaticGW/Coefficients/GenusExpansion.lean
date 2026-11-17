/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Coefficients.DescendantVariables
public import Tengoku.Seed.RingTheory.LaurentSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genus expansions and total free energies

The total free energy is Laurent-bounded below by `hbar^-1`. The exponential
total potential is intentionally absent because its powers need not have a
uniform lower bound in `hbar`.
-/

@[expose] public section

namespace AxiomaticGW

/-- One formal potential for each genus.-/
abbrev GenusPotential (A : Type*) := ℕ → A

/-- Assemble genus potentials with weights `hbar^(g-1)`.-/
noncomputable def totalFreeEnergy {A : Type*} [CommRing A]
    (F : GenusPotential A) : LaurentSeries A :=
  HahnSeries.single (-1) 1 *
    (PowerSeries.mk F : LaurentSeries A)

/-- The coefficient of `hbar^(g-1)` is exactly the genus-`g` potential.
@isnad1 id=eq.0h3v.s5.0ce0c1a7c6d7 from=translated src=- shape=2a2e9c70 vocab=d89f1796
-/
@[simp]
theorem totalFreeEnergy_coeff {A : Type*} [CommRing A]
    (F : GenusPotential A) (g : ℕ) :
    (totalFreeEnergy F).coeff ((g : ℤ) - 1) = F g := by
  rw [totalFreeEnergy, HahnSeries.coeff_single_mul]
  simp only [Int.reduceNeg, sub_neg_eq_add, sub_add_cancel,
    LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mk, one_mul]

/-- Descendant and ancestor genus potentials over the same Novikov and formal
variable completion.-/
structure GWPotentials {B : Type*} [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (Vars R : Type*) [CommRing R] where
  /-- Descendant potential in each genus.-/
  descendant : GenusPotential (FormalPotential D Vars R)
  /-- Ancestor potential in each genus.-/
  ancestor : GenusPotential (FormalPotential D Vars R)

namespace GWPotentials

variable {B Vars R : Type*} [AddCancelCommMonoid B]
  {D : EffectiveCurveMonoid B} [CommRing R]

/-- All-genus descendant free energy.-/
noncomputable def descendantFreeEnergy (F : GWPotentials D Vars R) :
    LaurentSeries (FormalPotential D Vars R) :=
  totalFreeEnergy F.descendant

/-- All-genus ancestor free energy.-/
noncomputable def ancestorFreeEnergy (F : GWPotentials D Vars R) :
    LaurentSeries (FormalPotential D Vars R) :=
  totalFreeEnergy F.ancestor

/--
@isnad1 id=eq.0h6v.s6.b6caa348c190 from=translated src=- shape=ec36ebf9 vocab=c1ab3314
-/
@[simp]
theorem descendantFreeEnergy_coeff (F : GWPotentials D Vars R) (g : ℕ) :
    F.descendantFreeEnergy.coeff ((g : ℤ) - 1) = F.descendant g :=
  totalFreeEnergy_coeff F.descendant g

/--
@isnad1 id=eq.0h6v.s6.808fd82ab250 from=translated src=- shape=ec36ebf9 vocab=ad3da44a
-/
@[simp]
theorem ancestorFreeEnergy_coeff (F : GWPotentials D Vars R) (g : ℕ) :
    F.ancestorFreeEnergy.coeff ((g : ℤ) - 1) = F.ancestor g :=
  totalFreeEnergy_coeff F.ancestor g

end GWPotentials

end AxiomaticGW
