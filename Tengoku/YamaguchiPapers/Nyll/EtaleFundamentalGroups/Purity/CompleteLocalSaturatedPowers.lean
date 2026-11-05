/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.CompleteLocalChevalley
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.CompleteLocalSymbolicPowers
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.FinitePowerTorsionLength
import Tengoku.Seed.Algebra.Module.Torsion.PrimaryComponent
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.FiniteLength
import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.Tactic.Push

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal-ideal saturation of powers

Contracting the maximal-ideal-primary component of a quotient gives the
maximal-ideal saturation of its defining ideal. If an ideal lies in a
nonmaximal prime of a complete Noetherian local domain, its saturated
powers and ordinary powers are cofinal. The finite-length error module
is the maximal-ideal-primary component itself, so no coheight assumption
on the containing prime is required.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The maximal-ideal saturation of an ideal, contracted from the torsion
submodule of its quotient.-/
def maximalIdealSaturation (I : Ideal R) : Ideal R :=
  (Ideal.primaryComponent (R ⧸ I) (maximalIdeal R)).comap I.mkQ

/-- Saturation membership is annihilation modulo the ideal by some power
of the maximal ideal.-/
theorem mem_maximalIdealSaturation_iff (I : Ideal R) (x : R) :
    x ∈ maximalIdealSaturation I ↔
      ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, a * x ∈ I := by
  change I.mkQ x ∈ Ideal.primaryComponent (R ⧸ I) (maximalIdeal R) ↔ _
  rw [Ideal.primaryComponent_mem]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun a ha => ?_⟩
    apply (Submodule.Quotient.mk_eq_zero I).mp
    change I.mkQ (a • x) = 0
    rw [map_smul]
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := R ⧸ I)
      (s := ((maximalIdeal R ^ k : Ideal R) : Set R)) (I.mkQ x)).mp hk ⟨a, ha⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hk a a.property)

/-- Every ideal is contained in its saturation.-/
theorem le_maximalIdealSaturation (I : Ideal R) : I ≤ maximalIdealSaturation I := by
  intro x hx
  exact (mem_maximalIdealSaturation_iff I x).mpr
    ⟨0, fun a _ => I.mul_mem_left a hx⟩

/-- Saturation preserves inclusions of ideals.-/
theorem maximalIdealSaturation_mono : Monotone (maximalIdealSaturation (R := R)) := by
  intro I J hIJ x hx
  obtain ⟨k, hk⟩ := (mem_maximalIdealSaturation_iff I x).mp hx
  exact (mem_maximalIdealSaturation_iff J x).mpr ⟨k, fun a ha => hIJ (hk a ha)⟩

/-- The descending filtration obtained by saturating ordinary powers.-/
def maximalIdealSaturatedPower (I : Ideal R) (n : ℕ) : Ideal R :=
  maximalIdealSaturation (I ^ n)

/-- Ordinary powers are contained in their maximal-ideal saturations.-/
theorem pow_le_maximalIdealSaturatedPower (I : Ideal R) (n : ℕ) :
    I ^ n ≤ maximalIdealSaturatedPower I n :=
  le_maximalIdealSaturation (I ^ n)

/-- Saturated powers form a decreasing filtration.-/
theorem maximalIdealSaturatedPower_antitone (I : Ideal R) :
    Antitone (maximalIdealSaturatedPower I) := by
  intro n m hnm
  exact maximalIdealSaturation_mono (Ideal.pow_le_pow_right hnm)

/-- The error module introduced by saturation has finite length.-/
theorem isFiniteLength_primaryComponent_quotient
    [IsNoetherianRing R] (I : Ideal R) :
    IsFiniteLength R (Ideal.primaryComponent (R ⧸ I) (maximalIdeal R)) := by
  apply isFiniteLength_of_finite_of_maximalIdealPower_torsion
  intro z
  obtain ⟨k, hk⟩ := (Ideal.primaryComponent_mem
    (M := R ⧸ I) (I := maximalIdeal R) (z : R ⧸ I)).mp z.property
  refine ⟨k, fun a ha => ?_⟩
  apply Subtype.ext
  exact (Submodule.mem_torsionBySet_iff (R := R) (M := R ⧸ I)
    (s := ((maximalIdeal R ^ k : Ideal R) : Set R)) (z : R ⧸ I)).mp hk ⟨a, ha⟩

/-- A proper ideal whose radical is not the maximal ideal is contained
in a nonmaximal prime.-/
theorem exists_nonmaximal_prime_over_of_radical_ne
    (I : Ideal R) (hI : I ≠ ⊤) (hrad : I.radical ≠ maximalIdeal R) :
    ∃ P : Ideal R, I ≤ P ∧ P.IsPrime ∧ P ≠ maximalIdeal R := by
  classical
  by_contra h
  push Not at h
  apply hrad
  apply le_antisymm
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr (le_maximalIdeal hI)
  · rw [I.radical_eq_sInf]
    apply le_sInf
    intro P hP
    rw [h P hP.1 hP.2]

end EtaleFundamentalGroups.Purity

end
