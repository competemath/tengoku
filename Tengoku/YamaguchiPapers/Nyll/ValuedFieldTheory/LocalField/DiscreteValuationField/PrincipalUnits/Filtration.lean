/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
import Tengoku.Seed.Algebra.CharP.Lemmas
import Tengoku.Seed.Algebra.Group.Units.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal-unit filtration from a valuation ring

For a complete DVF `F`, the concrete principal-unit filtration on the unit group
of the valuation ring is

`U^n = { u | u - 1 ∈ m^n }`.

This file turns that definition into the abstract `AntitoneSubgroupFiltration`
used by ramification and norm arguments.
-/

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The concrete `n`-th principal-unit subgroup of the valuation ring unit group.-/
def higherPrincipalUnitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) (n : ℕ) :
    Subgroup F.valuationSubringˣ where
  carrier := {u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}
  one_mem' := by
    change (1 : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [sub_self]
    exact (F.maximalIdeal ^ n).zero_mem
  mul_mem' := by
    intro x y hx hy
    have hxy :
        ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 =
          (x : F.valuationSubring) * ((y : F.valuationSubring) - 1) +
            ((x : F.valuationSubring) - 1) := by
      change (x : F.valuationSubring) * (y : F.valuationSubring) - 1 = _
      ring
    change ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxy]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) hx
  inv_mem' := by
    intro x hx
    have hxinv :
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
      calc
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) -
              ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
                (x : F.valuationSubring) := by
          rw [Units.inv_mul]
        _ = -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
          ring
    change ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxinv]
    exact (F.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left (F.maximalIdeal ^ n)
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) hx)

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/--
Characterizes `u ∈ higherPrincipalUnitGroup F n` by the equivalent condition `(u :
F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n`.
@isnad1 id=iff.0h4v.s10.db0714bc120f from=translated src=- shape=1fa35fdb vocab=6ed6cc88
-/
@[simp] theorem mem_iff (n : ℕ) (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F n ↔
      (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n :=
  Iff.rfl

/-- Higher levels are contained in lower levels.
@isnad1 id=le.1h4v.s9.d981fbc12525 from=translated src=- shape=a0dd2222 vocab=2f0804a7
-/
theorem antitone {m n : ℕ} (h : m ≤ n) :
    higherPrincipalUnitGroup F n ≤ higherPrincipalUnitGroup F m := by
  intro u hu
  exact (Ideal.pow_le_pow_right h) hu

/-- Prime-binomial containment in an ideal.  If `p ∈ I` and `a ∈ I^n` with
`n ≥ 1`, then `(1 + a)^p - 1` is one level deeper.
@isnad1 id=mem.4h5v.s8.8cce3a2c0222 from=translated src=- shape=fcf18b22 vocab=3c75195c
-/
theorem one_add_pow_prime_sub_one_mem_pow_succ
    {R : Type*} [CommRing R] (I : Ideal R)
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hp_mem : (p : R) ∈ I) {a : R} (ha : a ∈ I ^ n) :
    (1 + a) ^ p - 1 ∈ I ^ (n + 1) := by
  rcases exists_add_pow_prime_eq hp (1 : R) a with ⟨r, hr⟩
  have hnp : n + 1 ≤ n * p := by
    exact (Nat.add_le_add_left hn n).trans
      (by simpa [Nat.mul_two] using Nat.mul_le_mul_left n hp.two_le)
  have ha_pow_np : a ^ p ∈ I ^ (n * p) := by
    simpa [pow_mul] using (Ideal.pow_mem_pow ha p)
  have ha_pow_succ : a ^ p ∈ I ^ (n + 1) :=
    Ideal.pow_le_pow_right hnp ha_pow_np
  have ha_p_succ : a * (p : R) ∈ I ^ (n + 1) := by
    simpa [pow_succ] using (Ideal.mul_mem_mul ha hp_mem)
  have hp_a_succ : (p : R) * a ∈ I ^ (n + 1) := by
    simpa [mul_comm] using ha_p_succ
  have hp_a_r_succ : (p : R) * a * r ∈ I ^ (n + 1) :=
    (I ^ (n + 1)).mul_mem_right r hp_a_succ
  have hbinom : (1 + a) ^ p - 1 = a ^ p + (p : R) * a * r := by
    rw [hr]
    ring
  rw [hbinom]
  exact Ideal.add_mem _ ha_pow_succ hp_a_r_succ

/-- If the residue field has ring characteristic `p`, then `p` lies in the
maximal ideal of the valuation ring.
@isnad1 id=mem.1h3v.s8.3a5f5633ccdd from=translated src=- shape=19b08878 vocab=48ed92a2
-/
theorem natCast_mem_maximalIdeal_of_residue_ringChar_eq
    {p : ℕ} (hchar : ringChar F.residueField = p) :
    (p : F.valuationSubring) ∈ F.maximalIdeal := by
  have : CharP F.residueField p := (ringChar.eq_iff (R := F.residueField)).1 hchar
  rw [← F.residue_eq_zero_iff]
  rw [map_natCast]
  exact CharP.cast_eq_zero F.residueField p

/-- Concrete principal-unit form of the prime-binomial containment:
if `p ∈ m`, then the `p`th power carries `U^n` into `U^(n+1)` for `n ≥ 1`.
@isnad1 id=mem.4h5v.s10.12c5ade6bc98 from=translated src=- shape=bc29e1c1 vocab=63cabca6
-/
theorem pow_mem_succ_of_natCast_mem_maximalIdeal
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hp_mem : (p : F.valuationSubring) ∈ F.maximalIdeal)
    {u : F.valuationSubringˣ}
    (hu : u ∈ higherPrincipalUnitGroup F n) :
    u ^ p ∈ higherPrincipalUnitGroup F (n + 1) := by
  rw [higherPrincipalUnitGroup.mem_iff] at hu ⊢
  let a : F.valuationSubring := (u : F.valuationSubring) - 1
  have hu_eq : (u : F.valuationSubring) = 1 + a := by
    simp [a]
  have hpow :
      ((u ^ p : F.valuationSubringˣ) : F.valuationSubring) =
        (u : F.valuationSubring) ^ p := Units.val_pow_eq_pow_val u p
  rw [hpow, hu_eq]
  exact
    higherPrincipalUnitGroup.one_add_pow_prime_sub_one_mem_pow_succ
      F.maximalIdeal hp hn hp_mem hu

/-- Residue-characteristic form of `pow_mem_succ_of_natCast_mem_maximalIdeal`:
if the residue field has characteristic `p`, then `p`th powers move principal
units one step deeper.
@isnad1 id=mem.4h5v.s10.936271cf56c3 from=translated src=- shape=97195eb1 vocab=b77fc01b
-/
theorem pow_mem_succ_of_residue_ringChar_eq
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hchar : ringChar F.residueField = p)
    {u : F.valuationSubringˣ}
    (hu : u ∈ higherPrincipalUnitGroup F n) :
    u ^ p ∈ higherPrincipalUnitGroup F (n + 1) :=
  higherPrincipalUnitGroup.pow_mem_succ_of_natCast_mem_maximalIdeal
    F hp hn
    (higherPrincipalUnitGroup.natCast_mem_maximalIdeal_of_residue_ringChar_eq
      F hchar)
    hu

/-- Establishes the identity `higherPrincipalUnitGroup F 0 = ⊤`.
@isnad1 id=eq.0h2v.s8.29ec071c301f from=translated src=- shape=83992b77 vocab=a0aa4e45
-/
@[simp] theorem zero_eq_top :
    higherPrincipalUnitGroup F 0 = ⊤ := by
  ext u
  simp [higherPrincipalUnitGroup]

/-- The residue of a valuation-ring unit, viewed as a unit of the residue
field.-/
def residueUnitHom :
    F.valuationSubringˣ →* F.residueFieldˣ :=
  Units.map F.residueMap.toMonoidHom

/--
The defining evaluation formula for `residueUnitHom` is `((higherPrincipalUnitGroup.residueUnitHom
F u : F.residueFieldˣ) : F.residueField) = F.residueMap (u : F.valuationSubring)`.
@isnad1 id=eq.0h3v.s10.2580b39a658d from=translated src=- shape=8d353bc3 vocab=a6991181
-/
@[simp] theorem residueUnitHom_apply (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.residueUnitHom F u : F.residueFieldˣ) :
        F.residueField) =
      F.residueMap (u : F.valuationSubring) :=
  rfl

/-- The first concrete principal-unit level consists exactly of units whose
residue is `1`.
@isnad1 id=iff.0h3v.s9.fcd707501277 from=translated src=- shape=ebe89fbe vocab=575f763c
-/
theorem mem_one_iff_residue_eq_one (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F 1 ↔
      F.residueMap (u : F.valuationSubring) = 1 := by
  rw [higherPrincipalUnitGroup.mem_iff, pow_one]
  constructor
  · intro hu
    have hres :
        F.residueMap (u : F.valuationSubring) = F.residueMap 1 := by
      exact
        (residue_eq_residue_iff_sub_mem_maximalIdeal
          (R := F.valuationSubring) (u : F.valuationSubring) 1).2 hu
    simpa using hres
  · intro hu
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := F.valuationSubring) (u : F.valuationSubring) 1).1
        (by simpa using hu)

/--
Characterizes `higherPrincipalUnitGroup.residueUnitHom F u = 1` by the equivalent condition `u ∈
higherPrincipalUnitGroup F 1`.
@isnad1 id=iff.0h3v.s10.a4396048096d from=translated src=- shape=7ba9ca61 vocab=ec314607
-/
theorem residueUnitHom_eq_one_iff (u : F.valuationSubringˣ) :
    higherPrincipalUnitGroup.residueUnitHom F u = 1 ↔
      u ∈ higherPrincipalUnitGroup F 1 := by
  constructor
  · intro hu
    apply (higherPrincipalUnitGroup.mem_one_iff_residue_eq_one F u).2
    have hval :=
      congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) hu
    simpa using hval
  · intro hu
    apply Units.ext
    simpa using (higherPrincipalUnitGroup.mem_one_iff_residue_eq_one F u).1 hu

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
