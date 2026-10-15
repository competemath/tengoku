/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.Germs.Representatives
public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.Nullstellensatz.ZeroSetGerms
public import Tengoku

/-!
# Representatives of a finite ideal generating family

Noetherianity supplies a chosen finite generating set for every ideal.  This
file chooses analytic representatives of those generators and records the
exact pointwise predicate representing the ideal's local zero-set germ.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LocalComplexGeometry

noncomputable section

/-- The finite type indexing the chosen generators of an ideal. -/
abbrev IdealGeneratorIndex {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) := idealGeneratorFinset I

/-- Chosen analytic representatives of the chosen generators of an ideal. -/
def idealGeneratorRepresentatives {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) :
    IdealGeneratorIndex I → ComplexEuclidean n → ℂ :=
  fun f ↦ HolomorphicGerm.representative (f : HolomorphicGerm n)

/--
@isnad1 id=analytic.0h3v.s11.8a6ff6da377f from=translated src=- shape=29011af4 vocab=f64938d1
-/
theorem analyticAt_idealGeneratorRepresentatives {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (f : IdealGeneratorIndex I) :
    AnalyticAt ℂ (idealGeneratorRepresentatives I f) 0 :=
  HolomorphicGerm.analyticAt_representative (f : HolomorphicGerm n)

/--
@isnad1 id=eq.0h3v.s11.75a4e09b9a77 from=translated src=- shape=5200ca97 vocab=a6a920d2
-/
theorem ofFunction_idealGeneratorRepresentatives {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (f : IdealGeneratorIndex I) :
    HolomorphicGerm.ofFunction (idealGeneratorRepresentatives I f)
        (analyticAt_idealGeneratorRepresentatives I f) =
      (f : HolomorphicGerm n) := by
  apply Subtype.ext
  exact HolomorphicGerm.coe_representative (f : HolomorphicGerm n)

/-- Every member of the chosen generating finset belongs to the ideal it
generates.
@isnad1 id=mem.0h3v.s12.c0ea195cef4a from=translated src=- shape=31d218cb vocab=b948fb23
-/
theorem idealGenerator_mem {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (f : IdealGeneratorIndex I) :
    (f : HolomorphicGerm n) ∈ I := by
  have hle : Ideal.span
      (idealGeneratorFinset I : Set (HolomorphicGerm n)) ≤ I :=
    (span_idealGeneratorFinset I).le
  exact hle (Ideal.subset_span f.property)

/-- Pointwise representative of the ideal zero-set germ furnished by the
chosen finite generating family. -/
def idealGeneratorZeroPredicate {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (z : ComplexEuclidean n) : Prop :=
  ∀ f : IdealGeneratorIndex I, idealGeneratorRepresentatives I f z = 0

/-- The canonical finite-generator predicate represents the abstract local
zero-set germ of the ideal.
@isnad1 id=eq.0h2v.s10.91a2e11348c7 from=translated src=- shape=ee7e3029 vocab=cec03387
-/
theorem idealZeroSetGerm_eq_generatorZeroPredicate {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) :
    idealZeroSetGerm I =
      (idealGeneratorZeroPredicate I : LocalSetGerm n) := by
  calc
    idealZeroSetGerm I = finiteCommonZeroSet (idealGeneratorFinset I) := rfl
    _ = fintypeCommonZeroSet
        (fun f : IdealGeneratorIndex I ↦ (f : HolomorphicGerm n)) :=
      finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype
        (idealGeneratorFinset I)
    _ = fintypeCommonZeroSet
        (fun f : IdealGeneratorIndex I ↦
          HolomorphicGerm.ofFunction (idealGeneratorRepresentatives I f)
            (analyticAt_idealGeneratorRepresentatives I f)) := by
      congr 1
      funext f
      exact (ofFunction_idealGeneratorRepresentatives I f).symm
    _ = (idealGeneratorZeroPredicate I : LocalSetGerm n) := by
      rw [fintypeCommonZeroSet_ofFunction
        (idealGeneratorRepresentatives I)
        (analyticAt_idealGeneratorRepresentatives I)]
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun _ ↦ propext (by
        simp only [idealGeneratorZeroPredicate])

/-- A chosen representative of any ideal member vanishes on the pointwise
finite-generator predicate, on one neighborhood of the origin.
@isnad1 id=eventual.1h3v.s12.46f0b50455bf from=translated src=- shape=0b7bb226 vocab=d45cc2bf
-/
theorem eventually_representative_eq_zero_of_mem_ideal
    {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (f : HolomorphicGerm n) (hf : f ∈ I) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z →
        HolomorphicGerm.representative f z = 0 := by
  have hzero : idealZeroSetGerm I ≤ germZeroLocus f :=
    idealZeroSetGerm_le_germZeroLocus_of_mem I hf
  rw [idealZeroSetGerm_eq_generatorZeroPredicate I] at hzero
  have hrep := HolomorphicGerm.coe_representative f
  unfold germZeroLocus at hzero
  rw [← hrep] at hzero
  change
    (idealGeneratorZeroPredicate I : LocalSetGerm n) ≤
      ((fun z ↦ HolomorphicGerm.representative f z = 0) :
        LocalSetGerm n) at hzero
  rw [Filter.Germ.coe_le] at hzero
  exact hzero

/-- Equality modulo an ideal makes chosen representatives equal on that
ideal's local zero set, after shrinking once.
@isnad1 id=eventual.1h4v.s14.7d85e0c090ac from=translated src=- shape=23eb5ffc vocab=2da76763
-/
theorem eventually_representatives_eq_of_quotient_eq
    {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (f g : HolomorphicGerm n)
    (hfg : Ideal.Quotient.mk I f = Ideal.Quotient.mk I g) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z →
        HolomorphicGerm.representative f z =
          HolomorphicGerm.representative g z := by
  have hsub : f - g ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hfg, sub_self]
  have hzero := eventually_representative_eq_zero_of_mem_ideal I (f - g) hsub
  have hrepSub :
      ((HolomorphicGerm.representative (f - g) :
          ComplexEuclidean n → ℂ) : FunctionGerm n) =
        (((fun z ↦ HolomorphicGerm.representative f z -
            HolomorphicGerm.representative g z) :
          ComplexEuclidean n → ℂ) : FunctionGerm n) := by
    calc
      _ = ((f - g : HolomorphicGerm n) : FunctionGerm n) :=
        HolomorphicGerm.coe_representative (f - g)
      _ = (f : FunctionGerm n) - (g : FunctionGerm n) := rfl
      _ = (HolomorphicGerm.representative f : FunctionGerm n) -
          (HolomorphicGerm.representative g : FunctionGerm n) := by
        rw [HolomorphicGerm.coe_representative f,
          HolomorphicGerm.coe_representative g]
      _ = _ := (Filter.Germ.coe_sub _ _).symm
  have hsubeq : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      HolomorphicGerm.representative (f - g) z =
        HolomorphicGerm.representative f z -
          HolomorphicGerm.representative g z :=
    Filter.Germ.coe_eq.mp hrepSub
  filter_upwards [hzero, hsubeq] with z hz hzeq
  intro hZ
  exact sub_eq_zero.mp (hzeq ▸ hz hZ)

end

end LocalComplexGeometry
