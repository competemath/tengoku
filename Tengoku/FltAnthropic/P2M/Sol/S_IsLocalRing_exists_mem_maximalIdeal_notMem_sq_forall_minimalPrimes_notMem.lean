import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem

open IsLocalRing RingTheory
open scoped Pointwise

namespace W2RLR

universe u v

/--
@isnad1 id=ne.1h1v.s6.fa8c521f3369 from=translated src=- shape=ff4e19b8 vocab=6bb23999
-/
theorem maximalIdeal_ne_bot_of_ringKrullDim_pos (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ≠ ⊥ := by
  intro hbot
  rw [ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
  exact hdim.false

namespace No4PatchingCore

section FromABFreeness
variable {R : Type u} [CommRing R]

end FromABFreeness

section Exchange0
variable (R : Type u) [CommRing R]

end Exchange0

section PrimeAvoidance

/--
@isnad1 id=not.1h1v.s6.15db0760469e from=translated src=- shape=5f391251 vocab=ef030caf
-/
theorem maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro hmem

  have hall : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      (hmem.2 ⟨p.isPrime, bot_le⟩ (IsLocalRing.le_maximalIdeal p.isPrime.ne_top))
  haveI : Subsingleton (PrimeSpectrum R) :=
    ⟨fun p q => PrimeSpectrum.ext ((hall p).trans (hall q).symm)⟩
  have heq : ringKrullDim R = 0 := by
    rw [ringKrullDim]
    haveI : Nonempty (PrimeSpectrum R) := ⟨⟨maximalIdeal R, inferInstance⟩⟩
    letI : Unique (PrimeSpectrum R) := uniqueOfSubsingleton (Classical.arbitrary _)
    exact Order.krullDim_eq_zero_of_unique
  rw [heq] at hdim
  exact hdim.false

/--
@isnad1 id=ex.1h1v.s8.331277e0cc45 from=translated src=- shape=45e1dd62 vocab=5880acdb
-/
theorem exists_parameter_notMem_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hbot : maximalIdeal R ≠ ⊥ :=
    W2RLR.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim

  have hfin : (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)).Finite :=
    Set.Finite.insert _ (minimalPrimes.finite_of_isNoetherianRing R)

  have hnotle : ¬ ∃ I ∈ hfin.toFinset, maximalIdeal R ≤ I := by
    rintro ⟨I, hIs, hle⟩
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    ·
      refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
        (maximalIdeal R) (IsNoetherian.noetherian _) ?_
        (IsLocalRing.maximalIdeal_le_jacobson _))
      rwa [Ideal.smul_eq_mul, ← pow_two]
    ·
      have hp_prime : I.IsPrime := Ideal.IsMinimalPrime.isPrime hI
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal hp_prime.ne_top).antisymm hle
      rw [heq] at hI
      exact maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos R hdim hI

  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ (hfin.toFinset : Set (Ideal R)), (I : Set R)) := by
    intro hsub
    refine hnotle ((Ideal.subset_union_prime (s := hfin.toFinset) (f := fun I => I)
      ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2) ?_).mp hsub)
    intro I hIs hI₁ _
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    · exact absurd rfl hI₁
    · exact Ideal.IsMinimalPrime.isPrime hI

  rw [hfin.coe_toFinset] at havoid
  obtain ⟨x, hxm, hxout⟩ := Set.not_subset.mp havoid
  refine ⟨x, hxm, ?_, ?_⟩
  ·
    intro hx2
    exact hxout (Set.mem_biUnion (Set.mem_insert _ _) hx2)
  ·
    intro p hp hxp
    exact hxout (Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp)

end PrimeAvoidance

section DimensionDrop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

end DimensionDrop

section QuotientRegularity

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

end QuotientRegularity

section MatsumuraDomain

end MatsumuraDomain

end No4PatchingCore

end W2RLR

open IsLocalRing

/--
@isnad1 id=ex.1h1v.s8.331277e0cc45 from=translated src=- shape=45e1dd62 vocab=5880acdb
-/
theorem solution
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p :=
  W2RLR.No4PatchingCore.exists_parameter_notMem_minimalPrimes R hdim
