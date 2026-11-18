import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_ResidueField_algebraMap_surjective_quotient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_ResidueField_algebraMap_surjective_quotient

open IsLocalRing

namespace LCMazurS10LTRES

variable {A : Type*} [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in
/--
@isnad1 id=nontrivi.1h2v.s6.25d02e1ff0f5 from=translated src=- shape=d6f59e47 vocab=147351a3
-/
theorem nontrivial_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr hI

/--
@isnad1 id=islocalh.1h2v.s7.1c5ce50ccf35 from=translated src=- shape=37a2513e vocab=3a4668b4
-/
theorem isLocalHom_mk_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : IsLocalHom (Ideal.Quotient.mk I) :=
  haveI := nontrivial_quotient_of_ne_top hI
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/--
@isnad1 id=eq.1h2v.s8.9a4c31985ee9 from=translated src=- shape=91278451 vocab=3c485cba
-/
theorem map_maximalIdeal_mk_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) [IsLocalRing (A ⧸ I)] :
    (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
  haveI := isLocalHom_mk_of_ne_top hI
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI), mem_maximalIdeal,
    mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end LCMazurS10LTRES

open LCMazurS10LTRES in
/--
@isnad1 id=surjecti.1h3v.s9.690ed2a8a454 from=translated src=- shape=58825a5e vocab=8359e7eb
-/
theorem solution
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (h : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField A))) :
    Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField (A ⧸ I))) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨o, ho⟩ := h (IsLocalRing.residue A a)
  refine ⟨o, ?_⟩
  change IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I (algebraMap 𝒪 A o)) =
    IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I a)
  change IsLocalRing.residue A (algebraMap 𝒪 A o) = IsLocalRing.residue A a at ho
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at ho ⊢
  rw [← map_sub, ← map_maximalIdeal_mk_of_ne_top hI]
  exact Ideal.mem_map_of_mem _ ho
