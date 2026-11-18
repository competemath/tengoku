import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.RingTheory.Ideal.Quotient.Noetherian
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow

open IsLocalRing

namespace LCMazurS10LTART

variable {A : Type*} [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in
/--
@isnad1 id=nontrivi.1h2v.s6.25d02e1ff0f5 from=translated src=- shape=d6f59e47 vocab=147351a3
-/
theorem nontrivial_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr hI

/--
@isnad1 id=islocalr.1h2v.s6.ba35c7720006 from=translated src=- shape=ff1dd6f5 vocab=b20e41e6
-/
theorem isLocalRing_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : IsLocalRing (A ⧸ I) :=
  haveI := nontrivial_quotient_of_ne_top hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

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

end LCMazurS10LTART

open LCMazurS10LTART in
/--
@isnad1 id=isartini.0h2v.s7.9477f1f4ce81 from=translated src=- shape=8a367c76 vocab=d83c7d66
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (m : ℕ) :
    IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) := by
  have hne : IsLocalRing.maximalIdeal A ^ (m + 1) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self m.succ_ne_zero))
  haveI := isLocalRing_quotient_of_ne_top hne
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal, ← map_maximalIdeal_mk_of_ne_top hne]
  exact ⟨m + 1, by rw [← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker]⟩
