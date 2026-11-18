import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers

open _root_.IsDedekindDomain open _root_.IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain
export _root_.IsDedekindDomain (HeightOneSpectrum.ext FiniteAdeleRing exists_forall_sub_mem_ideal HeightOneSpectrum)
namespace HeightOneSpectrum
export _root_.IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap intValuation_le_pow_iff_mem valuedAdicCompletion_eq_valuation adicCompletion_valueGroup_eq algebraMap_adicCompletion intValuation_lt_one_iff_mem asIdeal mem_adicCompletionIntegers isPrime intValuation_ne_zero adicCompletion valuation coe_mem_adicCompletionIntegers ne_bot intValuation_le_one adicCompletionIntegers valuedAdicCompletion_surjective irreducible adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers intValuation_if_neg prime intValuation)
open _root_.IsDedekindDomain.HeightOneSpectrum open _root_.IsDedekindDomain

section Multiplicative

open scoped WithZero

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

scoped instance s2_isRankOneDiscrete_valuedAdicCompletion : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open scoped algebraMap

end IsDedekindDomain.HeightOneSpectrum
open scoped _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain.HeightOneSpectrum
open scoped _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain
