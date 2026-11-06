import Tengoku.Seed.Topology.Algebra.Valued.ValuationTopology
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Defs
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation
import Tengoku.Seed.Analysis.Normed.Ring.Lemmas
import Tengoku.Seed.NumberTheory.RamificationInertia.Inertia
import Tengoku.Seed.RingTheory.Valuation.Discrete.Basic
import Tengoku.Seed.Topology.Path
import Tengoku.Seed.Algebra.Group.Int.TypeTags
import Tengoku.Seed.RingTheory.Valuation.Discrete.RankOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

end IsDedekindDomain.HeightOneSpectrum

end

section

end

section

variable {F : Type*} [Field F]

end

section

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

instance : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)

lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl

instance : (v.completionIdeal K).LiesOver v.asIdeal := ⟨by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]⟩

open IsLocalRing in

noncomputable def ResidueFieldToCompletionResidueField :
    A ⧸ v.asIdeal →+* ResidueField (v.adicCompletionIntegers K) :=
  Ideal.quotientMap _ (algebraMap _ _) <| le_of_eq Ideal.LiesOver.over

namespace adicCompletion

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum

end
