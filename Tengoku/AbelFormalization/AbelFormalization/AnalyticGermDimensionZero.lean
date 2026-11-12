import Tengoku.AbelFormalization.AbelFormalization.AnalyticGermLocal
import Tengoku.Seed.RingTheory.Noetherian.Basic
import Tengoku.Seed.RingTheory.KrullDimension.Field
import Tengoku.Seed.RingTheory.SimpleModule.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The zero-dimensional analytic-germ ring

On a subsingleton parameter space, analytic germs are determined by their
value at the base point. Evaluation is therefore a ring equivalence with
the reals. In particular, the actual ring of real-analytic germs in zero
variables is Noetherian and has Krull dimension zero. No corresponding
property in a positive number of variables is assumed here.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]

/-- In a subsingleton parameter space, equality of values forces equality of
analytic representatives everywhere, hence equality of their germs.
@isnad1 id=injectiv.0h2v.s10.0162929617f2 from=translated src=- shape=8bb93d8d vocab=a8cce08c
-/
theorem analyticGermValue_injective_of_subsingleton (x : E) :
    Function.Injective (analyticGermValue x) := by
  intro a b hab
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative a
  obtain ⟨g, hg, rfl⟩ := exists_analyticGerm_representative b
  change f x = g x at hab
  apply (analyticGermOf_eq_iff hf hg).mpr
  exact Eventually.of_forall fun y => by simpa only [Subsingleton.elim y x] using hab

/-- Evaluation identifies the analytic-germ ring over a subsingleton space
with the scalar field.-/
def analyticGermEquivRealOfSubsingleton (x : E) : AnalyticGermAt x ≃+* ℝ :=
  RingEquiv.ofBijective (analyticGermValue x)
    ⟨analyticGermValue_injective_of_subsingleton x, analyticGermValue_surjective x⟩

/--
@isnad1 id=eq.0h3v.s12.1afc1d2c0e3d from=translated src=- shape=d53c0336 vocab=334cf437
-/
@[simp]
theorem analyticGermEquivRealOfSubsingleton_apply (x : E) (g : AnalyticGermAt x) :
    analyticGermEquivRealOfSubsingleton x g = analyticGermValue x g := rfl

/--
@isnad1 id=isnoethe.0h2v.s8.8225af8c2264 from=translated src=- shape=cfa5b61e vocab=2b1050ab
-/
instance analyticGermIsNoetherianRingOfSubsingleton (x : E) :
    IsNoetherianRing (AnalyticGermAt x) :=
  isNoetherianRing_of_ringEquiv ℝ (analyticGermEquivRealOfSubsingleton x).symm

/--
@isnad1 id=eq.0h2v.s8.54b8e3af4466 from=translated src=- shape=e83f717e vocab=34fd85f0
-/
theorem analyticGerm_ringKrullDim_eq_zero_of_subsingleton (x : E) :
    ringKrullDim (AnalyticGermAt x) = 0 := by
  rw [(analyticGermEquivRealOfSubsingleton x).ringKrullDim,
    ringKrullDim_eq_zero_of_field ℝ]

/-- The dimension-zero base case in the manuscript's notation.-/
def realAnalyticGermZeroEquivReal : RealAnalyticGerm 0 ≃+* ℝ :=
  analyticGermEquivRealOfSubsingleton (0 : Fin 0 → ℝ)

/--
@isnad1 id=isnoethe.0h0v.s11.8f5c529bc7fa from=translated src=- shape=73f89a9c vocab=8cb7f7b9
-/
theorem realAnalyticGerm_zero_isNoetherian : IsNoetherianRing (RealAnalyticGerm 0) :=
  inferInstance

/--
@isnad1 id=eq.0h0v.s11.5b95dcb0aac0 from=translated src=- shape=e35ca635 vocab=fa70dab2
-/
theorem realAnalyticGerm_zero_ringKrullDim : ringKrullDim (RealAnalyticGerm 0) = 0 :=
  analyticGerm_ringKrullDim_eq_zero_of_subsingleton (0 : Fin 0 → ℝ)

end AbelFormalization
