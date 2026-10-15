/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.Defs
public import Tengoku
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.GammaFactor

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace Module

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/--
@isnad1 id=eq.0h2v.s5.d51008ebc2ea from=translated src=- shape=49a22e68 vocab=33b1c465
-/
theorem dedekindArchimedeanFactor_of_isTotallyComplex (s : ℂ) :
    CompletedZeta.archimedeanFactor K s =
      (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K := by
  simp [CompletedZeta.archimedeanFactor, IsTotallyComplex.nrRealPlaces_eq_zero K]

/--
@isnad1 id=eq.0h2v.s6.84b44b59a7fa from=translated src=- shape=da84fa3d vocab=e97bbe98
-/
theorem completedDedekindZeta_of_isTotallyComplex (s : ℂ) :
    CompletedZeta.completed K s =
      CompletedZeta.discriminantFactor K s *
        (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K * dedekindZeta K s := by
  rw [CompletedZeta.completed, dedekindArchimedeanFactor_of_isTotallyComplex]

/--
@isnad1 id=eq.0h1v.s5.b7ef465221fe from=translated src=- shape=52e78819 vocab=a142bd17
-/
theorem two_mul_nrComplexPlaces_eq_finrank :
    2 * nrComplexPlaces K = finrank ℚ K := by
  simpa [IsTotallyComplex.nrRealPlaces_eq_zero K] using
    (card_add_two_mul_card_eq_rank K)

/--
@isnad1 id=eq.1h2v.s6.01415bcac857 from=translated src=- shape=d1ffc765 vocab=9933f9eb
-/
theorem logDeriv_dedekindArchimedeanFactor_of_isTotallyComplex {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (CompletedZeta.archimedeanFactor K) s =
      nrComplexPlaces K *
        (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) := by
  rw [show CompletedZeta.archimedeanFactor K =
      fun z : ℂ ↦ CompletedZeta.complexPlaceGammaFactor z ^ nrComplexPlaces K by
    funext z
    simp [dedekindArchimedeanFactor_of_isTotallyComplex, CompletedZeta.complexPlaceGammaFactor]]
  rw [logDeriv_fun_pow (differentiableAt_complexPlaceGammaFactor_of_re_pos hs),
    logDeriv_complexPlaceGammaFactor_of_re_pos hs]

end NumberField.Odlyzko
