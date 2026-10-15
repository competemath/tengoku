/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.Germs.Basic
public import Tengoku

/-!
# Canonical chosen analytic representatives

Abstract germs cannot be evaluated away from the origin.  For finite
specialization arguments it is convenient to choose one analytic
representative for each germ and retain the theorem identifying its raw
function germ.
-/

@[expose] public section

namespace LocalComplexGeometry

noncomputable section

/-- A chosen analytic representative of a holomorphic germ. -/
def HolomorphicGerm.representative {n : ℕ}
    (f : HolomorphicGerm n) : ComplexEuclidean n → ℂ :=
  Classical.choose (HolomorphicGerm.exists_rep f)

/-- The chosen representative is analytic at the origin.
@isnad1 id=analytic.0h2v.s8.1a43efafc54d from=translated src=- shape=6e82f202 vocab=347148a3
-/
theorem HolomorphicGerm.analyticAt_representative {n : ℕ}
    (f : HolomorphicGerm n) :
    AnalyticAt ℂ (HolomorphicGerm.representative f) 0 :=
  (Classical.choose_spec (HolomorphicGerm.exists_rep f)).1

/-- The chosen representative represents the original germ.
@isnad1 id=eq.0h2v.s8.98006eded4f6 from=translated src=- shape=55f67261 vocab=32453793
-/
theorem HolomorphicGerm.coe_representative {n : ℕ}
    (f : HolomorphicGerm n) :
    (HolomorphicGerm.representative f : FunctionGerm n) =
      (f : FunctionGerm n) :=
  (Classical.choose_spec (HolomorphicGerm.exists_rep f)).2

/-- Chosen representatives of a finite coefficient vector. -/
def HolomorphicGerm.coefficientRepresentatives {n k : ℕ}
    (c : Fin k → HolomorphicGerm n) :
    Fin k → ComplexEuclidean n → ℂ :=
  fun i ↦ HolomorphicGerm.representative (c i)

/--
@isnad1 id=analytic.0h4v.s8.3b306e501475 from=translated src=- shape=34b6c12c vocab=53c5f1f0
-/
theorem HolomorphicGerm.analyticAt_coefficientRepresentatives {n k : ℕ}
    (c : Fin k → HolomorphicGerm n) (i : Fin k) :
    AnalyticAt ℂ (HolomorphicGerm.coefficientRepresentatives c i) 0 :=
  HolomorphicGerm.analyticAt_representative (c i)

/--
@isnad1 id=eq.0h4v.s8.a9c4437d88aa from=translated src=- shape=4ea93353 vocab=cd7cdabb
-/
theorem HolomorphicGerm.coe_coefficientRepresentatives {n k : ℕ}
    (c : Fin k → HolomorphicGerm n) (i : Fin k) :
    (HolomorphicGerm.coefficientRepresentatives c i : FunctionGerm n) =
      (c i : FunctionGerm n) :=
  HolomorphicGerm.coe_representative (c i)

end

end LocalComplexGeometry
