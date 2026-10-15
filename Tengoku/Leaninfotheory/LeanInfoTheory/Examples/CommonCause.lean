/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Markov

/-!
# A finite common-cause model

This opt-in example constructs two noisy binary observations of a shared fair
binary cause. Conditional on the cause, the observations are independent. The
example exercises the positive-fiber, zero-conditional-mutual-information, and
channel-factorization views of that statement.
-/

namespace LeanInfoTheory
namespace Examples
namespace CommonCause

open Shannon

noncomputable section

/-- A fair binary common cause. -/
def causeLaw : PMF Bool := PMF.uniformOfFintype Bool

/-- A binary channel that copies its input correctly with probability `3 / 4`. -/
def noisyCopy (b : Bool) : PMF Bool :=
  if b then
    PMF.ofFintype
      (fun c : Bool =>
        ((cond c (3 / 4 : NNReal) (1 - (3 / 4 : NNReal)) : NNReal) : ENNReal))
      (by
        have h : (3 / 4 : NNReal) <= 1 := by
          change (3 / 4 : Real) <= 1
          norm_num
        rw [Fintype.sum_bool]
        simp only [Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add]
        rw [add_tsub_cancel_of_le h]
        rfl)
  else
    PMF.ofFintype
      (fun c : Bool =>
        ((cond c (1 / 4 : NNReal) (1 - (1 / 4 : NNReal)) : NNReal) : ENNReal))
      (by
        have h : (1 / 4 : NNReal) <= 1 := by
          change (1 / 4 : Real) <= 1
          norm_num
        rw [Fintype.sum_bool]
        simp only [Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add]
        rw [add_tsub_cancel_of_le h]
        rfl)

/-- Both channel rows are genuinely random and depend on the input.
@isnad1 id=and.0h0v.s6.8587a2dc1f77 from=translated src=- shape=a47bda60 vocab=0610b594
-/
theorem noisyCopy_masses :
    noisyCopy false true = (1 / 4 : ENNReal) /\
      noisyCopy true true = (3 / 4 : ENNReal) := by
  norm_num [noisyCopy, PMF.ofFintype_apply, ENNReal.coe_div]

/-- Two noisy observations sampled independently from the same binary cause. -/
def law : PMF (Bool × Bool × Bool) :=
  PMF.channelExtension
    ((PMF.channelJoint causeLaw noisyCopy).map Prod.swap) noisyCopy

/-- The observation-cause-observation law is a Markov triple.
@isnad1 id=ismarkov.0h0v.s2.bf2b43b880bb from=translated src=- shape=aa9fb30a vocab=0c66cdb8
-/
theorem law_isMarkov : IsMarkovChain law := by
  simp [law]

/-- The two observations are conditionally independent given their common cause.
@isnad1 id=iscondin.0h0v.s5.752cfe2cb6d5 from=translated src=- shape=b4771597 vocab=b3aea34f
-/
theorem endpoints_condIndependent :
    IsCondIndependentOf law (fun x => x.1) (fun x => x.2.2)
      (fun x => x.2.1) := by
  simpa [IsMarkovChain, IsMarkovChainOf] using law_isMarkov

/-- Every positive-mass cause fiber has an independent endpoint law.
@isnad1 id=isindepe.1h1v.s7.2846cab7b7bd from=translated src=- shape=0d9078a1 vocab=2fc957f6
-/
theorem positiveFiber_isIndependent :
    forall b (hb : thirdMarginal
        (law.map fun x => (x.1, x.2.2, x.2.1)) b ≠ 0),
      IsIndependent
        (condFstSndGivenThird
          (law.map fun x => (x.1, x.2.2, x.2.1)) b hb) :=
  (isMarkovChain_iff_fiberwise_endpoints_independent law).mp law_isMarkov

/-- The endpoint conditional mutual information given the cause vanishes.
@isnad1 id=eq.0h0v.s5.07085c45a5b2 from=translated src=- shape=09b9af3e vocab=0873d0ee
-/
theorem endpoint_condMutualInfo_eq_zero :
    condMutualInfoOf law (fun x => x.1) (fun x => x.2.2)
      (fun x => x.2.1) = 0 :=
  (condMutualInfoOf_eq_zero_iff_isCondIndependentOf law
    (fun x => x.1) (fun x => x.2.2) (fun x => x.2.1)).mpr
      endpoints_condIndependent

/-- The canonical total conditional channel reconstructs the common-cause law.
@isnad1 id=eq.0h0v.s5.dac468422264 from=translated src=- shape=e2860747 vocab=cd0570ce
-/
theorem law_eq_canonical_channelExtension :
    law = PMF.channelExtension (fstSndMarginal law)
      (condFstGivenSndChannel ((sndThirdMarginal law).map Prod.swap)) :=
  (isMarkovChain_iff_canonical_channelExtension law).mp law_isMarkov

/-- Some channel from the cause reconstructs the common-cause law.
@isnad1 id=ex.0h0v.s4.6a22c5b82519 from=translated src=- shape=db913504 vocab=98eb2058
-/
theorem law_eq_some_channelExtension :
    exists V : Bool -> PMF Bool,
      law = PMF.channelExtension (fstSndMarginal law) V :=
  (isMarkovChain_iff_exists_channelExtension law).mp law_isMarkov

end

end CommonCause
end Examples
end LeanInfoTheory
