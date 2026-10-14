module

public import Tengoku

public section

namespace ENNReal
variable {α : Type*}

/--
@isnad1 id=eq.0h3v.s5.cbd21b6c2984 from=translated src=- shape=79dfb935 vocab=bbcd208e
-/
@[simp] lemma ofReal_indicator_one (s : Set α) (a : α) :
    ENNReal.ofReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

/--
@isnad1 id=eq.0h3v.s5.dc44c8500ff9 from=translated src=- shape=79dfb935 vocab=c0b32cc1
-/
@[local simp] lemma tOReal_indicator_one (s : Set α) (a : α) :
    ENNReal.toReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

end ENNReal
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
