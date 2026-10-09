module

public import Tengoku

public section

namespace ENNReal
variable {α : Type*}

@[simp] lemma ofReal_indicator_one (s : Set α) (a : α) :
    ENNReal.ofReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

@[local simp] lemma tOReal_indicator_one (s : Set α) (a : α) :
    ENNReal.toReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

end ENNReal
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
