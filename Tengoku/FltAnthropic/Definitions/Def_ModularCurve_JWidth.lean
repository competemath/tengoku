import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve

def jWidth {K : Type*} [Field K] [DecidableEq K] (j : K) : ℕ :=
  if j = 0 then 3 else if j = 1728 then 2 else 1

variable {K : Type*} [Field K] [DecidableEq K]

/--
@isnad1 id=eq.1h2v.s5.252b0a815f4b from=translated src=- shape=43b237cd vocab=641d8fe3
-/
theorem jWidth_of_eq_zero {j : K} (h : j = 0) : jWidth j = 3 := by simp [jWidth, h]

/--
@isnad1 id=eq.2h2v.s6.6d6cca072b57 from=translated src=- shape=8712feb9 vocab=641d8fe3
-/
theorem jWidth_of_eq_1728 {j : K} (h : j = 1728) (h0 : j ≠ 0) : jWidth j = 2 := by
  subst h; simp [jWidth, h0]

/--
@isnad1 id=eq.2h2v.s6.f17090676369 from=translated src=- shape=5eed5cea vocab=641d8fe3
-/
theorem jWidth_of_ne {j : K} (h0 : j ≠ 0) (h1728 : j ≠ 1728) : jWidth j = 1 := by
  simp [jWidth, h0, h1728]

/--
@isnad1 id=eq.0h2v.s6.4250999eb7dc from=translated src=- shape=18b5e056 vocab=b95d9a06
-/
theorem jWidth_eq_ite (j : K) :
    jWidth j = (if j = 0 then 3 else if j = 1728 then 2 else 1) := rfl

/--
@isnad1 id=lt.0h2v.s4.d6ae927bcd33 from=translated src=- shape=c83d11cb vocab=92b06aa5
-/
theorem jWidth_pos (j : K) : 0 < jWidth j := by
  unfold jWidth; split_ifs <;> decide

/--
@isnad1 id=or.0h2v.s5.c876ed0223e0 from=translated src=- shape=a4a533ac vocab=641d8fe3
-/
theorem jWidth_eq_one_or (j : K) : jWidth j = 1 ∨ jWidth j = 2 ∨ jWidth j = 3 := by
  unfold jWidth; split_ifs <;> simp

/--
@isnad1 id=dvd.0h2v.s4.1ed277dab0c6 from=translated src=- shape=50729a11 vocab=217a98d7
-/
theorem jWidth_dvd_six (j : K) : jWidth j ∣ 6 := by
  unfold jWidth; split_ifs <;> decide

/--
@isnad1 id=eq.0h4v.s6.9aded739a3ac from=translated src=- shape=78d0efce vocab=dba54e05
-/
theorem jWidth_map {L : Type*} [Field L] [DecidableEq L] (f : K →+* L) (j : K) :
    jWidth (f j) = jWidth j := by
  have h1728 : f 1728 = (1728 : L) := map_ofNat f 1728
  unfold jWidth
  by_cases hj0 : j = 0
  · subst hj0; simp
  · have hne : f j ≠ 0 := (map_ne_zero_iff f f.injective).mpr hj0
    rw [ite_eq_right hj0, ite_eq_right hne]
    by_cases hj : j = 1728
    · have hfj : f j = 1728 := by rw [hj, h1728]
      rw [ite_eq_left hj, ite_eq_left hfj]
    · have hfj : f j ≠ 1728 := fun h => hj (f.injective (h.trans h1728.symm))
      rw [ite_eq_right hj, ite_eq_right hfj]

end ModularCurve
