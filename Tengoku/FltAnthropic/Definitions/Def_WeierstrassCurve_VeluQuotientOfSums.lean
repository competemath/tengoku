import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_Velu

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluQuotientOfSums (t w : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * t
  a₆ := W.a₆ - W.b₂ * t - 7 * w

/--
@isnad1 id=eq.0h4v.s4.795b4e75cfa1 from=translated src=- shape=f718534b vocab=91a2f115
-/
@[simp] lemma veluQuotientOfSums_a₁ (t w : R) : (W.veluQuotientOfSums t w).a₁ = W.a₁ := rfl
/--
@isnad1 id=eq.0h4v.s4.0ee6da8a8894 from=translated src=- shape=f718534b vocab=3d41f969
-/
@[simp] lemma veluQuotientOfSums_a₂ (t w : R) : (W.veluQuotientOfSums t w).a₂ = W.a₂ := rfl
/--
@isnad1 id=eq.0h4v.s4.e7e45ac6f500 from=translated src=- shape=f718534b vocab=875ed622
-/
@[simp] lemma veluQuotientOfSums_a₃ (t w : R) : (W.veluQuotientOfSums t w).a₃ = W.a₃ := rfl
/--
@isnad1 id=eq.0h4v.s6.684a9e1db403 from=translated src=- shape=2c869bb6 vocab=0c1f32e6
-/
lemma veluQuotientOfSums_a₄ (t w : R) : (W.veluQuotientOfSums t w).a₄ = W.a₄ - 5 * t := rfl
/--
@isnad1 id=eq.0h4v.s6.4e47569793f3 from=translated src=- shape=b9ea3b67 vocab=5f05c5f6
-/
lemma veluQuotientOfSums_a₆ (t w : R) :
    (W.veluQuotientOfSums t w).a₆ = W.a₆ - W.b₂ * t - 7 * w := rfl

/--
@isnad1 id=eq.0h3v.s5.059d49783800 from=translated src=- shape=5cc5f18c vocab=04b63355
-/
theorem veluQuotient_eq_veluQuotientOfSums (S : Finset (R × R)) :
    W.veluQuotient S = W.veluQuotientOfSums (W.veluTSum S) (W.veluWSum S) := rfl

/--
@isnad1 id=eq.2h5v.s5.abf060799785 from=translated src=- shape=dd47af33 vocab=04b63355
-/
theorem veluQuotient_eq_veluQuotientOfSums_of_sums {S : Finset (R × R)} {t w : R}
    (ht : W.veluTSum S = t) (hw : W.veluWSum S = w) :
    W.veluQuotient S = W.veluQuotientOfSums t w := by
  subst ht hw; rfl

end WeierstrassCurve
