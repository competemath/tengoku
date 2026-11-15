import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace HahnSeries

variable {K : Type*} [Field K]

def ramScale (e : ℕ) : ℤ →+ ℚ where
  toFun k := (k : ℚ) / e
  map_zero' := by simp
  map_add' a b := by simp only [Int.cast_add]; rw [add_div]

/--
@isnad1 id=eq.0h2v.s5.23b3563775e8 from=translated src=- shape=3153e5fe vocab=d2e6e2c4
-/
@[simp] theorem ramScale_apply (e : ℕ) (k : ℤ) : ramScale e k = (k : ℚ) / e := rfl

/--
@isnad1 id=injectiv.1h1v.s5.a8aea14fdfdb from=translated src=- shape=1d18f940 vocab=76e32b56
-/
theorem ramScale_injective {e : ℕ} (he : 0 < e) : Function.Injective (ramScale e) := by
  intro a b hab
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  simp only [ramScale_apply, div_eq_div_iff he' he'] at hab
  exact_mod_cast mul_right_cancel₀ he' hab

/--
@isnad1 id=iff.1h3v.s6.620d4621069d from=translated src=- shape=bb22010b vocab=37477d9f
-/
theorem ramScale_le_iff {e : ℕ} (he : 0 < e) (a b : ℤ) :
    ramScale e a ≤ ramScale e b ↔ a ≤ b := by
  have he' : (0 : ℚ) < e := Nat.cast_pos.mpr he
  simp only [ramScale_apply, div_le_div_iff_of_pos_right he', Int.cast_le]

def puiseuxRamEmb {e : ℕ} (he : 0 < e) : HahnSeries ℤ K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (ramScale e) (ramScale_injective he) (ramScale_le_iff he)

def HasRamBound (e : ℕ) (y : HahnSeries ℚ K) : Prop :=
  y.support ⊆ Set.range (fun k : ℤ => (k : ℚ) / e)

variable (K) in

def puiseuxRamSubfield {e : ℕ} (he : 0 < e) : Subfield (HahnSeries ℚ K) :=
  (puiseuxRamEmb (K := K) he).fieldRange

end HahnSeries

end
