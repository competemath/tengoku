import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DiagHom

variable {A : Type*} [CommRing A]

def diagUnitGL2 (x : Aˣ) : GL (Fin 2) A where
  val := !![(x : A), 0; 0, 1]
  inv := !![((x⁻¹ : Aˣ) : A), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s8.85f08c87ba68 from=translated src=- shape=e8b5b67f vocab=b45e5348
-/
@[simp] theorem coe_diagUnitGL2 (x : Aˣ) :
    ((diagUnitGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, 1] :=
  rfl

def diagHom : Aˣ →* GL (Fin 2) A where
  toFun := diagUnitGL2
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s8.82a615085f57 from=translated src=- shape=2da95ba0 vocab=950f2b66
-/
theorem diagHom_apply (x : Aˣ) : diagHom x = diagUnitGL2 x :=
  rfl

end DiagHom

section RatTorus

variable (v : HeightOneSpectrum (𝓞 ℚ))

def ratPrimeAt : v.adicCompletion ℚ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ)

/--
@isnad1 id=ne.0h1v.s7.aa4c1c38b4b2 from=translated src=- shape=e10c7071 vocab=733f0b8d
-/
theorem ratPrimeAt_ne_zero : ratPrimeAt v ≠ 0 := by
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact Nat.cast_ne_zero.mpr (by omega)

def ratPrimeUnit : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 (ratPrimeAt v) (ratPrimeAt_ne_zero v)

def iotaTorusLocal (n : ℕ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  iotaGL (diagHom (ratPrimeUnit v ^ n))

/--
@isnad1 id=eq.0h1v.s8.455c4001f2c5 from=translated src=- shape=ee75062e vocab=e5124de8
-/
@[simp] theorem iotaTorusLocal_zero : iotaTorusLocal v 0 = 1 := by
  simp only [iotaTorusLocal, pow_zero, map_one]

/--
@isnad1 id=eq.0h3v.s9.f69b043739a1 from=translated src=- shape=a4a0885e vocab=3a34f85b
-/
theorem iotaTorusLocal_add (m n : ℕ) :
    iotaTorusLocal v (m + n) = iotaTorusLocal v m * iotaTorusLocal v n := by
  simp only [iotaTorusLocal, pow_add, map_mul]

end RatTorus

section Countable

variable (K : Type*) [Field K] [Countable K]

/--
@isnad1 id=countabl.0h1v.s5.1bd6df1f958b from=translated src=- shape=9ccf9302 vocab=a0a0579f
-/
instance countable_GL2 : Countable (GL (Fin 2) K) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  Function.Injective.countable fun _ _ h => Units.ext h

/--
@isnad1 id=countabl.0h1v.s3.6b7fa9e44745 from=translated src=- shape=d96e9922 vocab=d86eee3c
-/
instance countable_mirabolicIndex : Countable (MirabolicIndex K) := by
  unfold MirabolicIndex
  infer_instance

end Countable

end LanglandsTunnell.CubicInduction
