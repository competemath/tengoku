import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

def deuringCurve (α β : R) : WeierstrassCurve R := ⟨α, 0, β, 0, 0⟩

section deuringCurve

variable (α β : R)

/--
@isnad1 id=eq.0h3v.s4.02e0f397a191 from=translated src=- shape=89a3f101 vocab=8d7770fa
-/
@[simp] theorem deuringCurve_a₁ : (deuringCurve α β).a₁ = α := rfl
/--
@isnad1 id=eq.0h3v.s5.7fc373e22183 from=translated src=- shape=598a312d vocab=7e8ab571
-/
@[simp] theorem deuringCurve_a₂ : (deuringCurve α β).a₂ = 0 := rfl
/--
@isnad1 id=eq.0h3v.s4.21612aa4a912 from=translated src=- shape=d14c0297 vocab=8e57dfa9
-/
@[simp] theorem deuringCurve_a₃ : (deuringCurve α β).a₃ = β := rfl
/--
@isnad1 id=eq.0h3v.s5.5f7777385139 from=translated src=- shape=598a312d vocab=a198d4e1
-/
@[simp] theorem deuringCurve_a₄ : (deuringCurve α β).a₄ = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.632101ae8fa2 from=translated src=- shape=598a312d vocab=422f0cf6
-/
@[simp] theorem deuringCurve_a₆ : (deuringCurve α β).a₆ = 0 := rfl

/--
@isnad1 id=eq.0h5v.s7.df2111b12194 from=translated src=- shape=d3a36827 vocab=0525d3aa
-/
theorem deuringCurve_map {S : Type*} [CommRing S] (f : R →+* S) :
    (deuringCurve α β).map f = deuringCurve (f α) (f β) := by
  simp [deuringCurve, WeierstrassCurve.map]

end deuringCurve

variable (W : WeierstrassCurve R)

def deuringA₃ (x y : R) : R := 2 * y + W.a₁ * x + W.a₃

def tangentSlopeNum (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

noncomputable def tangentSlope (x y : R) : R := W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x y)

noncomputable def deuringA₁ (x y : R) : R := W.a₁ + 2 * W.tangentSlope x y

def flexForm (x y : R) : R :=
  W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
    - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2

noncomputable def deuringVariableChange (x₁ y₁ : R) (u : Rˣ) : VariableChange R :=
  ⟨u, x₁, W.tangentSlope x₁ y₁, y₁⟩

noncomputable def levelThreeModulus (x₁ y₁ x₂ : R) : R :=
  W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁)

noncomputable def levelThreeAbscissa (x₁ y₁ x₂ : R) : R :=
  (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2

noncomputable def levelThreeOrdinate (x₁ y₁ x₂ y₂ : R) : R :=
  (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 3

section ring

variable {W}

/--
@isnad1 id=eq.0h4v.s6.8746cb8e2980 from=translated src=- shape=92247b7a vocab=275fb53c
-/
theorem deuringA₃_def (x y : R) : W.deuringA₃ x y = 2 * y + W.a₁ * x + W.a₃ := rfl

/--
@isnad1 id=eq.0h4v.s7.52bdd31c4440 from=translated src=- shape=a38c0ee3 vocab=45821540
-/
theorem tangentSlopeNum_def (x y : R) :
    W.tangentSlopeNum x y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := rfl

/--
@isnad1 id=eq.0h4v.s5.68af3eae8005 from=translated src=- shape=c6456a2a vocab=e4416b48
-/
theorem tangentSlope_def (x y : R) :
    W.tangentSlope x y = W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x y) := rfl

/--
@isnad1 id=eq.0h4v.s6.03da3c31d4bc from=translated src=- shape=659d3a45 vocab=a67864c7
-/
theorem deuringA₁_def (x y : R) : W.deuringA₁ x y = W.a₁ + 2 * W.tangentSlope x y := rfl

/--
@isnad1 id=eq.0h4v.s7.789811333c49 from=translated src=- shape=8b9718c3 vocab=3194acbf
-/
theorem flexForm_def (x y : R) : W.flexForm x y =
    W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
      - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2 := rfl

/--
@isnad1 id=eq.0h5v.s6.e18e59c79e67 from=translated src=- shape=426d4325 vocab=2aef5e39
-/
theorem levelThreeModulus_def (x₁ y₁ x₂ : R) : W.levelThreeModulus x₁ y₁ x₂ =
    W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁) := rfl

/--
@isnad1 id=eq.0h5v.s6.59d4b37f9778 from=translated src=- shape=7b3861e2 vocab=a3fb530e
-/
theorem levelThreeAbscissa_def (x₁ y₁ x₂ : R) : W.levelThreeAbscissa x₁ y₁ x₂ =
    (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2 := rfl

/--
@isnad1 id=eq.0h6v.s7.9b731dfde51d from=translated src=- shape=ef62cb71 vocab=411e87cc
-/
theorem levelThreeOrdinate_def (x₁ y₁ x₂ y₂ : R) : W.levelThreeOrdinate x₁ y₁ x₂ y₂ =
    (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3
      * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 3 := rfl

/--
@isnad1 id=eq.0h5v.s5.3e77f89ce008 from=translated src=- shape=162251b2 vocab=71ebc9cd
-/
@[simp] theorem deuringVariableChange_u (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).u = u := rfl
/--
@isnad1 id=eq.0h5v.s5.7a7655188a1d from=translated src=- shape=c123dc89 vocab=8733fbee
-/
@[simp] theorem deuringVariableChange_r (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).r = x₁ := rfl
/--
@isnad1 id=eq.0h5v.s5.af2d738adb3b from=translated src=- shape=7c5e5881 vocab=5cfc4153
-/
@[simp] theorem deuringVariableChange_s (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).s = W.tangentSlope x₁ y₁ := rfl
/--
@isnad1 id=eq.0h5v.s5.4832545329e0 from=translated src=- shape=60e31544 vocab=299f37f9
-/
@[simp] theorem deuringVariableChange_t (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).t = y₁ := rfl

/--
@isnad1 id=eq.0h4v.s5.1becbfe05d29 from=translated src=- shape=8e0b9f9d vocab=dfae2350
-/
theorem deuringA₃_eq_sub_negY (x y : R) : W.deuringA₃ x y = y - W.toAffine.negY x y := by
  rw [deuringA₃_def, Affine.negY]; change 2 * y + W.a₁ * x + W.a₃ = y - (-y - W.a₁ * x - W.a₃); ring

/--
@isnad1 id=eq.0h4v.s5.d04aba97e4f0 from=translated src=- shape=7fd490ac vocab=30257ee1
-/
theorem tangentSlopeNum_eq_neg_evalEval_polynomialX (x y : R) :
    W.tangentSlopeNum x y = -W.toAffine.polynomialX.evalEval x y := by
  rw [Affine.evalEval_polynomialX, tangentSlopeNum_def]; change _ = -(W.a₁ * y - _); ring

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

/--
@isnad1 id=eq.1h4v.s7.26a126663638 from=translated src=- shape=84b91563 vocab=2d0f57e7
-/
theorem map_ringInverse_of_isUnit {a : R} (h : IsUnit a) : f (Ring.inverse a) = Ring.inverse (f a) := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit, show f (u : R) = ((Units.map (f : R →* S) u : Sˣ) : S) from rfl,
    Ring.inverse_unit]
  rfl

/--
@isnad1 id=eq.0h6v.s7.73df5b6f6873 from=translated src=- shape=f535ec2d vocab=d24dbc8a
-/
theorem deuringA₃_map (x y : R) : (W.map f).deuringA₃ (f x) (f y) = f (W.deuringA₃ x y) := by
  simp [deuringA₃_def, map_ofNat]

/--
@isnad1 id=eq.0h6v.s7.04c26c3210d1 from=translated src=- shape=f535ec2d vocab=546d8898
-/
theorem tangentSlopeNum_map (x y : R) :
    (W.map f).tangentSlopeNum (f x) (f y) = f (W.tangentSlopeNum x y) := by
  simp [tangentSlopeNum_def, map_ofNat]

/--
@isnad1 id=eq.0h6v.s7.cf5b489d98ac from=translated src=- shape=f535ec2d vocab=7b40e0c0
-/
theorem flexForm_map (x y : R) : (W.map f).flexForm (f x) (f y) = f (W.flexForm x y) := by
  simp [flexForm_def, tangentSlopeNum_map, deuringA₃_map, map_ofNat]

/--
@isnad1 id=eq.1h6v.s7.12b333b3df12 from=translated src=- shape=61a58cb9 vocab=2812ca00
-/
theorem tangentSlope_map_of_isUnit {x y : R} (h : IsUnit (W.deuringA₃ x y)) :
    (W.map f).tangentSlope (f x) (f y) = f (W.tangentSlope x y) := by
  rw [tangentSlope_def, tangentSlope_def, tangentSlopeNum_map, deuringA₃_map, map_mul,
    map_ringInverse_of_isUnit f h]

/--
@isnad1 id=eq.1h6v.s7.27d7146eb992 from=translated src=- shape=61a58cb9 vocab=667b78df
-/
theorem deuringA₁_map_of_isUnit {x y : R} (h : IsUnit (W.deuringA₃ x y)) :
    (W.map f).deuringA₁ (f x) (f y) = f (W.deuringA₁ x y) := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_map_of_isUnit f h]; simp [map_ofNat]

/--
@isnad1 id=eq.1h7v.s7.48e56703a041 from=translated src=- shape=f087c816 vocab=9faac7ac
-/
theorem levelThreeModulus_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ : R) :
    (W.map f).levelThreeModulus (f x₁) (f y₁) (f x₂) = f (W.levelThreeModulus x₁ y₁ x₂) := by
  rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₁_map_of_isUnit f h, deuringA₃_map,
    ← map_ringInverse_of_isUnit f h]
  simp

/--
@isnad1 id=eq.1h7v.s7.daaca5a64b7a from=translated src=- shape=f087c816 vocab=d6f09295
-/
theorem levelThreeAbscissa_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ : R) :
    (W.map f).levelThreeAbscissa (f x₁) (f y₁) (f x₂) = f (W.levelThreeAbscissa x₁ y₁ x₂) := by
  rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_map, ← map_ringInverse_of_isUnit f h]
  simp

/--
@isnad1 id=eq.1h8v.s8.8f6fd995cedc from=translated src=- shape=cce579e5 vocab=7423acbf
-/
theorem levelThreeOrdinate_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ y₂ : R) :
    (W.map f).levelThreeOrdinate (f x₁) (f y₁) (f x₂) (f y₂) = f (W.levelThreeOrdinate x₁ y₁ x₂ y₂) := by
  rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_map, tangentSlope_map_of_isUnit f h,
    ← map_ringInverse_of_isUnit f h]
  simp

end map

/--
@isnad1 id=eq.0h5v.s8.bbc85ab9241b from=translated src=- shape=0c8cb5db vocab=cc3fc331
-/
theorem deuringA₃_variableChange (C : VariableChange R) (x y : R) :
    W.deuringA₃ ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).deuringA₃ x y := by
  simp only [deuringA₃_def, variableChange_a₁, variableChange_a₃]
  linear_combination -((W.a₁ + 2 * C.s) * x * (C.u : R) ^ 2) * C.u.inv_mul
    - (W.a₃ + C.r * W.a₁ + 2 * C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul

/--
@isnad1 id=eq.0h5v.s8.cf300fc6f3f3 from=translated src=- shape=df115721 vocab=f2951ee7
-/
theorem tangentSlopeNum_variableChange (C : VariableChange R) (x y : R) :
    W.tangentSlopeNum ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 4 * (C • W).tangentSlopeNum x y + C.s * (C.u : R) ^ 3 * (C • W).deuringA₃ x y := by
  simp only [tangentSlopeNum_def, deuringA₃_def, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄]
  linear_combination -(2 * (C.u : R) ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * x)
      * pow_mul_pow_eq_one 2 C.u.inv_mul
    - (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t)
      * pow_mul_pow_eq_one 4 C.u.inv_mul
    + ((C.u : R) ^ 3 * (W.a₁ + 2 * C.s) * y - C.s * (C.u : R) ^ 2 * (W.a₁ + 2 * C.s) * x)
      * C.u.inv_mul
    - C.s * (W.a₃ + C.r * W.a₁ + 2 * C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul

/--
@isnad1 id=eq.0h5v.s8.f06f530c30c2 from=translated src=- shape=0c8cb5db vocab=645d88e4
-/
theorem flexForm_variableChange (C : VariableChange R) (x y : R) :
    W.flexForm ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 8 * (C • W).flexForm x y := by
  rw [flexForm_def, flexForm_def, tangentSlopeNum_variableChange, deuringA₃_variableChange]
  have ha₁ : W.a₁ = (C.u : R) * (C • W).a₁ - 2 * C.s := by
    rw [variableChange_a₁]; linear_combination -(W.a₁ + 2 * C.s) * C.u.inv_mul
  have ha₂ : W.a₂ + 3 * ((C.u : R) ^ 2 * x + C.r)
      = (C.u : R) ^ 2 * ((C • W).a₂ + 3 * x) + C.s * W.a₁ + C.s ^ 2 := by
    rw [variableChange_a₂]
    linear_combination -(W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * pow_mul_pow_eq_one 2 C.u.inv_mul
  rw [ha₂, ha₁]
  ring

end ring

section field

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

/--
@isnad1 id=eq.0h4v.s5.197731d6683e from=translated src=- shape=0abcd7ab vocab=c39c1330
-/
theorem tangentSlope_eq_div (x y : F) :
    W.tangentSlope x y = W.tangentSlopeNum x y / W.deuringA₃ x y := by
  rw [tangentSlope_def, Ring.inverse_eq_inv, div_eq_mul_inv]

/--
@isnad1 id=eq.1h4v.s5.ff6ee945888f from=translated src=- shape=2fd598a2 vocab=388b0686
-/
theorem tangentSlope_eq_slope [DecidableEq F] {x y : F} (h : W.deuringA₃ x y ≠ 0) :
    W.tangentSlope x y = W.toAffine.slope x x y y := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy; apply h; rw [deuringA₃_eq_sub_negY, ← hy, sub_self]
  rw [Affine.slope_of_Y_ne rfl hy, ← deuringA₃_eq_sub_negY, tangentSlope_eq_div]; rfl

/--
@isnad1 id=eq.0h5v.s7.5ef63ba9728f from=translated src=- shape=ba2a8fa1 vocab=3c4e5917
-/
theorem levelThreeModulus_eq_div (x₁ y₁ x₂ : F) : W.levelThreeModulus x₁ y₁ x₂ =
    (W.a₁ * W.deuringA₃ x₁ y₁ + 2 * W.tangentSlopeNum x₁ y₁) * (x₂ - x₁) / W.deuringA₃ x₁ y₁ ^ 2 := by
  rw [levelThreeModulus_def, deuringA₁_def, tangentSlope_eq_div, Ring.inverse_eq_inv]
  by_cases h : W.deuringA₃ x₁ y₁ = 0
  · rw [h]; simp
  · field_simp

/--
@isnad1 id=eq.0h5v.s6.34f12eb935de from=translated src=- shape=f63295a9 vocab=97be3a3c
-/
theorem levelThreeAbscissa_eq_div (x₁ y₁ x₂ : F) :
    W.levelThreeAbscissa x₁ y₁ x₂ = (x₂ - x₁) ^ 3 / W.deuringA₃ x₁ y₁ ^ 2 := by
  rw [levelThreeAbscissa_def, Ring.inverse_eq_inv, div_eq_mul_inv, inv_pow]

/--
@isnad1 id=eq.0h6v.s7.8fef07d896fc from=translated src=- shape=621a0028 vocab=a3227635
-/
theorem levelThreeOrdinate_eq_div (x₁ y₁ x₂ y₂ : F) : W.levelThreeOrdinate x₁ y₁ x₂ y₂ =
    (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 / W.deuringA₃ x₁ y₁ ^ 3 := by
  rw [levelThreeOrdinate_def, Ring.inverse_eq_inv, div_eq_mul_inv, inv_pow]

section map

variable {K : Type*} [Field K] (φ : F →+* K)

/--
@isnad1 id=eq.0h6v.s7.ff567950cb38 from=translated src=- shape=f535ec2d vocab=04984f2d
-/
theorem tangentSlope_map (x y : F) : (W.map φ).tangentSlope (φ x) (φ y) = φ (W.tangentSlope x y) := by
  rw [tangentSlope_eq_div, tangentSlope_eq_div, tangentSlopeNum_map, deuringA₃_map, map_div₀]

/--
@isnad1 id=eq.0h7v.s8.69d7132d7ac8 from=translated src=- shape=27047cd8 vocab=51a170d7
-/
theorem levelThreeModulus_map (x₁ y₁ x₂ : F) :
    (W.map φ).levelThreeModulus (φ x₁) (φ y₁) (φ x₂) = φ (W.levelThreeModulus x₁ y₁ x₂) := by
  rw [levelThreeModulus_eq_div, levelThreeModulus_eq_div, tangentSlopeNum_map, deuringA₃_map]
  simp [map_ofNat, map_div₀]

/--
@isnad1 id=eq.0h7v.s8.5f78cb60ceba from=translated src=- shape=27047cd8 vocab=169853d1
-/
theorem levelThreeAbscissa_map (x₁ y₁ x₂ : F) :
    (W.map φ).levelThreeAbscissa (φ x₁) (φ y₁) (φ x₂) = φ (W.levelThreeAbscissa x₁ y₁ x₂) := by
  rw [levelThreeAbscissa_eq_div, levelThreeAbscissa_eq_div, deuringA₃_map]
  simp [map_div₀]

/--
@isnad1 id=eq.0h8v.s8.df0a315f40ec from=translated src=- shape=6fb669cf vocab=ae73d424
-/
theorem levelThreeOrdinate_map (x₁ y₁ x₂ y₂ : F) :
    (W.map φ).levelThreeOrdinate (φ x₁) (φ y₁) (φ x₂) (φ y₂) = φ (W.levelThreeOrdinate x₁ y₁ x₂ y₂) := by
  rw [levelThreeOrdinate_eq_div, levelThreeOrdinate_eq_div, deuringA₃_map, tangentSlope_map]
  simp [map_div₀]

end map

/--
@isnad1 id=eq.3h5v.s7.3ef33ab1b2ed from=translated src=- shape=80c2bf26 vocab=e08bf4db
-/
theorem deuringVariableChange_smul {x₁ y₁ : F} (heq : W.toAffine.Equation x₁ y₁)
    (hΨ : W.deuringA₃ x₁ y₁ ≠ 0) (hflex : W.flexForm x₁ y₁ = 0) (u : Fˣ) :
    W.deuringVariableChange x₁ y₁ u • W =
      deuringCurve (W.deuringA₁ x₁ y₁ / u) (W.deuringA₃ x₁ y₁ / (u : F) ^ 3) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rw [Affine.equation_iff] at heq
  set m := W.tangentSlope x₁ y₁ with hm
  have hmd : m * W.deuringA₃ x₁ y₁ = W.tangentSlopeNum x₁ y₁ := by
    rw [hm, tangentSlope_eq_div, div_mul_cancel₀ _ hΨ]
  have hfl : m ^ 2 + W.a₁ * m - W.a₂ - 3 * x₁ = 0 := by
    have h : (m ^ 2 + W.a₁ * m - W.a₂ - 3 * x₁) * W.deuringA₃ x₁ y₁ ^ 2 = W.flexForm x₁ y₁ := by
      rw [flexForm_def, ← hmd]; ring
    rw [hflex] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hΨ)
  rw [deuringA₃_def] at hmd hΨ
  rw [tangentSlopeNum_def] at hmd
  ext
  · simp only [variableChange_a₁, deuringVariableChange, deuringCurve_a₁, deuringA₁_def,
      Units.val_inv_eq_inv_val, ← hm]
    field_simp
  · simp only [variableChange_a₂, deuringVariableChange, deuringCurve_a₂, Units.val_inv_eq_inv_val,
      ← hm]
    rw [show W.a₂ - m * W.a₁ + 3 * x₁ - m ^ 2 = 0 by linear_combination -hfl, mul_zero]
  · simp only [variableChange_a₃, deuringVariableChange, deuringCurve_a₃, deuringA₃_def,
      Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [variableChange_a₄, deuringVariableChange, deuringCurve_a₄, Units.val_inv_eq_inv_val,
      ← hm]
    rw [show W.a₄ - m * W.a₃ + 2 * x₁ * W.a₂ - (y₁ + x₁ * m) * W.a₁ + 3 * x₁ ^ 2 - 2 * m * y₁ = 0 by
      linear_combination -hmd, mul_zero]
  · simp only [variableChange_a₆, deuringVariableChange, deuringCurve_a₆, Units.val_inv_eq_inv_val]
    rw [show W.a₆ + x₁ * W.a₄ + x₁ ^ 2 * W.a₂ + x₁ ^ 3 - y₁ * W.a₃ - y₁ ^ 2 - x₁ * y₁ * W.a₁ = 0 by
      linear_combination -heq, mul_zero]

/--
@isnad1 id=eq.5h6v.s7.610606f84a82 from=translated src=- shape=8d7f81a8 vocab=37ff9ad8
-/
theorem deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus {x₁ y₁ x₂ : F}
    (heq : W.toAffine.Equation x₁ y₁) (hΨ : W.deuringA₃ x₁ y₁ ≠ 0) (hflex : W.flexForm x₁ y₁ = 0)
    (hx : x₁ ≠ x₂) (u : Fˣ) (hu : (u : F) = W.deuringA₃ x₁ y₁ / (x₂ - x₁)) :
    W.deuringVariableChange x₁ y₁ u • W =
      deuringCurve (W.levelThreeModulus x₁ y₁ x₂) (W.levelThreeAbscissa x₁ y₁ x₂) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [deuringVariableChange_smul heq hΨ hflex u, hu, levelThreeModulus_def, levelThreeAbscissa_def,
    Ring.inverse_eq_inv]
  congr 1
  · field_simp
  · field_simp

/--
@isnad1 id=eq.1h5v.s8.2d5f86b15d91 from=translated src=- shape=c0d1bbc9 vocab=6bf2cbe8
-/
theorem tangentSlope_variableChange (C : VariableChange F) {x y : F} (h : (C • W).deuringA₃ x y ≠ 0) :
    W.tangentSlope ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).tangentSlope x y + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [tangentSlope_eq_div, tangentSlope_eq_div, tangentSlopeNum_variableChange,
    deuringA₃_variableChange]
  field_simp

/--
@isnad1 id=eq.1h5v.s8.7364b3993a89 from=translated src=- shape=613ed559 vocab=ffaf0ce4
-/
theorem deuringA₁_variableChange (C : VariableChange F) {x y : F} (h : (C • W).deuringA₃ x y ≠ 0) :
    W.deuringA₁ ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).deuringA₁ x y := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_variableChange C h, variableChange_a₁,
    Units.val_inv_eq_inv_val]
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  field_simp
  ring

/--
@isnad1 id=eq.0h6v.s8.65d9df214ea5 from=translated src=- shape=3286a11c vocab=648bee56
-/
theorem levelThreeModulus_variableChange (C : VariableChange F) (x₁ y₁ x₂ : F) :
    W.levelThreeModulus ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).levelThreeModulus x₁ y₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₃_variableChange,
      deuringA₁_variableChange C h, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    field_simp
    ring

/--
@isnad1 id=eq.0h6v.s8.83e23ad50eab from=translated src=- shape=3286a11c vocab=63743405
-/
theorem levelThreeAbscissa_variableChange (C : VariableChange F) (x₁ y₁ x₂ : F) :
    W.levelThreeAbscissa ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).levelThreeAbscissa x₁ y₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_variableChange, Ring.inverse_eq_inv,
      Ring.inverse_eq_inv]
    field_simp
    ring

/--
@isnad1 id=eq.0h7v.s9.b425ba978176 from=translated src=- shape=5de44a4d vocab=6077db0c
-/
theorem levelThreeOrdinate_variableChange (C : VariableChange F) (x₁ y₁ x₂ y₂ : F) :
    W.levelThreeOrdinate ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C • W).levelThreeOrdinate x₁ y₁ x₂ y₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_variableChange,
      tangentSlope_variableChange C h, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    field_simp
    ring

/--
@isnad1 id=eq.0h3v.s5.aabc3f8101fa from=translated src=- shape=b9bc3e17 vocab=bffbc1fb
-/
theorem deuringA₃_deuringCurve_zero (τ ν : F) : (deuringCurve τ ν).deuringA₃ 0 0 = ν := by
  simp [deuringA₃_def]

/--
@isnad1 id=eq.0h3v.s6.b4f7c51e3e53 from=translated src=- shape=b54489f9 vocab=c55da1a7
-/
theorem tangentSlope_deuringCurve_zero (τ ν : F) : (deuringCurve τ ν).tangentSlope 0 0 = 0 := by
  simp [tangentSlope_eq_div, tangentSlopeNum_def]

/--
@isnad1 id=eq.1h3v.s6.43d7d8332a06 from=translated src=- shape=89f8be47 vocab=fe397cee
-/
theorem levelThreeModulus_deuringCurve {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeModulus 0 0 ν = τ := by
  rw [levelThreeModulus_def, deuringA₁_def, tangentSlope_deuringCurve_zero, deuringA₃_deuringCurve_zero,
    Ring.inverse_eq_inv]
  simp only [deuringCurve_a₁, mul_zero, add_zero, sub_zero]
  field_simp

/--
@isnad1 id=eq.1h3v.s6.ba464e8f7580 from=translated src=- shape=a57329c9 vocab=03a7e405
-/
theorem levelThreeAbscissa_deuringCurve {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeAbscissa 0 0 ν = ν := by
  rw [levelThreeAbscissa_eq_div, deuringA₃_deuringCurve_zero, sub_zero]
  field_simp

/--
@isnad1 id=eq.1h4v.s6.5eec65920f3a from=translated src=- shape=34a98f2f vocab=647b06be
-/
theorem levelThreeOrdinate_deuringCurve {τ ν : F} (hν : ν ≠ 0) (η : F) :
    (deuringCurve τ ν).levelThreeOrdinate 0 0 ν η = η := by
  rw [levelThreeOrdinate_eq_div, deuringA₃_deuringCurve_zero, tangentSlope_deuringCurve_zero]
  field_simp
  ring

/--
@isnad1 id=eq.0h4v.s8.5c0e98aba61b from=translated src=- shape=688c0853 vocab=a53154c8
-/
theorem flexForm_deuringCurve (τ ν η : F) :
    (deuringCurve τ ν).flexForm ν η =
      -(τ ^ 2 + 12 * ν) * (deuringCurve τ ν).toAffine.polynomial.evalEval ν η
        - ν ^ 3 * (3 * ν + τ ^ 2 + 3 * τ + 3) := by
  rw [Affine.evalEval_polynomial, flexForm_def, tangentSlopeNum_def, deuringA₃_def]
  simp only [deuringCurve_a₁, deuringCurve_a₂, deuringCurve_a₃, deuringCurve_a₄, deuringCurve_a₆]
  change _ = -(τ ^ 2 + 12 * ν) * (η ^ 2 + τ * ν * η + ν * η - (ν ^ 3 + 0 * ν ^ 2 + 0 * ν + 0)) - _
  ring

end field

end WeierstrassCurve
