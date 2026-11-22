import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option linter.style.header false

/-!
# Point maps induced by Weierstrass variable changes

An admissible variable change of Weierstrass equations induces the expected
coordinate equivalence on affine elliptic-curve points.  This file packages
that algebraic equivalence and proves compatibility with the group law.
-/

noncomputable section
namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- The Weierstrass equation transforms under the documented affine coordinate
map `(x, y) ↦ (u²x + r, u³y + u²sx + t)`.
@isnad1 id=iff.0h5v.s8.a9efb2d90351 from=translated src=- shape=3d732024 vocab=dd6b77d4
-/
theorem variableChange_equation_iff (W : WeierstrassCurve F)
    (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r)
        (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  rw [Affine.equation_iff, Affine.equation_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  constructor <;> intro h <;> linear_combination h

namespace VariableChange

variable (C : VariableChange F)

/-- The inverse x-coordinate for the affine coordinate map of `C`. -/
def inverseX (x : F) : F :=
  (C.u⁻¹ : F) ^ 2 * (x - C.r)

/-- The inverse y-coordinate for the affine coordinate map of `C`. -/
def inverseY (x y : F) : F :=
  (C.u⁻¹ : F) ^ 3 * (y - C.s * (x - C.r) - C.t)

/--
@isnad1 id=eq.0h3v.s6.c931fab15921 from=translated src=- shape=6e591722 vocab=036128ff
-/
@[simp] theorem forward_inverseX (x : F) :
    (C.u : F) ^ 2 * C.inverseX x + C.r = x := by
  simp only [inverseX]
  field_simp [Units.ne_zero]
  ring

/--
@isnad1 id=eq.0h4v.s7.f4f09c92375d from=translated src=- shape=2c8cf345 vocab=6017b044
-/
@[simp] theorem forward_inverseY (x y : F) :
    (C.u : F) ^ 3 * C.inverseY x y +
        (C.u : F) ^ 2 * C.s * C.inverseX x + C.t = y := by
  simp only [inverseX, inverseY]
  field_simp [Units.ne_zero]
  ring

/--
@isnad1 id=eq.0h3v.s6.8dbac9d182d1 from=translated src=- shape=e2053b6f vocab=036128ff
-/
@[simp] theorem inverseX_forward (x : F) :
    C.inverseX ((C.u : F) ^ 2 * x + C.r) = x := by
  simp only [inverseX]
  field_simp [Units.ne_zero]
  ring

/--
@isnad1 id=eq.0h4v.s8.76bad9ed5ce5 from=translated src=- shape=1fe1bc1f vocab=6d86de0b
-/
@[simp] theorem inverseY_forward (x y : F) :
    C.inverseY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) = y := by
  simp only [inverseY]
  field_simp [Units.ne_zero]
  ring

/-- Negation commutes with the affine coordinate transformation.
@isnad1 id=eq.0h5v.s8.c5411dc08409 from=translated src=- shape=b9cdc04f vocab=f0eb7a4b
-/
theorem negY_forward (W : WeierstrassCurve F) (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.negY x y +
        (C.u : F) ^ 2 * C.s * x + C.t := by
  simp only [Affine.negY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- The x-coordinate addition formula commutes with an admissible variable
change, provided the slope is transformed by `ℓ ↦ uℓ + s`.
@isnad1 id=eq.0h6v.s8.7e073377499a from=translated src=- shape=29af2d05 vocab=27d803b4
-/
theorem addX_forward (W : WeierstrassCurve F) (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s) =
      (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp only [Affine.addX, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- The y-coordinate addition formula commutes with an admissible variable
change, provided the slope is transformed by `ℓ ↦ uℓ + s`.
@isnad1 id=eq.0h7v.s9.80bc51232157 from=translated src=- shape=eef76c5b vocab=c6a4614c
-/
theorem addY_forward (W : WeierstrassCurve F) (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) * ℓ + C.s) =
      (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ +
        (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX,
    variableChange_a₁, variableChange_a₂, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- A nonvertical secant or tangent slope transforms by `ℓ ↦ uℓ + s`.
@isnad1 id=eq.3h7v.s9.4073c931d0df from=translated src=- shape=e2f8fb29 vocab=d465aa9b
-/
theorem slope_forward [DecidableEq F] (W : WeierstrassCurve F)
    (x₁ x₂ y₁ y₂ : F)
    (h₁ : (C • W).toAffine.Equation x₁ y₁)
    (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t) =
      (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h ↦ hxy ⟨hx, h⟩
    have hy_eq : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst x₂
    subst y₂
    have hY :
        (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t ≠
          W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [C.negY_forward W]
      intro h
      apply hy
      apply mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u))
      linear_combination h
    have hden : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hDen :
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) -
          W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ≠ 0 :=
      sub_ne_zero.mpr hY
    rw [Affine.slope_of_Y_ne rfl hY, Affine.slope_of_Y_ne rfl hy]
    apply (div_eq_iff hDen).2
    field_simp [hden, Units.ne_zero]
    simp only [Affine.negY, variableChange_a₁, variableChange_a₂,
      variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero]
    ring
  · have hX : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      intro h
      apply hx
      apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero C.u))
      linear_combination h
    rw [Affine.slope_of_X_ne hX, Affine.slope_of_X_ne hx]
    field_simp [Units.ne_zero, hx]
    ring

variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- The map on affine elliptic-curve points induced by an admissible variable
change. The point at infinity is fixed and finite coordinates transform by
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def pointMap : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((variableChange_equation_iff W C x y).mp h.1)

/--
@isnad1 id=eq.0h3v.s6.d9dbde1983cf from=translated src=- shape=d65f84fb vocab=bf70f1c1
-/
@[simp] theorem pointMap_zero : C.pointMap W .zero = .zero := rfl

/--
@isnad1 id=eq.1h5v.s8.b8fa6a63b2e8 from=translated src=- shape=cff2fa27 vocab=3e85f906
-/
@[simp] theorem pointMap_some (x y : F) (h : (C • W).toAffine.Nonsingular x y) :
    C.pointMap W (.some x y h) =
      .mk ((variableChange_equation_iff W C x y).mp h.1) := rfl

/-- The point map induced by an admissible variable change preserves the
elliptic-curve group law.
@isnad1 id=eq.0h5v.s8.5a0b58457649 from=translated src=- shape=2d3d257a vocab=3e9eebd0
-/
theorem pointMap_add [DecidableEq F] (P Q : (C • W).toAffine.Point) :
    C.pointMap W (P + Q) = C.pointMap W P + C.pointMap W Q := by
  classical
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · rfl
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · rfl
  let X₁ := (C.u : F) ^ 2 * x₁ + C.r
  let X₂ := (C.u : F) ^ 2 * x₂ + C.r
  let Y₁ := (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
  let Y₂ := (C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · have hX : X₁ = X₂ := by simp only [X₁, X₂, hxy.1]
    have hY : Y₁ = W.toAffine.negY X₂ Y₂ := by
      simp only [X₂, Y₁, Y₂]
      rw [C.negY_forward W, hxy.1, hxy.2]
    rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    simp only [pointMap_some, Affine.Point.mk]
    exact (Affine.Point.add_of_Y_eq hX hY).symm
  · have hX_of_eq : X₁ = X₂ → x₁ = x₂ := by
      intro h
      apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero C.u))
      dsimp only [X₁, X₂] at h
      linear_combination h
    have hXY : ¬(X₁ = X₂ ∧ Y₁ = W.toAffine.negY X₂ Y₂) := by
      rintro ⟨hX, hY⟩
      apply hxy
      have hx := hX_of_eq hX
      refine ⟨hx, ?_⟩
      dsimp only [X₁, X₂, Y₁, Y₂] at hY
      rw [C.negY_forward W] at hY
      apply mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u))
      rw [hx] at hY
      linear_combination hY
    rw [Affine.Point.add_some hxy]
    simp only [pointMap_some, Affine.Point.mk]
    rw [Affine.Point.add_some hXY]
    have hslope := C.slope_forward W x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    dsimp only [X₁, X₂, Y₁, Y₂] at hslope ⊢
    rw [Affine.Point.some.injEq]
    constructor
    · rw [hslope, C.addX_forward W]
    · rw [hslope, C.addY_forward W]

/-- The inverse point map, written in explicit affine coordinates. -/
def inversePointMap : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((variableChange_equation_iff W C (C.inverseX x) (C.inverseY x y)).mpr <| by
      simpa using h.1)

/--
@isnad1 id=eq.0h3v.s6.92dd64f59e8f from=translated src=- shape=8338c018 vocab=4f843a36
-/
@[simp] theorem inversePointMap_zero : C.inversePointMap W .zero = .zero := rfl

/--
@isnad1 id=eq.1h5v.s7.86bd7b4300f8 from=translated src=- shape=81742254 vocab=af891ffb
-/
@[simp] theorem inversePointMap_some (x y : F) (h : W.toAffine.Nonsingular x y) :
    C.inversePointMap W (.some x y h) =
      .mk ((variableChange_equation_iff W C (C.inverseX x) (C.inverseY x y)).mpr <| by
        simpa using h.1) := rfl

/-- The equivalence of affine point types induced by an admissible variable
change of Weierstrass equations. -/
def pointEquiv : (C • W).toAffine.Point ≃ W.toAffine.Point where
  toFun := C.pointMap W
  invFun := C.inversePointMap W
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · change Affine.Point.some
        (C.inverseX ((C.u : F) ^ 2 * x + C.r))
        (C.inverseY ((C.u : F) ^ 2 * x + C.r)
          ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)) _ =
          Affine.Point.some x y h
      congr <;> simp
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · change Affine.Point.some
        ((C.u : F) ^ 2 * C.inverseX x + C.r)
        ((C.u : F) ^ 3 * C.inverseY x y +
          (C.u : F) ^ 2 * C.s * C.inverseX x + C.t) _ =
          Affine.Point.some x y h
      congr <;> simp

/--
@isnad1 id=eq.0h4v.s8.f27700c6659f from=translated src=- shape=c1aa86c9 vocab=5acaf89d
-/
@[simp] theorem pointEquiv_apply (P : (C • W).toAffine.Point) :
    C.pointEquiv W P = C.pointMap W P := rfl

/--
@isnad1 id=eq.0h4v.s8.91187857b4b7 from=translated src=- shape=534a8ba9 vocab=c30816b8
-/
@[simp] theorem pointEquiv_symm_apply (P : W.toAffine.Point) :
    (C.pointEquiv W).symm P = C.inversePointMap W P := rfl

/-- The additive equivalence of affine elliptic-curve points induced by an
admissible variable change. -/
def pointAddEquiv [DecidableEq F] :
    (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toEquiv := C.pointEquiv W
  map_add' := C.pointMap_add W

/--
@isnad1 id=eq.0h4v.s8.545a0caa17a3 from=translated src=- shape=46d11316 vocab=209e5da7
-/
@[simp] theorem pointAddEquiv_apply [DecidableEq F]
    (P : (C • W).toAffine.Point) :
    C.pointAddEquiv W P = C.pointMap W P := rfl

/--
@isnad1 id=eq.0h4v.s8.8d43a5de9a87 from=translated src=- shape=cc272a2a vocab=35f22f09
-/
@[simp] theorem pointAddEquiv_symm_apply [DecidableEq F]
    (P : W.toAffine.Point) :
    (C.pointAddEquiv W).symm P = C.inversePointMap W P := rfl

end VariableChange
end WeierstrassCurve
