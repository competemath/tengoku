import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

universe u v

variable {F : Type u} {k : Type v} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

theorem Affine.Point.some_congr' {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

def mapPoint : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[simp]
lemma mapPoint_zero : mapPoint f (0 : W₀.toAffine.Point) = 0 :=
  rfl

lemma mapPoint_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h)
      = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

theorem mapPoint_add [DecidableEq F] [DecidableEq k] (P Q : W₀.toAffine.Point) :
    mapPoint f (P + Q) = mapPoint f P + mapPoint f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, mapPoint_zero, mapPoint_some,
      mapPoint_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, mapPoint_some, mapPoint_some, mapPoint_some,
      Affine.Point.add_some hxy']
    exact Affine.Point.some_congr' (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

@[simps]
def mapPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := mapPoint f
  map_zero' := rfl
  map_add' := mapPoint_add f

theorem mapPoint_nsmul [DecidableEq F] [DecidableEq k] (n : ℕ) (P : W₀.toAffine.Point) :
    mapPoint f (n • P) = n • mapPoint f P :=
  map_nsmul (mapPointHom f (W₀ := W₀)) n P

end WeierstrassCurve
