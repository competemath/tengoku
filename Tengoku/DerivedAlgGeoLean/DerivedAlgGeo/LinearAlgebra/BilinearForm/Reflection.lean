/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.LinearAlgebra.BilinearForm.Isometry
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reflection in a vector of norm minus two

For a module `M` over a commutative ring `R` with a bilinear form `B`, and a
vector `s` with `B s s = -2`, the map

```
ρ_s(v) = v + B v s • s
```

is the reflection in the hyperplane `s^⊥`. The `-2` is what makes the usual
formula `v - 2⟪v,s⟫/⟪s,s⟫ · s` integral: the denominator cancels the `2`, so no
division is needed and the reflection is defined on the module rather than on
its rationalisation.

## This is stated over an arbitrary ambient form, not over one extension

`Lattice/Mukai/Reflection.lean` used to own this argument on the single
carrier `ℤ × N × ℤ`, even though nothing in it is about that carrier: every
step is bilinearity, symmetry, or the one hypothesis `B s s = -2`. It is
restated here on `(R, M, B)`, and the Mukai file specialises it at
`B := Mukai.pairingBilin b`. There is one reflection, not two.

**This is not the spherical twist.** On a K3 surface the Seidel--Thomas twist
`T_E` acts on the Mukai lattice as `ρ_{v(E)}`, and that statement is the
eventual reason this theory exists. But `T_E` is an autoequivalence of
`Dᵇ(Coh X)`, its construction needs an evaluation triangle and a functorial
cone, and none of that is available here or asserted here.

## Which hypothesis does what

The split is not the expected one, and stating it over an arbitrary form is
what makes it visible:

* **additivity** needs neither symmetry of `B` nor `B s s = -2`. It is
  bilinearity alone, so `reflectHom` is a linear map for *every* `s`;
* **involutivity** needs `B s s = -2` and nothing else;
* **isometry** needs symmetry of `B` as well, and fails without it -- the two
  cross terms only cancel against `B v s * B w s * B s s` once they are equal.

`-2` is the hypothesis rather than a `IsSpherical`-style predicate on purpose:
spherical-class vocabulary is application vocabulary, and it stays with the
application.
-/

namespace BilinearForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : M →ₗ[R] M →ₗ[R] R)

/-- Reflection in `s`: `ρ_s(v) = v + B v s • s`.

For `B s s = -2` this is the reflection in `s^⊥`; for other `s` it is still a
well-defined additive map, but is neither an involution nor an isometry. The
definition deliberately takes no hypothesis so that `reflectHom` below is
available unconditionally.-/
def reflect (s v : M) : M := v + B v s • s

/--
@isnad1 id=eq.0h5v.s9.96b3d380ee60 from=translated src=- shape=9157eabf vocab=2157ae81
-/
theorem reflect_apply (s v : M) : reflect B s v = v + B v s • s := rfl

/--
@isnad1 id=eq.0h4v.s7.f9f05f2b55f6 from=translated src=- shape=261f5e0c vocab=371f1606
-/
@[simp] theorem reflect_zero (s : M) : reflect B s 0 = 0 := by simp [reflect]

/--
@isnad1 id=eq.0h6v.s8.0e7810efc9ae from=translated src=- shape=7d4a3c83 vocab=c909fff0
-/
theorem reflect_add (s v w : M) :
    reflect B s (v + w) = reflect B s v + reflect B s w := by
  simp only [reflect, map_add, LinearMap.add_apply, add_smul]
  abel

/--
@isnad1 id=eq.0h6v.s8.a66d5593899c from=translated src=- shape=9dd90de4 vocab=7fcb9db4
-/
theorem reflect_smul (a : R) (s v : M) :
    reflect B s (a • v) = a • reflect B s v := by
  simp only [reflect, map_smul, LinearMap.smul_apply, smul_add, smul_eq_mul,
    mul_smul]

/--
@isnad1 id=eq.0h5v.s7.394abc8436e4 from=translated src=- shape=d0a5a0a3 vocab=88a4f742
-/
theorem reflect_neg (s v : M) : reflect B s (-v) = -reflect B s v := by
  simp only [reflect, map_neg, LinearMap.neg_apply, neg_smul, neg_add_rev]
  abel

/-- `ρ_s` as a linear endomorphism.

No hypothesis on `s`: additivity is bilinearity of `B`, nothing more.-/
def reflectHom (s : M) : M →ₗ[R] M where
  toFun := reflect B s
  map_add' := reflect_add B s
  map_smul' := by intro a v; simpa using reflect_smul B a s v

/--
@isnad1 id=eq.0h5v.s8.056f37d6319d from=translated src=- shape=5cf6be54 vocab=14bcd45a
-/
@[simp] theorem reflectHom_apply (s v : M) : reflectHom B s v = reflect B s v := rfl

/--
@isnad1 id=eq.1h5v.s10.d740fe6fff2c from=translated src=- shape=601a88e2 vocab=d487894d
-/
theorem apply_reflect_right (s : M) (hs : B s s = -2) (v : M) :
    B (reflect B s v) s = -B v s := by
  rw [reflect, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hs]
  ring

/--
@isnad1 id=eq.1h5v.s9.7fc997017bb9 from=translated src=- shape=b8d615a8 vocab=d487894d
-/
theorem reflect_reflect (s : M) (hs : B s s = -2) (v : M) :
    reflect B s (reflect B s v) = v := by
  conv_lhs => rw [reflect, apply_reflect_right B s hs, reflect]
  rw [neg_smul]
  abel

/--
@isnad1 id=involuti.1h4v.s9.973b7cef2130 from=translated src=- shape=ef0df69e vocab=1cde1ea9
-/
theorem reflect_involutive (s : M) (hs : B s s = -2) :
    Function.Involutive (reflect B s) := reflect_reflect B s hs

/--
@isnad1 id=bijectiv.1h4v.s9.dd2e956684bb from=translated src=- shape=d0ccbeed vocab=f0e5c3d0
-/
theorem reflect_bijective (s : M) (hs : B s s = -2) :
    Function.Bijective (reflect B s) := (reflect_involutive B s hs).bijective

/-- `ρ_s` as a linear automorphism, with itself as inverse. Needs
`B s s = -2`, which is what makes it an involution.-/
def reflectEquiv (s : M) (hs : B s s = -2) : M ≃ₗ[R] M :=
  { reflectHom B s with
    invFun := reflect B s
    left_inv := reflect_reflect B s hs
    right_inv := reflect_reflect B s hs }

/--
@isnad1 id=eq.1h5v.s9.1bebbb20982a from=translated src=- shape=c53f09d0 vocab=d583ff0f
-/
@[simp] theorem reflectEquiv_apply (s : M) (hs : B s s = -2) (v : M) :
    reflectEquiv B s hs v = reflect B s v := rfl

/--
@isnad1 id=eq.1h5v.s9.81f274db9983 from=translated src=- shape=c69d4fc6 vocab=6561457f
-/
@[simp] theorem reflectEquiv_symm_apply (s : M) (hs : B s s = -2) (v : M) :
    (reflectEquiv B s hs).symm v = reflect B s v := rfl

/--
@isnad1 id=eq.1h4v.s9.dd1d138b1bd7 from=translated src=- shape=61faee4d vocab=d487894d
-/
@[simp] theorem reflect_self (s : M) (hs : B s s = -2) : reflect B s s = -s := by
  rw [reflect, hs]
  module

/--
@isnad1 id=eq.1h5v.s9.e238f2fff1a5 from=translated src=- shape=82c8e49b vocab=7f88c2f3
-/
theorem reflect_of_apply_eq_zero {s v : M} (h : B v s = 0) : reflect B s v = v := by
  rw [reflect, h, zero_smul, add_zero]

/--
@isnad1 id=iff.1h5v.s10.7a82b4c0cbad from=translated src=- shape=494931ac vocab=d487894d
-/
theorem apply_reflect_eq_zero_iff (s : M) (hs : B s s = -2) (v : M) :
    B (reflect B s v) s = 0 ↔ B v s = 0 := by
  rw [apply_reflect_right B s hs, neg_eq_zero]

/--
@isnad1 id=eq.2h6v.s11.e974621647c9 from=translated src=- shape=742360a0 vocab=d487894d
-/
theorem apply_reflect_reflect (hb : ∀ x y : M, B x y = B y x)
    (s : M) (hs : B s s = -2) (v w : M) :
    B (reflect B s v) (reflect B s w) = B v w := by
  have hsw : B s w = B w s := hb s w
  simp only [reflect, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hs, hsw]
  ring

/--
@isnad1 id=eq.2h5v.s11.cc346b56bb46 from=translated src=- shape=ab188404 vocab=d487894d
-/
theorem self_reflect (hb : ∀ x y : M, B x y = B y x) (s : M) (hs : B s s = -2)
    (v : M) : B (reflect B s v) (reflect B s v) = B v v :=
  apply_reflect_reflect B hb s hs v v

/-- `ρ_s` as an isometry of `B`. This is the first statement to need symmetry
of `B` as well as `B s s = -2`.-/
def reflectIsometry (hb : ∀ x y : M, B x y = B y x) (s : M) (hs : B s s = -2) :
    B →bᵢ B where
  toLinearMap := reflectHom B s
  map_app' v w := apply_reflect_reflect B hb s hs v w

/--
@isnad1 id=eq.2h5v.s10.2767be0c4791 from=translated src=- shape=78d942d4 vocab=a596e718
-/
@[simp] theorem reflectIsometry_apply (hb : ∀ x y : M, B x y = B y x)
    (s : M) (hs : B s s = -2) (v : M) :
    reflectIsometry B hb s hs v = reflect B s v := rfl

/--
@isnad1 id=eq.0h5v.s7.2007ef30684b from=translated src=- shape=6bddec89 vocab=88a4f742
-/
@[simp] theorem reflect_neg_left (s v : M) : reflect B (-s) v = reflect B s v := by
  simp only [reflect, map_neg, neg_smul, smul_neg, neg_neg]

end BilinearForm
