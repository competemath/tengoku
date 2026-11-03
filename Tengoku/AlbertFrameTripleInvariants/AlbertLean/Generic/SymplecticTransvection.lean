import Tengoku.Seed.LinearAlgebra.BilinearMap
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms skew_of_alternating` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_neg_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms equiv_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms one_step_align` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms two_step_align` (it only prints; the queue checks the axioms of every declaration). -/

/-! Elementary symplectic transvections over an arbitrary field.

This file deliberately uses only a bilinear alternating form.  It does not
assume finite dimension, nondegeneracy, a matrix model, or a rank theorem.
-/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

abbrev BilinForm := V →ₗ[K] V →ₗ[K] K

def map (omega : BilinForm (K := K) (V := V)) (d : V) (t : K) : V →ₗ[K] V where
  toFun x := x + (t * omega d x) • d
  map_add' x y := by
    simp only [map_add, smul_add, add_assoc]
    module
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply, smul_add, smul_smul]
    module

@[simp] theorem map_apply
    (omega : BilinForm (K := K) (V := V)) (d : V) (t : K) (x : V) :
    map omega d t x = x + (t * omega d x) • d := rfl

theorem skew_of_alternating
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x y : V) :
    omega x y = -omega y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  have hxx := halt x
  have hyy := halt y
  linear_combination h - hxx - hyy

theorem map_preserves
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) (x y : V) :
    omega (map omega d t x) (map omega d t y) = omega x y := by
  have hskew := skew_of_alternating omega halt d x
  have hdd := halt d
  simp only [map_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (norm := ring) (t * omega d y) * hskew +
    (t ^ 2 * omega d x * omega d y) * hdd

theorem map_neg_comp
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) :
    (map omega d (-t)).comp (map omega d t) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hdd := halt d
  simp only [LinearMap.comp_apply, map_apply, LinearMap.id_apply, map_add,
    map_smul, smul_eq_mul]
  rw [hdd]
  module

theorem map_comp_neg
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) :
    (map omega d t).comp (map omega d (-t)) = LinearMap.id := by
  simpa only [neg_neg] using map_neg_comp omega halt d (-t)

def equiv
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (map omega d t) (map omega d (-t))
    (map_comp_neg omega halt d t) (map_neg_comp omega halt d t)

@[simp] theorem equiv_apply
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) (x : V) :
    equiv omega halt d t x = x + (t * omega d x) • d := rfl

@[simp] theorem equiv_symm_apply
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) (x : V) :
    (equiv omega halt d t).symm x = x + ((-t) * omega d x) • d := rfl

theorem equiv_preserves
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (d : V) (t : K) (x y : V) :
    omega (equiv omega halt d t x) (equiv omega halt d t y) = omega x y :=
  map_preserves omega halt d t x y

/-! If `omega y x` is nonzero, one transvection sends `x` to `y` provided
the two vectors have the same alternating self-pairing (automatically zero).
The coefficient is a field-point choice; the universal map itself is polynomial.
-/
theorem one_step_align
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x y : V)
    (hpair : omega y x ≠ 0) :
    equiv omega halt (y - x) (omega y x)⁻¹ x = y := by
  have hxx := halt x
  have hcancel : (omega y x)⁻¹ * omega y x = 1 := inv_mul_cancel₀ hpair
  simp only [equiv_apply, map_sub, LinearMap.sub_apply, hxx, sub_zero]
  rw [hcancel, one_smul]
  module

/-! The elementary two-vector detour used by the fixed-schedule argument. -/
theorem two_step_align
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0) :
    equiv omega halt (y - z) (omega y z)⁻¹
      (equiv omega halt (z - x) (omega z x)⁻¹ x) = y := by
  rw [one_step_align omega halt x z hxz]
  exact one_step_align omega halt z y hzy

end AlbertLean.Generic.SymplecticTransvection
