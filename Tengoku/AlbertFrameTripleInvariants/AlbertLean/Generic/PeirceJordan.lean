import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.JordanPolarization
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.PeircePolynomial
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms peirce_operator_cubic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflection_square_certificate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflection_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflection_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflectionEquiv` (it only prints; the queue checks the axioms of every declaration). -/

/-! Peirce reflection from the Jordan identity.  The seven-term certificate
below is replayed as an ordinary Lean equality; the search is not trusted. -/

noncomputable section
namespace AlbertLean.Generic.PeirceJordan

open JordanPolarization PeircePolynomial

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {A : Type v} [AddCommGroup A] [Module K A]

variable (μ : A →ₗ[K] A →ₗ[K] A)
variable (hcomm : ∀ x y, μ x y = μ y x)

/--
@isnad1 id=eq.1h7v.s8.8ec2e45a4450 from=translated src=- shape=021382d3 vocab=7787b706
-/
theorem polarization_zero
    (hJordan : ∀ x y, residual μ x y = 0) (a b c y : A) :
    polarization μ a b c y = 0 :=
  polarization_eq_zero_of_residual_eq_zero μ hJordan a b c y

include hcomm in
/-- The idempotent multiplication-operator cubic, obtained by specializing
the genuine six-term polarization rather than assuming a Peirce polynomial.
@isnad1 id=eq.3h5v.s12.6862c8d5ab46 from=translated src=- shape=3dc2ed97 vocab=159cc941
-/
theorem peirce_operator_cubic
    (hJordan : ∀ x y, residual μ x y = 0)
    (p : A) (hp : μ p p = p) (x : A) :
    (2 : K) • μ p (μ p (μ p x)) -
      (3 : K) • μ p (μ p x) + μ p x = 0 := by
  have hP := polarization_zero μ hJordan p p x p
  dsimp only [polarization, term] at hP
  simp only [hp] at hP
  simp only [hcomm] at hP
  linear_combination (norm := module) (-1 / 2 : K) • hP

include hcomm in
/-- Exact seven-term certificate found externally and checked here by direct
expansion in the free commutative nonassociative product modulo `p²=p`.
@isnad1 id=eq.2h5v.s12.b02060f7a107 from=translated src=- shape=c3022947 vocab=75dd080a
-/
theorem reflection_square_certificate
    (p : A) (hp : μ p p = p) (x : A) :
    reflection μ p (μ x x) - μ (reflection μ p x) (reflection μ p x) =
        (8 : K) • polarization μ p p (μ p x) x -
        (8 : K) • polarization μ p p x (μ p x) -
        (16 : K) • polarization μ p p (μ p x) (μ p x) -
        (4 : K) • polarization μ p x x p +
        (16 : K) • polarization μ p p x (μ p (μ p x)) -
        (8 : K) • μ x (polarization μ p p x p) +
        (16 : K) • μ (μ p x) (polarization μ p p x p) := by
  dsimp only [reflection, polarization, term]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, hp]
  simp only [hcomm]
  module

include hcomm in
/-- The Peirce reflection preserves squares.  Every certificate term vanishes
by the polarization of the all-vector Jordan identity.
@isnad1 id=eq.3h5v.s11.f7d0d1d9409b from=translated src=- shape=0d220fc7 vocab=1b1f5037
-/
theorem reflection_square
    (hJordan : ∀ x y, residual μ x y = 0)
    (p : A) (hp : μ p p = p) (x : A) :
    reflection μ p (μ x x) = μ (reflection μ p x) (reflection μ p x) := by
  apply sub_eq_zero.mp
  rw [reflection_square_certificate μ hcomm p hp x]
  simp only [polarization_zero μ hJordan, smul_zero, sub_zero, add_zero,
    map_zero]

/--
@isnad1 id=eq.0h6v.s8.1b688bdb9db3 from=translated src=- shape=b76afb51 vocab=44255055
-/
theorem reflection_add (p x y : A) :
    reflection μ p (x + y) = reflection μ p x + reflection μ p y := by
  simp [reflection, map_add]
  module

/--
@isnad1 id=eq.0h6v.s8.7f7742a1f870 from=translated src=- shape=efc0f033 vocab=f640ca7d
-/
theorem reflection_smul (p x : A) (c : K) :
    reflection μ p (c • x) = c • reflection μ p x := by
  simp [reflection, map_smul]
  module

include hcomm in
/-- Product preservation follows by polarizing square preservation and
cancelling two; no Peirce fusion table is assumed.
@isnad1 id=eq.3h6v.s11.4021d96b9b42 from=translated src=- shape=d12419a0 vocab=1b1f5037
-/
theorem reflection_mul
    (hJordan : ∀ x y, residual μ x y = 0)
    (p : A) (hp : μ p p = p) (x y : A) :
    reflection μ p (μ x y) = μ (reflection μ p x) (reflection μ p y) := by
  have hxy := reflection_square μ hcomm hJordan p hp (x + y)
  have hx := reflection_square μ hcomm hJordan p hp x
  have hy := reflection_square μ hcomm hJordan p hp y
  simp only [map_add, LinearMap.add_apply, reflection_add μ,
    hcomm y x, hcomm (reflection μ p y) (reflection μ p x)] at hxy
  linear_combination (norm := module)
    (1 / 2 : K) • hxy - (1 / 2 : K) • hx - (1 / 2 : K) • hy

def reflectionLinear (p : A) : A →ₗ[K] A where
  toFun := reflection μ p
  map_add' := reflection_add μ p
  map_smul' := fun c x => reflection_smul μ p x c

def reflectionEquiv
    (hJordan : ∀ x y, residual μ x y = 0)
    (p : A) (hp : μ p p = p) : A ≃ₗ[K] A where
  toLinearMap := reflectionLinear μ p
  invFun := reflection μ p
  left_inv := reflection_reflection μ p (peirce_operator_cubic μ hcomm hJordan p hp)
  right_inv := reflection_reflection μ p (peirce_operator_cubic μ hcomm hJordan p hp)

/--
@isnad1 id=eq.3h5v.s10.2e0ff5ac05e0 from=translated src=- shape=b800d46d vocab=dea78293
-/
@[simp] theorem reflectionEquiv_apply
    (hJordan : ∀ x y, residual μ x y = 0)
    (p : A) (hp : μ p p = p) (x : A) :
    reflectionEquiv μ hcomm hJordan p hp x = reflection μ p x := rfl

/--
@isnad1 id=eq.4h5v.s11.12df326982ad from=translated src=- shape=d117e154 vocab=a8fcc995
-/
theorem reflectionEquiv_unit
    (hJordan : ∀ x y, residual μ x y = 0)
    (one p : A) (hone : μ p one = p) (hp : μ p p = p) :
    reflectionEquiv μ hcomm hJordan p hp one = one := by
  exact reflection_one μ one p hone hp

end AlbertLean.Generic.PeirceJordan
