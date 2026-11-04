import Tengoku.Seed.LinearAlgebra.BilinearMap
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms polarizationMap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms polarization_diagonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms polarization_eq_alternating` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms polarizationMap_eq_zero_of_residual_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Polarization of the Jordan identity

The formulas hold for any bilinear product. Every nonassociative word
retains its parentheses; no associative multiplication on `V` is assumed.
The six-term polarization is four-linear and specializes on its cubic
diagonal to six times the Jordan residual.
-/

noncomputable section
namespace AlbertLean.Generic.JordanPolarization

universe u v
variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Cubic in x and linear in y; the exact bracket convention is literal.-/
def residual (μ : V →ₗ[K] V →ₗ[K] V) (x y : V) : V :=
  μ (μ x y) (μ x x) - μ x (μ y (μ x x))

/-- One four-linear word difference; its diagonal is the Jordan residual.-/
def term (μ : V →ₗ[K] V →ₗ[K] V) (a b c y : V) : V :=
  μ (μ a y) (μ b c) - μ a (μ y (μ b c))

/-- The six permutations of the three cubic slots, each appearing once.-/
def polarization (μ : V →ₗ[K] V →ₗ[K] V) (a b c y : V) : V :=
  term μ a b c y + term μ a c b y +
  term μ b a c y + term μ b c a y +
  term μ c a b y + term μ c b a y

/-- Actual four-linearity in the pinned MultilinearMap interface. The four
cases below are argument positions, not basis vectors or structure constants.-/
def polarizationMap (μ : V →ₗ[K] V →ₗ[K] V) :
    MultilinearMap K (fun _ : Fin 4 => V) V :=
  MultilinearMap.mk'
    (fun z => polarization μ (z 0) (z 1) (z 2) (z 3))
    (by
      intro z i a b
      fin_cases i <;>
        simp [polarization, term, Function.update_apply, map_add,
          LinearMap.add_apply] <;> abel)
    (by
      intro z i r a
      fin_cases i <;>
        simp [polarization, term, Function.update_apply, map_smul,
          LinearMap.smul_apply, smul_add, smul_sub])

/--
@isnad1 id=eq.0h4v.s8.fe7901af5260 from=translated src=- shape=f8bad030 vocab=1d3b6956
-/
@[simp] theorem polarizationMap_apply
    (μ : V →ₗ[K] V →ₗ[K] V) (z : Fin 4 → V) :
    polarizationMap μ z = polarization μ (z 0) (z 1) (z 2) (z 3) := rfl

/-- On the cubic diagonal each of the six terms is exactly the residual.
@isnad1 id=eq.0h5v.s8.0d92e785b4d6 from=translated src=- shape=4c05b1c1 vocab=3a22e427
-/
theorem polarization_diagonal (μ : V →ₗ[K] V →ₗ[K] V) (x y : V) :
    polarization μ x x x y = (6 : K) • residual μ x y := by
  dsimp only [polarization, term, residual]
  module

/-- The eight-subset polarization formula, including its identically zero
empty-subset term. It needs bilinearity alone, not commutativity or division.
@isnad1 id=eq.0h7v.s8.f77dcb0429a4 from=translated src=- shape=226bc5c1 vocab=fc9e18a2
-/
theorem polarization_eq_alternating
    (μ : V →ₗ[K] V →ₗ[K] V) (a b c y : V) :
    polarization μ a b c y =
      residual μ (a + b + c) y - residual μ (a + b) y -
      residual μ (a + c) y - residual μ (b + c) y +
      residual μ a y + residual μ b y + residual μ c y - residual μ 0 y := by
  simp only [polarization, term, residual, map_add, map_zero,
    LinearMap.add_apply, LinearMap.zero_apply]
  abel

/-- An all-vector Jordan identity implies the corresponding four-linear
identity, ready for a separately proved structure-constant extension.
@isnad1 id=eq.1h7v.s7.fee2d4844353 from=translated src=- shape=f29e9a9c vocab=f5530fe5
-/
theorem polarization_eq_zero_of_residual_eq_zero
    (μ : V →ₗ[K] V →ₗ[K] V) (h : ∀ x y, residual μ x y = 0)
    (a b c y : V) : polarization μ a b c y = 0 := by
  rw [polarization_eq_alternating]
  simp only [h, sub_zero, add_zero]

/--
@isnad1 id=eq.1h3v.s8.d0290e70510d from=translated src=- shape=15982511 vocab=14b3ceb2
-/
theorem polarizationMap_eq_zero_of_residual_eq_zero
    (μ : V →ₗ[K] V →ₗ[K] V) (h : ∀ x y, residual μ x y = 0) :
    polarizationMap μ = 0 := by
  ext z
  exact polarization_eq_zero_of_residual_eq_zero μ h (z 0) (z 1) (z 2) (z 3)

end AlbertLean.Generic.JordanPolarization
