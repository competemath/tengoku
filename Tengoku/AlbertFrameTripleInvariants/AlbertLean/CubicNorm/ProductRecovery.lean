import Tengoku.AlbertFrameTripleInvariants.AlbertLean.CubicNorm.TraceDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms RecoveryData.adjoint_characterization` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RecoveryData.cross_characterization` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RecoveryData.map_product` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Product recovery from cubic-norm data

This is source-independent infrastructure.  It records the normalization
`P(x,x,x)=6N(x)`, hence `dNₓ(y)=P(x,x,y)/2`, by building the gradient with
the literal factor `1/2`.  No Albert coordinate model occurs in this file.
-/

namespace AlbertLean.CubicNorm

open Module

variable (K V : Type*) [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- Linear data sufficient to recover a cubic-norm product.-/
structure RecoveryData where
  traceForm : V →ₗ[K] V →ₗ[K] K
  polar : V →ₗ[K] V →ₗ[K] V →ₗ[K] K
  trace : V →ₗ[K] K
  one : V
  traceForm_nondegenerate : LeftNondegenerate traceForm

namespace RecoveryData

variable {K V}
variable (D : RecoveryData K V)

/-- The cubic gradient with the locked finite-difference normalization.-/
def gradient (x : V) : Module.Dual K V := (2 : K)⁻¹ • D.polar x x

@[simp] theorem gradient_apply (x y : V) : D.gradient x y = D.polar x x y / 2 := by
  simp [gradient, div_eq_mul_inv, mul_comm]

/-- The trace-dual adjoint of the cubic gradient.-/
noncomputable def adjoint [FiniteDimensional K V] (x : V) : V :=
  (traceDualEquiv D.traceForm D.traceForm_nondegenerate).symm (D.gradient x)

/-- The adjoint is characterized without reference to a basis.-/
theorem adjoint_characterization [FiniteDimensional K V] (x y : V) :
    D.traceForm (D.adjoint x) y = D.polar x x y / 2 := by
  rw [adjoint, traceDualEquiv_symm_apply_apply, gradient_apply]

/-- Polarization of the adjoint.-/
noncomputable def cross [FiniteDimensional K V] (x y : V) : V :=
  D.adjoint (x + y) - D.adjoint x - D.adjoint y

/-- The bilinear spur associated with trace and trace form.-/
def spurBilinear (x y : V) : K := D.trace x * D.trace y - D.traceForm x y

/-- The canonical cubic-norm product.-/
noncomputable def product [FiniteDimensional K V] (x y : V) : V :=
  (2 : K)⁻¹ •
    (D.cross x y + D.trace x • y + D.trace y • x - D.spurBilinear x y • D.one)

theorem cross_characterization [FiniteDimensional K V] (x y z : V) :
    D.traceForm (D.cross x y) z =
      (D.polar x y z + D.polar y x z) / 2 := by
  simp only [cross, map_sub, LinearMap.sub_apply]
  rw [D.adjoint_characterization, D.adjoint_characterization,
    D.adjoint_characterization]
  simp [div_eq_mul_inv]
  ring

theorem cross_comm [FiniteDimensional K V] (x y : V) : D.cross x y = D.cross y x := by
  simp only [cross, add_comm]
  abel

theorem cross_add_left [FiniteDimensional K V] (x₁ x₂ y : V) :
    D.cross (x₁ + x₂) y = D.cross x₁ y + D.cross x₂ y := by
  apply sub_eq_zero.mp
  apply D.traceForm_nondegenerate
  intro z
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
  rw [D.cross_characterization, D.cross_characterization,
    D.cross_characterization]
  simp
  ring

theorem cross_smul_left [FiniteDimensional K V] (a : K) (x y : V) :
    D.cross (a • x) y = a • D.cross x y := by
  apply sub_eq_zero.mp
  apply D.traceForm_nondegenerate
  intro z
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [D.cross_characterization, D.cross_characterization]
  simp
  ring

theorem spurBilinear_add_left (x₁ x₂ y : V) :
    D.spurBilinear (x₁ + x₂) y =
      D.spurBilinear x₁ y + D.spurBilinear x₂ y := by
  simp [spurBilinear]
  ring

theorem spurBilinear_smul_left (a : K) (x y : V) :
    D.spurBilinear (a • x) y = a * D.spurBilinear x y := by
  simp [spurBilinear]
  ring

theorem product_add_left [FiniteDimensional K V] (x₁ x₂ y : V) :
    D.product (x₁ + x₂) y = D.product x₁ y + D.product x₂ y := by
  simp only [product, cross_add_left, map_add, spurBilinear_add_left,
    add_smul]
  module

theorem product_smul_left [FiniteDimensional K V] (a : K) (x y : V) :
    D.product (a • x) y = a • D.product x y := by
  simp only [product, cross_smul_left, map_smul, spurBilinear_smul_left,
    smul_add, smul_sub, smul_smul]
  module

/-- Commutativity requires only symmetry of the trace form.-/
theorem product_comm [FiniteDimensional K V]
    (hB : ∀ x y, D.traceForm x y = D.traceForm y x) (x y : V) :
    D.product x y = D.product y x := by
  simp only [product, cross_comm]
  have hS : D.spurBilinear x y = D.spurBilinear y x := by
    rw [spurBilinear, spurBilinear, hB]
    ring
  rw [hS]
  module

theorem product_add_right [FiniteDimensional K V]
    (hB : ∀ x y, D.traceForm x y = D.traceForm y x) (x y₁ y₂ : V) :
    D.product x (y₁ + y₂) = D.product x y₁ + D.product x y₂ := by
  calc
    D.product x (y₁ + y₂) = D.product (y₁ + y₂) x := D.product_comm hB _ _
    _ = D.product y₁ x + D.product y₂ x := D.product_add_left _ _ _
    _ = D.product x y₁ + D.product x y₂ := by
      rw [D.product_comm hB y₁ x, D.product_comm hB y₂ x]

theorem product_smul_right [FiniteDimensional K V]
    (hB : ∀ x y, D.traceForm x y = D.traceForm y x) (a : K) (x y : V) :
    D.product x (a • y) = a • D.product x y := by
  calc
    D.product x (a • y) = D.product (a • y) x := D.product_comm hB _ _
    _ = a • D.product y x := D.product_smul_left _ _ _
    _ = a • D.product x y := by rw [D.product_comm hB y x]

/-- Adjoint recovery commutes with any equivalence preserving both forms.-/
theorem map_adjoint
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (E : RecoveryData K W) (e : V ≃ₗ[K] W)
    (hB : ∀ x y, E.traceForm (e x) (e y) = D.traceForm x y)
    (hP : ∀ x y z, E.polar (e x) (e y) (e z) = D.polar x y z)
    (x : V) : e (D.adjoint x) = E.adjoint (e x) := by
  apply sub_eq_zero.mp
  apply E.traceForm_nondegenerate
  intro w
  obtain ⟨y, rfl⟩ := e.surjective w
  simp only [map_sub, LinearMap.sub_apply]
  rw [hB, D.adjoint_characterization, E.adjoint_characterization, hP]
  ring

theorem map_cross
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (E : RecoveryData K W) (e : V ≃ₗ[K] W)
    (hB : ∀ x y, E.traceForm (e x) (e y) = D.traceForm x y)
    (hP : ∀ x y z, E.polar (e x) (e y) (e z) = D.polar x y z)
    (x y : V) : e (D.cross x y) = E.cross (e x) (e y) := by
  simp [cross, D.map_adjoint E e hB hP]

/-- Full product transport under unit, trace-form, trace, and polarization preservation.-/
theorem map_product
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (E : RecoveryData K W) (e : V ≃ₗ[K] W)
    (hOne : e D.one = E.one)
    (hTrace : ∀ x, E.trace (e x) = D.trace x)
    (hB : ∀ x y, E.traceForm (e x) (e y) = D.traceForm x y)
    (hP : ∀ x y z, E.polar (e x) (e y) (e z) = D.polar x y z)
    (x y : V) : e (D.product x y) = E.product (e x) (e y) := by
  simp only [product, map_smul, map_add, map_sub, D.map_cross E e hB hP,
    hTrace, spurBilinear, hB, hOne]

end RecoveryData

end AlbertLean.CubicNorm
