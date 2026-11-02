import Tengoku.Seed.LinearAlgebra.Multilinear.Basis
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms cubicPolar_diagonal` (it only prints; the queue checks the axioms of every declaration). -/

/-! The cubic Newton residual and its genuine trilinear polarization. -/

noncomputable section
namespace AlbertLean.Generic.SourceCubicTrace

variable {K : Type*} [Field K] [CharZero K]

def cubicResidual {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one x : V) : V :=
  (6 : K) • μ x (μ x x) - (6 * T x) • μ x x +
    (3 * (T x)^2 - 3 * T (μ x x)) • x -
    ((T x)^3 - 3 * T x * T (μ x x) + 2 * T (μ x (μ x x))) • one

def cubicPolar {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one a b c : V) : V :=
  cubicResidual μ T one (a + b + c) - cubicResidual μ T one (a + b) -
  cubicResidual μ T one (a + c) - cubicResidual μ T one (b + c) +
  cubicResidual μ T one a + cubicResidual μ T one b +
  cubicResidual μ T one c - cubicResidual μ T one 0

/-- One ordered trilinear term whose diagonal is the cubic residual.-/
def cubicTrilinearTerm {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one a b c : V) : V :=
  (6 : K) • μ a (μ b c) - (6 * T a) • μ b c +
    (3 * T a * T b) • c - (3 * T (μ a b)) • c -
    (T a * T b * T c - 3 * T a * T (μ b c) +
      2 * T (μ a (μ b c))) • one

/-- Six-permutation symmetrization of the ordered trilinear term.-/
def cubicSymPolar {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one a b c : V) : V :=
  cubicTrilinearTerm μ T one a b c + cubicTrilinearTerm μ T one a c b +
  cubicTrilinearTerm μ T one b a c + cubicTrilinearTerm μ T one b c a +
  cubicTrilinearTerm μ T one c a b + cubicTrilinearTerm μ T one c b a

theorem cubicPolar_eq_cubicSymPolar {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one a b c : V) :
    cubicPolar μ T one a b c = cubicSymPolar μ T one a b c := by
  simp [cubicPolar, cubicResidual, cubicSymPolar, cubicTrilinearTerm,
    map_add, smul_add, add_smul]
  module

def cubicPolarMap {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one : V) :
    MultilinearMap K (fun _ : Fin 3 => V) V :=
  MultilinearMap.mk'
    (fun v => cubicSymPolar μ T one (v 0) (v 1) (v 2))
    (by
      intro v i x y
      fin_cases i <;>
        simp [cubicSymPolar, cubicTrilinearTerm, Function.update_apply, map_add,
          LinearMap.add_apply] <;> module)
    (by
      intro v i r x
      fin_cases i <;>
        simp [cubicSymPolar, cubicTrilinearTerm, Function.update_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul] <;> module)

@[simp] theorem cubicPolarMap_apply {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one : V)
    (v : Fin 3 → V) :
    cubicPolarMap μ T one v = cubicPolar μ T one (v 0) (v 1) (v 2) := by
  exact (cubicPolar_eq_cubicSymPolar μ T one (v 0) (v 1) (v 2)).symm

theorem cubicPolar_diagonal {V : Type*} [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (T : V →ₗ[K] K) (one x : V) :
    cubicPolar μ T one x x x = (6 : K) • cubicResidual μ T one x := by
  rw [cubicPolar_eq_cubicSymPolar]
  simp [cubicSymPolar, cubicTrilinearTerm, cubicResidual]
  module

end AlbertLean.Generic.SourceCubicTrace
