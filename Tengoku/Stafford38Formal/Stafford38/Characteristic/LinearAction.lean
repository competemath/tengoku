module
public import Tengoku.Stafford38Formal.Stafford38.Characteristic.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms symbolLinearCombination` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgHom` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgHom_X` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgHom_C` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgHom_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgHom_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgEquivOfInverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgEquivOfInverse_X` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgEquivOfInverse_symm_X` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-!
# Linear substitutions on polynomial phase space

A square matrix acts on the phase-space polynomial ring by substituting its
row-linear combination for each variable. Composition is contravariant in the
matrix order, matching the Weyl-generator substitution convention. Explicit
mutual inverse certificates produce an algebra equivalence.
-/

namespace Stafford38.CharacteristicLinearAction

open Stafford38.Characteristic

noncomputable section

universe u

variable (k : Type u) [Field k]

def symbolLinearCombination {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    SymbolRing k n :=
  ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

def symbolLinearAlgHom {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) :
    SymbolRing k n →ₐ[k] SymbolRing k n :=
  MvPolynomial.aeval (symbolLinearCombination k M)

/--
@isnad1 id=eq.0h4v.s8.49fa214e5bfd from=translated src=- shape=f0c5c88a vocab=5b277c14
-/
@[simp] theorem symbolLinearAlgHom_X {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    symbolLinearAlgHom k M (MvPolynomial.X i) =
      symbolLinearCombination k M i := by
  rw [symbolLinearAlgHom, MvPolynomial.aeval_X]

/--
@isnad1 id=eq.0h4v.s9.585b2b59818f from=translated src=- shape=210a8d11 vocab=5de6127e
-/
@[simp] theorem symbolLinearAlgHom_C {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (c : k) :
    symbolLinearAlgHom k M (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [symbolLinearAlgHom, MvPolynomial.aeval_C]
  rfl

/--
@isnad1 id=eq.0h4v.s8.00e9abcccf5a from=translated src=- shape=3f13e874 vocab=7d9e3040
-/
theorem symbolLinearAlgHom_comp {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k) :
    (symbolLinearAlgHom k M).comp (symbolLinearAlgHom k N) =
      symbolLinearAlgHom k (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, symbolLinearAlgHom_X, symbolLinearAlgHom_X]
  simp only [symbolLinearCombination, map_sum, map_mul,
    symbolLinearAlgHom_C, symbolLinearAlgHom_X, Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h2v.s8.6487db33f0d2 from=translated src=- shape=da56106b vocab=a0f20f4a
-/
theorem symbolLinearAlgHom_one {n : ℕ} :
    symbolLinearAlgHom k (1 : Matrix (PhaseVar n) (PhaseVar n) k) =
      AlgHom.id k (SymbolRing k n) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [symbolLinearCombination, Matrix.one_apply]

/-- The polynomial substitution equivalence attached to explicitly certified
inverse matrices.-/
def symbolLinearAlgEquivOfInverse {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    SymbolRing k n ≃ₐ[k] SymbolRing k n :=
  AlgEquiv.ofAlgHom (symbolLinearAlgHom k M) (symbolLinearAlgHom k N)
    (by rw [symbolLinearAlgHom_comp, hNM, symbolLinearAlgHom_one])
    (by rw [symbolLinearAlgHom_comp, hMN, symbolLinearAlgHom_one])

/--
@isnad1 id=eq.2h5v.s9.cfc7b5e87caa from=translated src=- shape=e2b4735a vocab=378dc46c
-/
@[simp] theorem symbolLinearAlgEquivOfInverse_X {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : PhaseVar n) :
    symbolLinearAlgEquivOfInverse k M N hMN hNM (MvPolynomial.X i) =
      symbolLinearCombination k M i :=
  symbolLinearAlgHom_X k M i

/--
@isnad1 id=eq.2h5v.s9.827b7786c660 from=translated src=- shape=5790f847 vocab=3237f5de
-/
@[simp] theorem symbolLinearAlgEquivOfInverse_symm_X {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : PhaseVar n) :
    (symbolLinearAlgEquivOfInverse k M N hMN hNM).symm
        (MvPolynomial.X i) = symbolLinearCombination k N i :=
  symbolLinearAlgHom_X k N i

/- Exact statement pins for matrix order and both substitutions. -/

end

end Stafford38.CharacteristicLinearAction
