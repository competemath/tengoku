import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Presentation
import Tengoku

namespace OAI

/-!
# The polynomial algebra structure of the zero fiber

Composing elimination, lifting, the plane parametrization, and a permutation
of variables gives the complex algebra isomorphism with `ℂ[X,Y,T]`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial Presentation

def variableOrder : Fin 3 ≃ Fin 3 where
  toFun := ![2,0,1]
  invFun := ![1,2,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def flattenPlane : Polynomial (MvPolynomial (Fin 2) ℂ) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 2).symm.trans (renameEquiv ℂ variableOrder)

/--
@isnad1 id=eq.0h0v.s10.6361d5ee2a05 from=translated src=- shape=1fdd1edf vocab=a610a9f8
-/
@[simp] theorem flattenPlane_symm_X0 : flattenPlane.symm (X 0) = Polynomial.C (X 0) := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 0)) = _
  rw [rename_X]
  exact finSuccEquiv_X_succ (j := (0 : Fin 2))

/--
@isnad1 id=eq.0h0v.s10.d0bb5440abf7 from=translated src=- shape=1fdd1edf vocab=a610a9f8
-/
@[simp] theorem flattenPlane_symm_X1 : flattenPlane.symm (X 1) = Polynomial.C (X 1) := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 1)) = _
  rw [rename_X]
  exact finSuccEquiv_X_succ (j := (1 : Fin 2))

/--
@isnad1 id=eq.0h0v.s9.5cce977603a9 from=translated src=- shape=5b93649f vocab=f5e6133f
-/
@[simp] theorem flattenPlane_symm_X2 : flattenPlane.symm (X 2) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 2)) = _
  rw [rename_X]
  exact finSuccEquiv_X_zero

/--
@isnad1 id=eq.0h0v.s9.c2669f390441 from=translated src=- shape=6d707e2e vocab=68057558
-/
@[simp] theorem flattenPlane_C_X0 : flattenPlane (Polynomial.C (X 0)) = X 0 := by
  apply flattenPlane.symm.injective
  simp
/--
@isnad1 id=eq.0h0v.s9.f42acf190b1c from=translated src=- shape=6d707e2e vocab=68057558
-/
@[simp] theorem flattenPlane_C_X1 : flattenPlane (Polynomial.C (X 1)) = X 1 := by
  apply flattenPlane.symm.injective
  simp
/--
@isnad1 id=eq.0h0v.s9.65dee4bc8446 from=translated src=- shape=7001f36f vocab=b6ae1e17
-/
@[simp] theorem flattenPlane_X : flattenPlane Polynomial.X = X 2 := by
  apply flattenPlane.symm.injective
  simp

def liftedEquiv : L ≃ₐ[ℂ] Polynomial B :=
  (Lifting.equivalence hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Plane.relation_cusp ℂ) (Plane.bezout ℂ)).restrictScalars ℂ

def planeExtensionEquiv : Polynomial B ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 2) ℂ) :=
  Polynomial.mapAlgEquiv (Plane.equivalence ℂ)

def fiberEquiv : (R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  Presentation.eliminationEquiv.symm.trans
    (liftedEquiv.trans (planeExtensionEquiv.trans flattenPlane))

end AbhyankarSathaye

end

end OAI
