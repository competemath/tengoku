import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.ExteriorSix
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The concrete exterior-square action in the literal six-coordinate basis

The order remains `12,13,14,23,24,34`.  The determinant-one specialization
preserves the source exterior pairing and the triality contraction.  These
are coordinate consequences of determinant multiplicativity, without a
Spin-group identification.
-/

namespace AlbertLean.Generic.ExteriorAction

open AlbertLean.Triality.ExteriorSix
open scoped BigOperators

variable {K : Type*} [CommRing K]

abbrev Mat4 (K : Type*) := Matrix (Fin 4) (Fin 4) K

def vecAct (g : Mat4 K) (p : U K) : U K := g.mulVec p

/-- Row-covector multiplication; pass the inverse matrix for the dual action.-/
def covAct (h : Mat4 K) (phi : Udual K) : Udual K := Matrix.vecMul phi h

/-- The exterior square, expressed through the six ordered basis wedges.-/
def wedgeAct (g : Mat4 K) (w : W K) : W K :=
  w .i12 • wedge2 (vecAct g (uBasis 0)) (vecAct g (uBasis 1)) +
  w .i13 • wedge2 (vecAct g (uBasis 0)) (vecAct g (uBasis 2)) +
  w .i14 • wedge2 (vecAct g (uBasis 0)) (vecAct g (uBasis 3)) +
  w .i23 • wedge2 (vecAct g (uBasis 1)) (vecAct g (uBasis 2)) +
  w .i24 • wedge2 (vecAct g (uBasis 1)) (vecAct g (uBasis 3)) +
  w .i34 • wedge2 (vecAct g (uBasis 2)) (vecAct g (uBasis 3))

theorem wedge_decomposition (w : W K) :
    w = w .i12 • wedge2 (uBasis 0) (uBasis 1) +
      w .i13 • wedge2 (uBasis 0) (uBasis 2) +
      w .i14 • wedge2 (uBasis 0) (uBasis 3) +
      w .i23 • wedge2 (uBasis 1) (uBasis 2) +
      w .i24 • wedge2 (uBasis 1) (uBasis 3) +
      w .i34 • wedge2 (uBasis 2) (uBasis 3) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis]

/-- Decomposable wedges span the actual six-coordinate carrier.-/
theorem wedge_induction {P : W K → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : K) x, P x → P (a • x))
    (hwedge : ∀ p q, P (wedge2 p q)) (w : W K) : P w := by
  rw [wedge_decomposition w]
  repeat' first | apply hadd | apply hsmul | apply hwedge

@[simp] theorem wedgeAct_zero (g : Mat4 K) : wedgeAct g 0 = 0 := by
  simp [wedgeAct]

theorem wedgeAct_add (g : Mat4 K) (w v : W K) :
    wedgeAct g (w + v) = wedgeAct g w + wedgeAct g v := by
  funext i
  simp [wedgeAct, add_smul]
  ring

theorem wedgeAct_smul (g : Mat4 K) (a : K) (w : W K) :
    wedgeAct g (a • w) = a • wedgeAct g w := by
  funext i
  simp [wedgeAct]
  ring

def wedgeActLinear (g : Mat4 K) : W K →ₗ[K] W K where
  toFun := wedgeAct g
  map_add' := wedgeAct_add g
  map_smul' := wedgeAct_smul g

theorem wedgeAct_wedge2 (g : Mat4 K) (p q : U K) :
    wedgeAct g (wedge2 p q) = wedge2 (vecAct g p) (vecAct g q) := by
  funext i
  fin_cases i <;>
    simp [wedgeAct, wedge2, vecAct, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, uBasis] <;> ring

@[simp] theorem vecAct_one (p : U K) : vecAct (1 : Mat4 K) p = p := by
  simp [vecAct]

theorem vecAct_mul (g h : Mat4 K) (p : U K) :
    vecAct g (vecAct h p) = vecAct (g * h) p := by
  exact Matrix.mulVec_mulVec p g h

theorem wedgeAct_mul (g h : Mat4 K) (w : W K) :
    wedgeAct g (wedgeAct h w) = wedgeAct (g * h) w := by
  conv_lhs => arg 2; unfold wedgeAct
  simp only [wedgeAct_add, wedgeAct_smul, wedgeAct_wedge2, vecAct_mul]
  rfl

@[simp] theorem wedgeAct_one (w : W K) : wedgeAct (1 : Mat4 K) w = w := by
  simpa only [wedgeAct, vecAct_one] using (wedge_decomposition w).symm

theorem wedgeAct_inverse (g h : Mat4 K) (hhg : h * g = 1) (w : W K) :
    wedgeAct h (wedgeAct g w) = w := by
  rw [wedgeAct_mul, hhg, wedgeAct_one]

/-- A specified two-sided matrix inverse supplies the exterior linear equivalence.-/
def wedgeEquiv (g h : Mat4 K) (hgh : g * h = 1) (hhg : h * g = 1) :
    W K ≃ₗ[K] W K where
  toFun := wedgeAct g
  invFun := wedgeAct h
  left_inv := wedgeAct_inverse g h hhg
  right_inv := wedgeAct_inverse h g hgh
  map_add' := wedgeAct_add g
  map_smul' := wedgeAct_smul g

/-- The four vectors are columns, so their order matches the source orientation.-/
def fourColumns (p q r s : U K) : Mat4 K := Matrix.transpose (![p, q, r, s] : Mat4 K)

theorem BW_wedge2_eq_det (p q r s : U K) :
    BW (wedge2 p q) (wedge2 r s) = Matrix.det (fourColumns p q r s) := by
  rw [Matrix.det_succ_row_zero]
  simp [fourColumns, Matrix.transpose, Matrix.det_fin_three, Matrix.submatrix,
    Fin.sum_univ_succ, Fin.succAbove, BW, wedge2] <;> ring

theorem fourColumns_vecAct (g : Mat4 K) (p q r s : U K) :
    fourColumns (vecAct g p) (vecAct g q) (vecAct g r) (vecAct g s) =
      g * fourColumns p q r s := by
  ext i j
  fin_cases j <;>
    simp [fourColumns, Matrix.transpose, vecAct, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

theorem BW_wedgeAct_wedges (g : Mat4 K) (p q r s : U K) :
    BW (wedgeAct g (wedge2 p q)) (wedgeAct g (wedge2 r s)) =
      Matrix.det g * BW (wedge2 p q) (wedge2 r s) := by
  rw [wedgeAct_wedge2, wedgeAct_wedge2, BW_wedge2_eq_det,
    fourColumns_vecAct, Matrix.det_mul, BW_wedge2_eq_det]

/-- Exterior square is a similitude with multiplier `det g`, not its square.-/
theorem BW_wedgeAct (g : Mat4 K) (w v : W K) :
    BW (wedgeAct g w) (wedgeAct g v) = Matrix.det g * BW w v := by
  have hw : ∀ w : W K, ∀ v : W K,
      BW (wedgeAct g w) (wedgeAct g v) = Matrix.det g * BW w v := by
    intro w
    apply wedge_induction (P := fun w => ∀ v : W K,
      BW (wedgeAct g w) (wedgeAct g v) = Matrix.det g * BW w v)
    · intro x y hx hy v
      simp only [wedgeAct_add, BW_add_left, hx, hy, mul_add]
    · intro a x hx v
      simp only [wedgeAct_smul, BW_smul_left, hx]
      ring
    · intro p q v
      apply wedge_induction (P := fun v =>
        BW (wedgeAct g (wedge2 p q)) (wedgeAct g v) =
          Matrix.det g * BW (wedge2 p q) v)
      · intro x y hx hy
        simp only [wedgeAct_add, BW_add_right, hx, hy, mul_add]
      · intro a x hx
        simp only [wedgeAct_smul, BW_smul_right, hx]
        ring
      · intro r s
        exact BW_wedgeAct_wedges g p q r s
  exact hw w v

theorem BW_wedgeAct_of_det_one (g : Mat4 K) (hg : Matrix.det g = 1)
    (w v : W K) : BW (wedgeAct g w) (wedgeAct g v) = BW w v := by
  rw [BW_wedgeAct, hg, one_mul]

theorem evalU_covAct_vecAct (g h : Mat4 K) (hhg : h * g = 1)
    (phi : Udual K) (p : U K) : evalU (covAct h phi) (vecAct g p) = evalU phi p := by
  have eval_dot (a : Udual K) (b : U K) : evalU a b = dotProduct a b := by
    simp [evalU, dotProduct, Fin.sum_univ_succ] <;> ring
  rw [eval_dot, eval_dot]
  change dotProduct (Matrix.vecMul phi h) (g.mulVec p) = dotProduct phi p
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hhg, Matrix.vecMul_one]

theorem pairW_add_left (w v : W K) (zeta : Wdual K) :
    pairW (w + v) zeta = pairW w zeta + pairW v zeta := by
  simp [pairW]
  ring

theorem pairW_smul_left (a : K) (w : W K) (zeta : Wdual K) :
    pairW (a • w) zeta = a * pairW w zeta := by
  simp [pairW]
  ring

/-- Exterior evaluation follows from ordinary vector/covector evaluation.
No inverse/cofactor identity on a six-by-six matrix is required.-/
theorem pairW_wedgeAct_dualWedge (g h : Mat4 K) (hhg : h * g = 1)
    (w : W K) (phi psi : Udual K) :
    pairW (wedgeAct g w) (dualWedge2 (covAct h phi) (covAct h psi)) =
      pairW w (dualWedge2 phi psi) := by
  apply wedge_induction (P := fun w =>
    pairW (wedgeAct g w) (dualWedge2 (covAct h phi) (covAct h psi)) =
      pairW w (dualWedge2 phi psi))
  · intro x y hx hy
    simp only [wedgeAct_add, pairW_add_left, hx, hy]
  · intro a x hx
    simp only [wedgeAct_smul, pairW_smul_left, hx]
  · intro p q
    rw [wedgeAct_wedge2, wedge_dual_pairing, wedge_dual_pairing,
      evalU_covAct_vecAct g h hhg, evalU_covAct_vecAct g h hhg,
      evalU_covAct_vecAct g h hhg, evalU_covAct_vecAct g h hhg]

end AlbertLean.Generic.ExteriorAction
