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

/--
@isnad1 id=eq.0h2v.s9.d8fbabf1098d from=translated src=- shape=31dbc925 vocab=f4844e9e
-/
theorem wedge_decomposition (w : W K) :
    w = w .i12 • wedge2 (uBasis 0) (uBasis 1) +
      w .i13 • wedge2 (uBasis 0) (uBasis 2) +
      w .i14 • wedge2 (uBasis 0) (uBasis 3) +
      w .i23 • wedge2 (uBasis 1) (uBasis 2) +
      w .i24 • wedge2 (uBasis 1) (uBasis 3) +
      w .i34 • wedge2 (uBasis 2) (uBasis 3) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis]

/-- Decomposable wedges span the actual six-coordinate carrier.
@isnad1 id=var.0h6v.s6.7ae947ad62a9 from=translated src=- shape=d413db5f vocab=bce0bfbf
-/
theorem wedge_induction {P : W K → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : K) x, P x → P (a • x))
    (hwedge : ∀ p q, P (wedge2 p q)) (w : W K) : P w := by
  rw [wedge_decomposition w]
  repeat' first | apply hadd | apply hsmul | apply hwedge

/--
@isnad1 id=eq.0h2v.s5.048aa08e4f0b from=translated src=- shape=c0d046c8 vocab=1465ebff
-/
@[simp] theorem wedgeAct_zero (g : Mat4 K) : wedgeAct g 0 = 0 := by
  simp [wedgeAct]

/--
@isnad1 id=eq.0h4v.s6.15798d9420a9 from=translated src=- shape=30277119 vocab=cf283a84
-/
theorem wedgeAct_add (g : Mat4 K) (w v : W K) :
    wedgeAct g (w + v) = wedgeAct g w + wedgeAct g v := by
  funext i
  simp [wedgeAct, add_smul]
  ring

/--
@isnad1 id=eq.0h4v.s6.fb4a3e72cb08 from=translated src=- shape=59de849e vocab=145bb74b
-/
theorem wedgeAct_smul (g : Mat4 K) (a : K) (w : W K) :
    wedgeAct g (a • w) = a • wedgeAct g w := by
  funext i
  simp [wedgeAct]
  ring

def wedgeActLinear (g : Mat4 K) : W K →ₗ[K] W K where
  toFun := wedgeAct g
  map_add' := wedgeAct_add g
  map_smul' := wedgeAct_smul g

/--
@isnad1 id=eq.0h4v.s5.ac438c30d730 from=translated src=- shape=7fc84efa vocab=bde6ad0f
-/
theorem wedgeAct_wedge2 (g : Mat4 K) (p q : U K) :
    wedgeAct g (wedge2 p q) = wedge2 (vecAct g p) (vecAct g q) := by
  funext i
  fin_cases i <;>
    simp [wedgeAct, wedge2, vecAct, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, uBasis] <;> ring

/--
@isnad1 id=eq.0h2v.s5.43629ba9d063 from=translated src=- shape=ac2eeb16 vocab=4767aa0b
-/
@[simp] theorem vecAct_one (p : U K) : vecAct (1 : Mat4 K) p = p := by
  simp [vecAct]

/--
@isnad1 id=eq.0h4v.s6.dd327af4ad37 from=translated src=- shape=27bb00d2 vocab=2274f904
-/
theorem vecAct_mul (g h : Mat4 K) (p : U K) :
    vecAct g (vecAct h p) = vecAct (g * h) p := by
  exact Matrix.mulVec_mulVec p g h

/--
@isnad1 id=eq.0h4v.s6.486f7d973274 from=translated src=- shape=27bb00d2 vocab=eef57968
-/
theorem wedgeAct_mul (g h : Mat4 K) (w : W K) :
    wedgeAct g (wedgeAct h w) = wedgeAct (g * h) w := by
  conv_lhs => arg 2; unfold wedgeAct
  simp only [wedgeAct_add, wedgeAct_smul, wedgeAct_wedge2, vecAct_mul]
  rfl

/--
@isnad1 id=eq.0h2v.s5.58e6a18e5242 from=translated src=- shape=ac2eeb16 vocab=13092583
-/
@[simp] theorem wedgeAct_one (w : W K) : wedgeAct (1 : Mat4 K) w = w := by
  simpa only [wedgeAct, vecAct_one] using (wedge_decomposition w).symm

/--
@isnad1 id=eq.1h4v.s7.94a22ce8a057 from=translated src=- shape=2b8aff1e vocab=eef57968
-/
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

/--
@isnad1 id=eq.0h5v.s5.e047faa37272 from=translated src=- shape=69eb1707 vocab=dd562c74
-/
theorem BW_wedge2_eq_det (p q r s : U K) :
    BW (wedge2 p q) (wedge2 r s) = Matrix.det (fourColumns p q r s) := by
  rw [Matrix.det_succ_row_zero]
  simp [fourColumns, Matrix.transpose, Matrix.det_fin_three, Matrix.submatrix,
    Fin.sum_univ_succ, Fin.succAbove, BW, wedge2] <;> ring

/--
@isnad1 id=eq.0h6v.s6.e24ae0f64f93 from=translated src=- shape=4cae6301 vocab=24632813
-/
theorem fourColumns_vecAct (g : Mat4 K) (p q r s : U K) :
    fourColumns (vecAct g p) (vecAct g q) (vecAct g r) (vecAct g s) =
      g * fourColumns p q r s := by
  ext i j
  fin_cases j <;>
    simp [fourColumns, Matrix.transpose, vecAct, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h6v.s6.ce75f470ca7d from=translated src=- shape=518eb927 vocab=1a5e0b5a
-/
theorem BW_wedgeAct_wedges (g : Mat4 K) (p q r s : U K) :
    BW (wedgeAct g (wedge2 p q)) (wedgeAct g (wedge2 r s)) =
      Matrix.det g * BW (wedge2 p q) (wedge2 r s) := by
  rw [wedgeAct_wedge2, wedgeAct_wedge2, BW_wedge2_eq_det,
    fourColumns_vecAct, Matrix.det_mul, BW_wedge2_eq_det]

/-- Exterior square is a similitude with multiplier `det g`, not its square.
@isnad1 id=eq.0h4v.s6.5812c5b5bb79 from=translated src=- shape=3ab19495 vocab=277ace8c
-/
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

/--
@isnad1 id=eq.1h4v.s6.8feb498f6f8f from=translated src=- shape=2a72d0bb vocab=e420415e
-/
theorem BW_wedgeAct_of_det_one (g : Mat4 K) (hg : Matrix.det g = 1)
    (w v : W K) : BW (wedgeAct g w) (wedgeAct g v) = BW w v := by
  rw [BW_wedgeAct, hg, one_mul]

/--
@isnad1 id=eq.1h5v.s7.b27b64f71c65 from=translated src=- shape=13e276a9 vocab=ec154369
-/
theorem evalU_covAct_vecAct (g h : Mat4 K) (hhg : h * g = 1)
    (phi : Udual K) (p : U K) : evalU (covAct h phi) (vecAct g p) = evalU phi p := by
  have eval_dot (a : Udual K) (b : U K) : evalU a b = dotProduct a b := by
    simp [evalU, dotProduct, Fin.sum_univ_succ] <;> ring
  rw [eval_dot, eval_dot]
  change dotProduct (Matrix.vecMul phi h) (g.mulVec p) = dotProduct phi p
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hhg, Matrix.vecMul_one]

/--
@isnad1 id=eq.0h4v.s6.39672e7a86ed from=translated src=- shape=6d223717 vocab=38328072
-/
theorem pairW_add_left (w v : W K) (zeta : Wdual K) :
    pairW (w + v) zeta = pairW w zeta + pairW v zeta := by
  simp [pairW]
  ring

/--
@isnad1 id=eq.0h4v.s6.751d728156d1 from=translated src=- shape=9f7f9aab vocab=28e62fe9
-/
theorem pairW_smul_left (a : K) (w : W K) (zeta : Wdual K) :
    pairW (a • w) zeta = a * pairW w zeta := by
  simp [pairW]
  ring

/-- Exterior evaluation follows from ordinary vector/covector evaluation.
No inverse/cofactor identity on a six-by-six matrix is required.
@isnad1 id=eq.1h6v.s7.4fe72e0d0f28 from=translated src=- shape=f812a5dc vocab=5969c387
-/
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
