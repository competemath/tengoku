import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.NestedReciprocalField
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms detN_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms det_rationalM_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Generic nonvanishing of the normalized moment determinant

The determinant is cleared in the polynomial ring before specialization.
No evaluation of a fraction-field element is used.
-/

noncomputable section

namespace AlbertLean.Generic.GenericDeterminantOpen

open Matrix Polynomial
open AlbertLean.Generic.NestedReciprocalField

universe u
variable (k : Type u) [Field k] [CharZero k]

abbrev R := BasePolynomial k
abbrev B := GenericBase k

def x (v : BaseVar) : R k := MvPolynomial.X v
def diagX (i : Fin 4) : R k := x k (Sum.inl i)
def gaugeX (i : Fin 3) : R k := x k (Sum.inr (Sum.inl i))
def offX (ij : OffDiagonal) : R k := x k (Sum.inr (Sum.inr ij))

def dA0 : R k := diagX k 0
def dA1 : R k := diagX k 1
def dB0 : R k := diagX k 2
def dB1 : R k := diagX k 3
def a : R k := gaugeX k 0
def b : R k := gaugeX k 1
def c : R k := gaugeX k 2
def dA2 : R k := -dA0 k - dA1 k
def dB2 : R k := -dB0 k - dB1 k
def PA : R k := dA1 k - dA2 k
def PB : R k := dB1 k - dB2 k

def off (i j : Fin 4) : R k :=
  if h : i = j then 0 else offX k ⟨(i,j), h⟩

def SA : R k := dA0 k*dA1 k + dA0 k*dA2 k + dA1 k*dA2 k - a k + 1
def SB : R k := dB0 k*dB1 k + dB0 k*dB2 k + dB1 k*dB2 k - b k*c k + 1
def TA : R k := dA0 k*dA1 k*dA2 k - dA0 k*a k + off k 0 2 + a k*off k 2 0
def TB : R k := dB0 k*dB1 k*dB2 k - dB0 k*(b k*c k) +
  b k*off k 1 3 + c k*off k 3 1
def nA0 : R k := TA k - dA2 k*SA k
def nA2 : R k := PA k*SA k - nA0 k
def nB1 : R k := TB k - dB2 k*SB k
def nB3 : R k := PB k*SB k - nB1 k

/-- Row-cleared moment matrix `diag(PA,PB,PA,PB) M`.-/
def N : Matrix (Fin 4) (Fin 4) (R k) := fun i j =>
  if h : i = j then ![nA0 k, nB1 k, nA2 k, nB3 k] i
  else ![PA k, PB k, PA k, PB k] i * offX k ⟨(i,j),h⟩

def witnessValue (v : BaseVar) : k := match v with
  | Sum.inl i => ![0,1,0,1] i
  | Sum.inr (Sum.inl i) => ![1,1,2] i
  | Sum.inr (Sum.inr _) => 0

def witnessEval : R k →+* k := MvPolynomial.eval₂Hom (RingHom.id k) (witnessValue k)

/--
@isnad1 id=eq.0h1v.s8.878d2560b504 from=translated src=- shape=a9bacb44 vocab=48f4845b
-/
theorem witnessEval_N : (N k).map (witnessEval k) =
    Matrix.diagonal ![-1, -2, -1, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, nA0, nA2, nB1, nB3, TA, TB, SA, SB, PA, PB, dA2, dB2,
      dA0, dA1, dB0, dB1, a, b, c, off, offX, diagX, gaugeX, x,
      witnessEval, witnessValue] <;> norm_num

/--
@isnad1 id=eq.0h1v.s7.e51ab05229bf from=translated src=- shape=c9036ea3 vocab=5da2630b
-/
theorem witnessEval_detN : witnessEval k (Matrix.det (N k)) = 4 := by
  rw [RingHom.map_det]
  change Matrix.det ((N k).map (witnessEval k)) = 4
  rw [witnessEval_N]
  norm_num [Matrix.det_diagonal, Fin.prod_univ_succ]

/--
@isnad1 id=ne.0h1v.s6.6523c1a7e7bc from=translated src=- shape=6f5eed03 vocab=a3fd3741
-/
theorem detN_ne_zero : Matrix.det (N k) ≠ 0 := by
  intro h
  have := congrArg (witnessEval k) h
  rw [witnessEval_detN] at this
  norm_num at this

def ι : R k →+* B k := algebraMap (R k) (B k)

/--
@isnad1 id=injectiv.0h1v.s8.8c2de794b9e0 from=translated src=- shape=e937283c vocab=8246f9a4
-/
theorem iota_injective : Function.Injective (ι k) :=
  IsFractionRing.injective (R k) (B k)

private theorem iota_ne_zero {p : R k} (hp : p ≠ 0) : ι k p ≠ 0 := by
  intro h
  apply hp
  apply iota_injective k
  simpa only [map_zero] using h

/--
@isnad1 id=ne.0h1v.s9.f76fc03b92fc from=translated src=- shape=85f2aa27 vocab=605a6cb7
-/
theorem mapped_detN_ne_zero : ι k (Matrix.det (N k)) ≠ 0 :=
  iota_ne_zero k (detN_ne_zero k)

def rowPivot (i : Fin 4) : B k :=
  algebraMap (R k) (B k) (![PA k, PB k, PA k, PB k] i)

def rationalM : Matrix (Fin 4) (Fin 4) (B k) := fun i j =>
  if h : i = j then
    ![ι k (nA0 k) / ι k (PA k), ι k (nB1 k) / ι k (PB k),
      ι k (nA2 k) / ι k (PA k), ι k (nB3 k) / ι k (PB k)] i
  else ι k (offX k ⟨(i,j),h⟩)

def rowScale : Matrix (Fin 4) (Fin 4) (B k) :=
  Matrix.diagonal (rowPivot k)

/--
@isnad1 id=ne.0h1v.s8.3ccf57c79d7b from=translated src=- shape=fcfb5405 vocab=a4214710
-/
theorem PA_ne_zero : ι k (PA k) ≠ 0 := by
  apply iota_ne_zero k
  intro h
  have hh := congrArg (witnessEval k) h
  norm_num [PA, dA2, dA1, dA0, diagX, x, witnessEval, witnessValue] at hh

/--
@isnad1 id=ne.0h1v.s8.f216cffec4d6 from=translated src=- shape=fcfb5405 vocab=f020276c
-/
theorem PB_ne_zero : ι k (PB k) ≠ 0 := by
  apply iota_ne_zero k
  intro h
  have hh := congrArg (witnessEval k) h
  simp [PB, dB2, dB1, dB0, diagX, x, witnessEval, witnessValue] at hh

/--
@isnad1 id=eq.0h1v.s9.084fb7af28fb from=translated src=- shape=6c482d4f vocab=8a0c5d6a
-/
theorem rowScale_mul_rationalM : rowScale k * rationalM k = (N k).map (ι k) := by
  have ha := PA_ne_zero k
  have hb := PB_ne_zero k
  simp only [ι] at ha hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowScale, rowPivot, rationalM, N, ι, Matrix.mul_apply,
      Fin.sum_univ_succ, mul_div_cancel₀ _ ha, mul_div_cancel₀ _ hb]

/-- The generic rational moment determinant is nonzero, obtained from the
nonzero cleared polynomial numerator.
@isnad1 id=ne.0h1v.s8.76faa9620cfb from=translated src=- shape=6f5eed03 vocab=5fe879e5
-/
theorem det_rationalM_ne_zero : Matrix.det (rationalM k) ≠ 0 := by
  intro h
  apply mapped_detN_ne_zero k
  rw [RingHom.map_det]
  change Matrix.det ((N k).map (ι k)) = 0
  rw [← rowScale_mul_rationalM, Matrix.det_mul, h, mul_zero]

end AlbertLean.Generic.GenericDeterminantOpen
