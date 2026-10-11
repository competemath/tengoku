import Tengoku.OpenaiMath.OAI.Probability.EntangledGames.SpectralEntropy

namespace OAI

universe u_n u_α u_m u_p u_J u_R

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci rectContinuousENorm
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma integral_matrix_apply {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] {f : α → Matrix m p ℂ}
    (hf : Integrable f μ) (i : m) (j : p) :
    (∫ s, f s ∂μ) i j = ∫ s, f s i j ∂μ := by
  erw [eval_integral (fun i => hf.eval i), eval_integral (fun j => (hf.eval i).eval j)]

variable {J : Type u_J} [Fintype J] [DecidableEq J]

def commonKernel (A : J → Matrix n n ℂ) (s : ℝ) : Matrix n (J × n) ℂ :=
  fun r v => purificationKernel (A v.1) s r v.2

def commonGram (A : J → Matrix n n ℂ) : Matrix (J × n) (J × n) ℂ :=
  ∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s

lemma commonGram_posSemidef (A : J → Matrix n n ℂ) : (commonGram A).PosSemidef := by
  apply integral_matrix_nonneg
  exact Filter.Eventually.of_forall fun s => posSemidef_conjTranspose_mul_self (commonKernel A s)

def finitePurification (A : J → Matrix n n ℂ) (j : J) : Matrix (J × n) n ℂ :=
  (CFC.sqrt (commonGram A)).submatrix id (fun i => (j, i))

end ThresholdParallelRepetition.Resolvent

end

end OAI
