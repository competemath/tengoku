import Tengoku.OpenaiMath.OAI.InformationTheory.AmplitudeDamping.Holevo

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

def codeEnsemble {n : ℕ} (C : Code n) : Ensemble n where
  size := C.messages
  weight := fun _ ↦ (C.messages:ℝ)⁻¹
  weight_nonneg := fun _ ↦ by positivity
  weight_sum := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast C.messages_pos.ne')
  signal := C.encoding
  signal_state := C.encoding_state

theorem code_success_dim_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) :
    (∑ m, (C.decoding m*channel γ ν n (C.encoding m)).trace.re) ≤ (2:ℝ)^n := by
  calc
    _ ≤ ∑ m, (C.decoding m).trace.re := Finset.sum_le_sum (fun m _ ↦
      state_measurement_prob_le_trace (channel_state γ ν hγ hν n (C.encoding_state m)) (C.decoding_pos m))
    _ = _ := by
      rw [← Complex.re_sum,← Matrix.trace_sum,C.decoding_sum,Matrix.trace_one]
      rw [basis_card,Nat.cast_pow,Nat.cast_ofNat]
      rw [← Complex.ofReal_ofNat,← Complex.ofReal_pow,Complex.ofReal_re]

theorem code_messages_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n)
    (he : averageError γ ν C ≤ 1/2) : (C.messages:ℝ) ≤ 2*(2:ℝ)^n := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hs := code_success_dim_bound γ ν hγ hν C
  dsimp [averageError] at he
  have ht : (1/2:ℝ)*(C.messages:ℝ) ≤ ∑ m, (C.decoding m*channel γ ν n (C.encoding m)).trace.re := by
    apply (le_div_iff₀ hM).mp
    linarith
  linarith

theorem code_log_dimension_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (hn : 0 < n) (C : Code n)
    (he : averageError γ ν C ≤ 1/2) :
    Real.log (2^n*C.messages:ℕ) ≤ 3*(n:ℝ)*Real.log 2 := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hpow : 0 < (2:ℝ)^n := by positivity
  have hb := code_messages_bound γ ν hγ hν C he
  have hl := Real.log_le_log hM hb
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hpow.ne',Real.log_pow] at hl
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.log_mul hpow.ne' hM.ne',Real.log_pow]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

end GAD

end

end OAI
