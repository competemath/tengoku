import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Localization
import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Physical
import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Measurement

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma eventually_exp_neg_power_lt {s ε : ℝ} (hs : 0<s) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-(N:ℝ)^s)<ε := by
  filter_upwards [eventually_power_le hs (-Real.log ε+1)] with N hN
  rw [Real.rpow_zero,mul_one] at hN
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr (by linarith only [hN])

lemma polynomial_qubit_threshold {n N : ℕ} {c t : ℝ} (hn : 1≤n)
    (ht : 0≤t) (hct : c*t≤1) (hN : (N:ℝ)≤(n:ℝ)^c) : (N:ℝ)^t≤(n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  calc
    (N:ℝ)^t ≤ ((n:ℝ)^c)^t := Real.rpow_le_rpow (Nat.cast_nonneg N) hN ht
    _ = (n:ℝ)^(c*t) := (Real.rpow_mul (Nat.cast_nonneg n) c t).symm
    _ ≤ (n:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hn1 hct
    _ = (n:ℝ) := Real.rpow_one _

lemma hadamard_high_entry_bound {n N : ℕ} (hnN : n≤N) (W : Operator N)
    (out : Fin N) (x : Word n) {r : ℝ} (hr : r≤(n:ℝ)) :
    ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤
    ‖(computationalCount (inputWord x)).high r*(localMatrix (inputHadamard n N)*star W)*
      (outputZeroCount out).zero*star (localMatrix (inputHadamard n N)*star W)*
      (computationalCount (inputWord x)).zero‖ := by
  have hcard : r≤((inputSet n N).card:ℝ) := by simpa only [inputSet_card hnN] using hr
  have hh := high_entry_bound
    (localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N)) (inputWord x) (inputSet n N) hcard
  simpa only [star_mul,star_star,inputHadamard_star,mul_assoc] using hh

end QAC

end

end OAI
