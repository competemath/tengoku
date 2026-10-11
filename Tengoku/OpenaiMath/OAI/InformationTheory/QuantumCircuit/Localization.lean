import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Backward
import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Asymptotics
import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.ScaleInduction
import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.DepthZero

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- The uniform estimate, with the eventual quantifier outside all circuit data. -/
def UniformLocalization (d : ℕ) (s t : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
    ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^s))

lemma uniform_zero {s t : ℝ} (hst : s < t) : UniformLocalization 0 s t := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_power_le hst (2/Real.log 2)] with N hN
  intro U hU M D
  obtain ⟨L,rfl⟩ := hU
  have hb := M.depth_zero_bound (D.rotate L) ((N:ℝ)^t)
  rw [D.rotate_zero L] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have h := (div_le_iff₀ hlog).mp (show 2*(N:ℝ)^s/Real.log 2 ≤ (N:ℝ)^t by
    simpa only [div_mul_eq_mul_div] using hN)
  nlinarith only [h]

lemma uniform_large (d : ℕ) {s t : ℝ} (ht : 1 < t) : UniformLocalization d s t := by
  filter_upwards [eventually_power_le ht 2,Filter.eventually_ge_atTop 1] with N hN hN1
  intro U _ M D
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlimit : (N:ℝ) < (N:ℝ)^t := by rw [Real.rpow_one] at hN; linarith only [hN,hNpos]
  rw [M.high_eq_zero hlimit,zero_mul,zero_mul,norm_zero]
  exact (Real.exp_pos _).le

lemma uniform_low_propagation {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {a s t : ℝ} (ha : 0 ≤ a) (_hs : 0 ≤ s) (hat : a < t) (hst : s < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
      ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.low ((N:ℝ)^a)‖ ≤ Real.exp (-((N:ℝ)^s)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hat hst)
  have hav : a < v := (le_max_left _ _).trans_lt hv
  have hsv : s < v := (le_max_right _ _).trans_lt hv
  obtain ⟨q,hvq,hqt⟩ := exists_between hvt
  filter_upwards [ih v q (ha.trans hav.le) hvq,
    eventually_two_powers_le hqt hat,eventually_pattern_cost ha hav hsv,
    Filter.eventually_ge_atTop 1] with N hN hp hc hN1
  intro U hU M D
  exact (M.low_propagation_bound (conjugate U D.zero) hN1 (Real.exp_pos _).le hp
    (fun K => hN U hU K D)).trans hc

lemma uniform_small_support {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {u w t : ℝ} (hu : 0 ≤ u) (_hw : 0 ≤ w) (hut : u < t) (hwt : w < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit (d+1) U → ∀ M A : Count N,
      (A.support.card:ℝ) ≤ (N:ℝ)^u →
      ‖M.high ((N:ℝ)^t)*conjugate U A.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^w)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hut hwt)
  have huv : u < v := (le_max_left _ _).trans_lt hv
  have hwv : w < v := (le_max_right _ _).trans_lt hv
  have hv0 : 0 < v := lt_of_le_of_lt hu huv
  obtain ⟨r₁,hvr₁,hr₁t⟩ := exists_between hvt
  obtain ⟨r₂,hr₁r₂,hr₂t⟩ := exists_between hr₁t
  filter_upwards [ih v r₁ hv0.le hvr₁,
    uniform_low_propagation ih (hv0.le.trans hvr₁.le) hv0.le hr₁r₂ (hvr₁.trans hr₁r₂),
    uniform_low_propagation ih (hv0.le.trans (hvr₁.trans hr₁r₂).le) hv0.le hr₂t hvt,
    eventually_exp_power_gap hwv huv hv0 3 1 1 (Real.log 9) (by norm_num) zero_lt_one] with N h₁ h₂ h₃ hc
  intro U hU M A hA
  obtain ⟨V,R,L,hV,rfl⟩ := hU
  have hb := small_support_layer_bound V hV.mem_unitary R L M A (Real.exp_pos _).le
    (fun D => h₁ V hV M D) (fun D => h₂ V hV M D) (fun D => h₃ V hV M D)
  have hcost : (9:ℝ)^A.support.card ≤ Real.exp (Real.log 9*(N:ℝ)^u) := by
    calc
      _ = Real.exp (Real.log 9*(A.support.card:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA (Real.log_nonneg (by norm_num)))
  apply hb.trans
  calc
    _ ≤ Real.exp (Real.log 9*(N:ℝ)^u)*(3*Real.exp (-((N:ℝ)^v))) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = 3*Real.exp (Real.log 9*(N:ℝ)^u-(N:ℝ)^v) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ _ := by simpa only [one_mul] using hc

end QAC

end

end OAI
