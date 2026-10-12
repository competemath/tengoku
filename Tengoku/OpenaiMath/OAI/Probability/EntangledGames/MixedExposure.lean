import Tengoku.OpenaiMath.OAI.Probability.EntangledGames.EffectExposure

namespace OAI

universe u_X u_Y u_I u_m u_n u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} {J : Type u_J} {K : Type u_K} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype K] [DecidableEq K] [Nonempty K]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [Fintype n]

lemma mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.lefts x₀ l F z) (μ.rights y₀ r H z)) =
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (H z)) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (μ.rights y₀ r H z)) := by
      apply pi_lefts_pairing μ x₀ l F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro i hi z x
      simp only [hθL i hi z, rights_ignoresLeft_notMem μ y₀ r (hlr i hi) (hH i hi) z]
    _ = _ := by
      apply pi_rights_pairing μ y₀ r H (fun z => θ z • probRight C (F z))
      intro i hi z y
      simp only [hθR i hi z, hF i hi z]

lemma fixed_mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i)
    (i : I) (hiL : i ∉ l) (hiR : i ∉ r) (q : X×Y) :
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) * prob C
      (μ.lefts x₀ l F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
      prob C (F (Function.update z i q)) (H (Function.update z i q))) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
        prob C (F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) := by
      apply pi_fixed_lefts_pairing μ x₀ l hiL q F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro j hj z x
      simp only [hθL j hj z, rights_ignoresLeft_notMem μ y₀ r (hlr j hj) (hH j hj) z]
    _ = _ := by
      apply pi_fixed_rights_pairing μ y₀ r hiR q H (fun z => θ z • probRight C (F z))
      intro j hj z y
      simp only [hθR j hj z, hF j hj z]
end ThresholdParallelRepetition.MixedExposure

end

end OAI
