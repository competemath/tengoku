import Tengoku.OpenaiMath.OAI.Probability.EntangledGames.FreshStates

namespace OAI

universe u_X u_Y u_I u_R u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

structure EventSystem where
  μ : Law (X×Y)
  x₀ : X
  y₀ : Y
  l : List I
  nodup : l.Nodup
  C : Matrix m n ℂ
  hC : hsSq C = 1
  F : R → Profile I X Y → Matrix m m ℂ
  H : R → Profile I X Y → Matrix n n ℂ
  hF : ∀ r z, (F r z).PosSemidef
  hF1 : ∀ r z, F r z ≤ 1
  hH : ∀ r z, (H r z).PosSemidef
  hH1 : ∀ r z, H r z ≤ 1
  localF : ∀ r i, IgnoresRight (F r) i
  localH : ∀ r i, IgnoresLeft (H r) i
  θ : R → Profile I X Y → ℝ
  hθ : ∀ r z, 0 ≤ θ r z
  hθ1 : ∀ r z, θ r z ≤ 1
  localθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i
  localθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i
  event_le_one : ∀ z, (∑ r, θ r z*prob C (F r z) (H r z)) ≤ 1
  p : ℝ
  hp : 0 < p
  mass : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p

variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
namespace EventSystem
variable (S : EventSystem X Y I R m n)
abbrev J := ExposureIndex (R := R) (X := X) (Y := Y) S.l
abbrev f := chainLeft S.μ S.x₀ S.l S.F
abbrev h := chainRight S.μ S.y₀ S.l S.H
abbrev A := chainLeftFamily S.μ S.x₀ S.l S.F
abbrev B := chainRightFamily S.μ S.y₀ S.l S.H

def U (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×m) m ℂ := commonMap S.A (S.f j r z)
def V (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×n) n ℂ := commonMap S.B (S.h j r z)

omit [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma f_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.f j r z).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (S.hF r) z
omit [DecidableEq X] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma h_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.h j r z).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (S.hH r) z

def D (j : Fin S.l.length) : X×Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V j)
def rawA (j : Fin S.l.length) : X → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun x => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) (x,S.y₀)
def rawB (j : Fin S.l.length) : Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun y => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) (S.x₀,y)

lemma rawA_eq (j : Fin S.l.length) (q : X×Y) : S.rawA j q.1 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) q := by
  apply stateAt_right_local
  · intro r z y
    exact congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  · intro r z y
    apply congrArg (commonMap S.B)
    rw [h, chainRight_step S.μ S.y₀ S.l S.H j j.isLt r]
    exact right_ignoresRight S.μ S.y₀ _ _ z y
lemma rawB_eq (j : Fin S.l.length) (q : X×Y) : S.rawB j q.2 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) q := by
  apply stateAt_left_local
  · intro r z x
    apply congrArg (commonMap S.A)
    rw [f, chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r]
    exact left_ignoresLeft S.μ S.x₀ _ _ z x
  · intro r z x
    exact congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)

def density : Profile I X Y → ℝ := eventDensity S.θ S.p S.C S.F S.H
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_nonneg : ∀ z, 0 ≤ S.density z := eventDensity_nonneg S.θ S.hθ S.hp S.C S.F S.H S.hF S.hH
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_total : (pi (fun _ : I => S.μ)).avg S.density = 1 :=
  eventDensity_total S.μ S.θ S.hp S.C S.F S.H S.mass
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_le (z : Profile I X Y) : S.density z ≤ 1/S.p := by
  exact (mul_le_mul_of_nonneg_left (S.event_le_one z) (div_nonneg zero_le_one S.hp.le)).trans_eq (mul_one _)

end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI
