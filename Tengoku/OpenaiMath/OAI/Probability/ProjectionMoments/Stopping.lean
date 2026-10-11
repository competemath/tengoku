import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.AllRadii

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

instance taggedMeasurableSingletonClass : MeasurableSingletonClass (TaggedState M T) :=
  ⟨fun _ => trivial⟩

lemma card_taggedState (M T : ℕ) : Fintype.card (TaggedState M T) = (T+2)*2^M := by
  simp only [TaggedState, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, State]
  ring

def decodeTagged : TaggedState M T → RunStatus M
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.val,j)

def taggedStep (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (t : ℕ) : TaggedState M T → (Vector d × ℝ) → TaggedState M T
  | .inr done, _ => .inr done
  | .inl j, obs =>
    if ht : t ≤ T then
      let a := τ t j obs
      if a.1 then .inr (⟨t,by omega⟩,a.2) else .inl a.2
    else .inl j

lemma measurable_taggedStep {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (t : ℕ) (j : TaggedState M T) :
    Measurable (taggedStep (T := T) τ t j) := by
  classical
  cases j with
  | inr done => exact measurable_const
  | inl j =>
    unfold taggedStep
    split_ifs with ht
    · exact (measurable_of_finite (fun a : Bool × State M =>
        if a.1 then Sum.inr ((⟨t,by omega⟩ : Fin (T+1)),a.2) else Sum.inl a.2)).comp (hτ t j)
    · exact measurable_const

def taggedOutput (L : Learner d M T Ω) (ω : Ω) : TaggedState M T → UnitSphere d
  | .inl j => L.output T ω j
  | .inr (t,j) => L.output t ω j

lemma decode_taggedStart (a : Bool × State M) :
    decodeTagged (taggedStart (T := T) a) = if a.1 then .inr (0,a.2) else .inl a.2 := by
  simp only [taggedStart]; split_ifs <;> rfl

lemma run_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.run s ω x n = decodeTagged (streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j))
      0 n (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE hn i)),fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫),streamRoute_snoc]
    rw [run,ih (by omega)]
    generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 n
      (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE (by omega : n ≤ T) i)),fun i => ⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫) = j
    cases j with
    | inr done => rfl
    | inl j =>
      simp only [decodeTagged, taggedStep, Nat.zero_add,dite_eq_left (by omega : n < T),
        dite_eq_left (by omega : n+1 ≤ T),real_inner_comm]
      split_ifs <;> rfl

lemma estimate_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    L.estimate s ω x = L.taggedOutput ω (streamRoute
      (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T (taggedStart (L.initialChoice ω))
      (x,fun i => ⟪s.val,x i⟫)) := by
  unfold estimate terminal
  rw [L.run_eq_taggedRoute s ω x le_rfl]
  have hi : (fun i : Fin T => x (Fin.castLE le_rfl i)) = x := by funext i; exact congrArg x (Fin.ext rfl)
  have hb : (fun i : Fin T => ⟪s.val,x (Fin.castLE le_rfl i)⟫) = (fun i => ⟪s.val,x i⟫) := by funext i; rfl
  rw [hi,hb]
  generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T
    (taggedStart (L.initialChoice ω)) (x,fun i => ⟪s.val,x i⟫) = j
  cases j with
  | inl j => rfl
  | inr done => rfl

lemma taggedStep_congr {τ τ' : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ)
    (h : ∀ a, τ t a obs = τ' t a obs) :
    taggedStep τ t j obs = taggedStep τ' t j obs := by
  cases j with
  | inr done => rfl
  | inl j => simp only [taggedStep,h]

end Learner
end NoiselessRegression

end

end OAI
