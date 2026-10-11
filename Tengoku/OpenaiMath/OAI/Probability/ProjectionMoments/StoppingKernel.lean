import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Realization

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end

namespace Learner

section
variable {d M : ℕ}

def haltShift {k : ℕ} : TaggedState M k → TaggedState M (k+1)
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.succ,j)

def haltRoute (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M) (n : ℕ) :
    (k : ℕ) → State M → ((Fin k → Vector d) × (Fin k → ℝ)) → TaggedState M k
  | 0, j, _ => .inl j
  | k+1, j, X =>
    let a := τ (n+1) j (X.1 0,X.2 0)
    if a.1 then .inr (⟨1,by omega⟩,a.2)
    else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))

lemma measurable_haltRoute {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (n k : ℕ) (j : State M) :
    Measurable (haltRoute τ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    let h : (Bool × State M) → ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) → TaggedState M (k+1) :=
      fun a X => if a.1 then .inr (⟨1,by omega⟩,a.2)
        else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))
    change Measurable (fun X => h (τ (n+1) j (X.1 0,X.2 0)) X)
    apply measurable_select (J := Bool × State M) _ ((hτ (n+1) j).comp (by fun_prop))
    intro a
    dsimp [h]
    split_ifs
    · exact measurable_const
    · exact (measurable_of_finite haltShift).comp ((ih (n+1) a.2).comp (by
        change Measurable (fun X : ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) =>
          ((fun i : Fin k => X.1 i.succ),(fun i : Fin k => X.2 i.succ)))
        fun_prop))

def haltChild (w : ℕ → State M → Vector d → ℝ≥0∞)
    (v : State M → Vector d → ℝ≥0∞) (n : ℕ) {k : ℕ} : TaggedState M k → Vector d → ℝ≥0∞
  | .inl j => v j
  | .inr (t,j) => w (n+t) j

def stoppedContinuation (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : ℕ → State M → Vector d → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, let a := τ (n+1) j (x,⟪s,x⟫)
      if a.1 then w (n+1) a.2 s else stoppedContinuation τ w (n+1) k a.2 s ∂stdGaussian (Vector d)

lemma measurable_stoppedContinuation {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : State M) :
    Measurable (stoppedContinuation τ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    change Measurable (fun z : Vector d × Vector d =>
      if (τ (n+1) j (z.1,⟪z.2,z.1⟫)).1 then w (n+1) (τ (n+1) j (z.1,⟪z.2,z.1⟫)).2 z.2
      else stoppedContinuation τ w (n+1) k (τ (n+1) j (z.1,⟪z.2,z.1⟫)).2 z.2)
    apply measurable_select (J := Bool × State M) (h := fun a (z : Vector d × Vector d) =>
      if a.1 then w (n+1) a.2 z.2 else stoppedContinuation τ w (n+1) k a.2 z.2) _
      ((hτ (n+1) j).comp (by fun_prop))
    intro a
    split_ifs
    · exact (hw (n+1) a.2).comp measurable_snd
    · exact (ih (n+1) a.2).comp measurable_snd

lemma stoppedContinuation_le_one
    {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : State M) (s : Vector d) :
    stoppedContinuation τ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    change (∫⁻ x, (if (τ (n+1) j (x,⟪s,x⟫)).1 then w (n+1) (τ (n+1) j (x,⟪s,x⟫)).2 s else stoppedContinuation τ w (n+1) k (τ (n+1) j (x,⟪s,x⟫)).2 s) ∂stdGaussian (Vector d)) ≤ 1
    apply (lintegral_mono (g := fun _ => (1:ℝ≥0∞)) (fun x => ?_)).trans_eq (by simp)
    split_ifs
    · exact hw _ _ _
    · exact ih _ _

lemma stoppedContinuation_unroll
    {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (n m k : ℕ) (j : State M) (s : Vector d) :
    stoppedContinuation τ w n (m+k) j s =
      blockValue (haltChild w (stoppedContinuation τ w (n+m) k) n) (haltRoute τ n m j) s := by
  induction m generalizing n j with
  | zero => simp [blockValue,haltRoute,haltChild]
  | succ m ih =>
    rw [Nat.succ_add,stoppedContinuation]
    unfold blockValue
    have hf : Measurable (fun X : Fin (m+1) → Vector d =>
        haltChild w (stoppedContinuation τ w (n+(m+1)) k) n
          (haltRoute τ n (m+1) j (X,fun i => ⟪s,X i⟫)) s) :=
      (measurable_of_finite (fun a => haltChild w (stoppedContinuation τ w (n+(m+1)) k) n a s)).comp
        ((measurable_haltRoute hτ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    have htail (X : Fin m → Vector d) : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x X : Fin (m+1) → Vector d) i⟫) = (fun i => ⟪s,X i⟫) := by funext i; rfl
    simp only [haltRoute,Fin.cons_zero,Fin.tail_cons,htail]
    split_ifs with h
    · simp [haltChild]
    · rw [ih]
      unfold blockValue
      apply lintegral_congr
      intro X
      have h1 : n+(m+1) = n+1+m := by omega
      rw [h1]
      generalize haltRoute τ (n+1) m (τ (n+1) j (x,⟪s,x⟫)).2 (X,fun i => ⟪s,X i⟫) = a
      cases a with
      | inl j => rfl
      | inr done =>
        simp only [haltShift,haltChild,Fin.val_succ]
        rw [show n+1+done.1.val = n+(done.1.val+1) by omega]

end

variable {d M T : ℕ}

def taggedWeight (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : TaggedState M T → Vector d → ℝ≥0∞
  | .inl j => w n j
  | .inr (t,j) => w t j

lemma measurable_taggedWeight {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j, Measurable (w n j)) (n : ℕ) (j : TaggedState M T) :
    Measurable (taggedWeight w n j) := by cases j <;> exact hw _ _

lemma continuation_tagged_eq {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (n k : ℕ) (hnk : n+k ≤ T) (j : TaggedState M T) (s : Vector d) :
    continuation (taggedStep τ) (taggedWeight w) n k j s =
      match j with
      | .inl a => stoppedContinuation τ w n k a s
      | .inr (t,a) => w t a s := by
  induction k generalizing n j with
  | zero => cases j <;> rfl
  | succ k ih =>
    cases j with
    | inl j =>
      simp only [continuation,stoppedContinuation]
      apply lintegral_congr
      intro x
      rw [ih (n+1) (by omega)]
      simp only [taggedStep,dite_eq_left (by omega : n+1 ≤ T)]
      split_ifs <;> rfl
    | inr done =>
      simp only [continuation,taggedStep]
      simp only [ih (n+1) (by omega),lintegral_const,measure_univ,mul_one]

variable [NeZero d]

end Learner
end NoiselessRegression

end

end OAI
