import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.MarkovProduct

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.ExpandedChain
open scoped BigOperators
open ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A : Type*} [Fintype A]

noncomputable def past (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ) (f : A → ℝ) : ℕ → A → ℝ
  | 0 => f
  | n+1 => action (μ (n+1)) (fun b a => Q n a b) (past μ Q f n)

lemma past_bounds (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (n : ℕ) :
    ∀ a, 0 ≤ past μ Q f n a ∧ past μ Q f n a ≤ 1 := by
  induction n with
  | zero => exact hf
  | succ n ih => exact action_bounds (hQ n).symm _ ih

lemma sum_fiber_mul {B : Type*} [Fintype B] (k : A → B) (w : A → ℝ) (g : B → ℝ) :
    (∑ a, w a * g (k a)) = ∑ b, (∑ a, if k a = b then w a else 0) * g b := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

/-- Conditional past means in the actual finite product law, not an assumed
Markov response. This identity includes all zero-mass states. -/
lemma weighted_terminal (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f : A → ℝ) (n : ℕ) (b : A) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      if x (Fin.last n) = b then
        MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x * f (x 0)
      else 0) = μ n b * past μ Q f n b := by
  induction n generalizing b with
  | zero =>
    let e : A ≃ (Fin 1 → A) := (Equiv.piUnique (fun _ : Fin 1 => A)).symm
    rw [← e.sum_comp]
    simp [e, MarkovProduct.weight, past, Equiv.piUnique, uniqueElim]
  | succ n ih =>
    rw [MarkovProduct.sum_history_snoc (fun _ => A)]
    simp only [Fin.snoc_last, MarkovProduct.weight_snoc]
    have hzero (x : Fin (n+1) → A) (c : A) :
        @Fin.snoc (n+1) (fun _ : Fin (n+2) => A) x c 0 = x 0 := by
      exact @Fin.snoc_castSucc (n+1) (fun _ => A) c x 0
    simp only [hzero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    let w : (Fin (n+1) → A) → ℝ := fun x =>
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x * f (x 0)
    have he : (∑ x : Fin (n+1) → A,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
      MarkovProduct.couplingKernel (fun _ => A) μ Q n (x (Fin.last n)) b * f (x 0)) =
       ∑ a, μ n a * past μ Q f n a * MarkovProduct.couplingKernel (fun _ => A) μ Q n a b := by
      trans ∑ x, w x * MarkovProduct.couplingKernel (fun _ => A) μ Q n (x (Fin.last n)) b
      · apply Finset.sum_congr rfl
        intro x _
        dsimp [w]
        ring
      · rw [sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) w
          (fun a => MarkovProduct.couplingKernel (fun _ => A) μ Q n a b)]
        apply Finset.sum_congr rfl
        intro a _
        rw [show (∑ x, if x (Fin.last n) = a then w x else 0) = μ n a * past μ Q f n a from ih a]
    rw [he]
    change _ = μ (n+1) b * action (μ (n+1)) (fun b a => Q n a b) (past μ Q f n) b
    rw [weighted_action (hQ n).symm]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_right_comm, MarkovProduct.couplingKernel_balance (fun _ => A) μ Q
      (fun n => (hQ n).nonneg) (fun n => (hQ n).row)]

/-- Separation of endpoint labels in the genuine product density is precisely
its conditional-predictor defect. The identity holds for all bounded or unbounded
real endpoint observables; bounds are needed only for the subsequent tests. -/
theorem endpoint_defect (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (n : ℕ) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
        (f (x 0) + g (x (Fin.last n)) - 2*f (x 0)*g (x (Fin.last n)))) =
      defect (μ n) g (past μ Q f n) := by
  let w : (Fin (n+1) → A) → ℝ := MarkovProduct.weight (fun _ => A) (μ 0)
    (MarkovProduct.couplingKernel (fun _ => A) μ Q) n
  have hm (b : A) : (∑ x : Fin (n+1) → A, if x (Fin.last n) = b then w x else 0) = μ n b := by
    exact (MarkovProduct.terminal_marginal (fun _ => A) (μ 0)
      (MarkovProduct.couplingKernel (fun _ => A) μ Q) n b).trans
        (MarkovProduct.coupling_forward (fun _ => A) μ Q
          (fun n => (hQ n).nonneg) (fun n => (hQ n).row) (fun n => (hQ n).col) n b)
  have hw (b : A) : (∑ x : Fin (n+1) → A, if x (Fin.last n) = b then w x * f (x 0) else 0) =
      μ n b * past μ Q f n b := weighted_terminal μ Q hQ f n b
  have he : (∑ x : Fin (n+1) → A, w x * f (x 0)) =
      ∑ b, μ n b * past μ Q f n b := by
    simpa only [mul_one, hw] using
      (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) (fun x => w x*f (x 0)) (fun _ => (1:ℝ)))
  have hg : (∑ x : Fin (n+1) → A, w x * g (x (Fin.last n))) = ∑ b, μ n b*g b := by
    simpa only [hm] using (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) w g)
  have hfg : (∑ x : Fin (n+1) → A, w x * f (x 0) * g (x (Fin.last n))) =
      ∑ b, μ n b * past μ Q f n b * g b := by
    simpa only [hw] using (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n))
      (fun x => w x*f (x 0)) g)
  change (∑ x, w x * _) = _
  calc
    _ = (∑ x, w x*f (x 0)) + (∑ x, w x*g (x (Fin.last n))) -
        2*(∑ x, w x*f (x 0)*g (x (Fin.last n))) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [he,hg,hfg]
      unfold defect
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma response_past (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (t n : ℕ) :
    defect (μ t) (response μ Q t n g) (past μ Q f t) =
      defect (μ (t+n)) g (past μ Q f (t+n)) := by
  induction n generalizing t with
  | zero => simp only [response, Nat.add_zero]
  | succ n ih =>
    change defect (μ t) (action (μ t) (Q t) (response μ Q (t+1) n g)) (past μ Q f t) = _
    rw [transfer_defect (hQ t)]
    change defect (μ (t+1)) (response μ Q (t+1) n g) (past μ Q f (t+1)) = _
    rw [ih, show (t+1)+n = t+(n+1) by omega]

/-- One may test at ANY interior location: past and future are the honest
conditional responses of the already constructed product law. -/
theorem endpoint_defect_at (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (t n : ℕ) (ht : t ≤ n) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
        (f (x 0) + g (x (Fin.last n)) - 2*f (x 0)*g (x (Fin.last n)))) =
      defect (μ t) (response μ Q t (n-t) g) (past μ Q f t) := by
  rw [endpoint_defect μ Q hQ, response_past μ Q hQ, Nat.add_sub_of_le ht]
end BoundedTreewidthL1.ExpandedChain

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

end BoundedTreewidthL1.ReservedSuffix

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

end BoundedTreewidthL1.ReservedSuffix

namespace BoundedTreewidthL1.ExpandedPathTests
open ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix ExpandedChain
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def distance (M : ℝ) (F : ℕ → ι → V → ℝ)
    (Q : ℕ → State ι V → State ι V → ℝ) (n : ℕ) (y z : V) : ℝ :=
  ∑ x : Fin (n+1) → State ι V,
    MarkovProduct.weight (fun _ => State ι V) (weight M (F 0))
      (MarkovProduct.couplingKernel (fun _ => State ι V) (fun s => weight M (F s)) Q) n x *
      (if label (x 0) y = label (x (Fin.last n)) z then 0 else 1)

lemma distance_at (M : ℝ) (F : ℕ → ι → V → ℝ)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (y z : V) :
    distance M F Q (t+(n+1)) y z =
      defect (weight M (F t)) (action (weight M (F t)) (Q t)
        (response (fun s => weight M (F s)) Q (t+1) n (fun b => if label b z then 1 else 0)))
        (past (fun s => weight M (F s)) Q (fun b => if label b y then 1 else 0) t) := by
  have he := endpoint_defect_at (fun s => weight M (F s)) Q hQ
    (fun b => if label b y then 1 else 0) (fun b => if label b z then 1 else 0)
    t (t+(n+1)) (by omega)
  rw [Nat.add_sub_cancel_left, response] at he
  rw [← he]
  unfold distance
  apply Finset.sum_congr rfl
  intro x _
  cases hy : label (x 0) y <;> cases hz : label (x (Fin.last (t+(n+1)))) z <;> norm_num [hy,hz]

end BoundedTreewidthL1.ExpandedPathTests

end OAI
