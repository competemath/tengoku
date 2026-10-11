import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.ExpandedParticles

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.OrderedSweepFlow
open scoped BigOperators

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def fiber (b : α → β) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun y => b y = b x)

noncomputable def mass (μ : α → ℝ) (b : α → β) (x : α) : ℝ :=
  ∑ y ∈ fiber b x, μ y

noncomputable def bath (μ : α → ℝ) (b : α → β) (f : α → ℝ) (x : α) : ℝ :=
  (∑ y ∈ fiber b x, μ y * f y) / mass μ b x

noncomputable def total (μ f : α → ℝ) : ℝ := ∑ x, μ x * f x

noncomputable def risk (μ f : α → ℝ) (p : α → Bool) : ℝ :=
  ∑ x, μ x * (if p x then 1 - f x else f x)

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

lemma mem_fiber
    {α : Type treewidthLevel1} {β : Type treewidthLevel2} [Fintype α] [LinearOrder α]
    [LinearOrder β]
    (b : α → β) (x y : α) : y ∈ fiber b x ↔ b y = b x := by
  classical
  simp [fiber]

lemma fiber_eq (b : α → β) {x y : α} (h : b x = b y) : fiber b x = fiber b y := by
  classical
  ext z
  simp only [mem_fiber, h]

lemma mass_pos (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β) (x : α) :
    0 < mass μ b x := by
  classical
  exact Finset.sum_pos (fun y _ => hμ y) ⟨x, (mem_fiber b x x).mpr rfl⟩

lemma bath_const_fiber (μ : α → ℝ) (b : α → β) (f : α → ℝ) {x y : α}
    (h : b x = b y) : bath μ b f x = bath μ b f y := by
  unfold bath mass
  rw [fiber_eq b h]

lemma bath_le (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (x : α) (c : ℝ) (hc : ∀ y ∈ fiber b x, f y ≤ c) :
    bath μ b f x ≤ c := by
  rw [bath, div_le_iff₀ (mass_pos μ hμ b x)]
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y hy => by nlinarith [hμ y, hc y hy])

lemma le_bath (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (x : α) (c : ℝ) (hc : ∀ y ∈ fiber b x, c ≤ f y) :
    c ≤ bath μ b f x := by
  rw [bath, le_div_iff₀ (mass_pos μ hμ b x)]
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y hy => by nlinarith [hμ y, hc y hy])

lemma fiber_lt (b : α → β) (hb : Monotone b) {x y s t : α}
    (hxy : b x < b y) (hs : s ∈ fiber b x) (ht : t ∈ fiber b y) : s < t := by
  have hs' := (mem_fiber b x s).mp hs
  have ht' := (mem_fiber b y t).mp ht
  by_contra h
  have := hb (le_of_not_gt h)
  rw [hs', ht'] at this
  exact (not_le_of_gt hxy) this

theorem bath_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Monotone f) :
    Monotone (bath μ b f) := by
  intro x y hxy
  rcases (hb hxy).eq_or_lt with h | h
  · exact le_of_eq (bath_const_fiber μ b f h)
  · apply le_bath μ hμ b f y
    intro t ht
    apply bath_le μ hμ b f x
    intro s hs
    exact hf (fiber_lt b hb h hs ht).le

theorem bath_antitone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Antitone f) :
    Antitone (bath μ b f) := by
  intro x y hxy
  rcases (hb hxy).eq_or_lt with h | h
  · exact le_of_eq (bath_const_fiber μ b f h.symm)
  · apply le_bath μ hμ b f x
    intro s hs
    apply bath_le μ hμ b f y
    intro t ht
    exact hf (fiber_lt b hb h hs ht).le

lemma bath_bounds (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : α) :
    0 ≤ bath μ b f x ∧ bath μ b f x ≤ 1 :=
  ⟨le_bath μ hμ b f x 0 (fun y _ => (hf y).1),
   bath_le μ hμ b f x 1 (fun y _ => (hf y).2)⟩

lemma bath_expand
    {α : Type treewidthLevel1} {β : Type treewidthLevel2} [Fintype α] [LinearOrder α]
    [LinearOrder β]
    (μ : α → ℝ) (b : α → β) (f : α → ℝ) (x : α) :
    bath μ b f x = ∑ y, if b y = b x then μ y * f y / mass μ b x else 0 := by
  classical
  simp [bath, fiber, Finset.sum_filter, Finset.sum_div, ite_div]

theorem bath_total (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (f : α → ℝ) : total μ (bath μ b f) = total μ f := by
  classical
  unfold total
  simp_rw [bath_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have he (x : α) :
      μ x * (if b y = b x then μ y * f y / mass μ b x else 0) =
      (if b x = b y then μ x else 0) * (μ y * f y / mass μ b y) := by
    by_cases h : b x = b y
    · have hm : mass μ b x = mass μ b y := by unfold mass; rw [fiber_eq b h]
      simp [h, hm]
    · simp [h, Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hm : (∑ x, if b x = b y then μ x else 0) = mass μ b y := by
    simp [mass, fiber, Finset.sum_filter]
  rw [hm]
  field_simp [ne_of_gt (mass_pos μ hμ b y)]

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def defect (μ f p : α → ℝ) : ℝ :=
  ∑ x, μ x * (f x + p x - 2 * f x * p x)

noncomputable def optimal (μ : α → ℝ) (b : α → β) (f : α → ℝ) : α → Bool :=
  fun x => decide (1 / 2 < bath μ b f x)

noncomputable def labelReal (p : α → Bool) : α → ℝ :=
  fun x => if p x then 1 else 0

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

lemma defect_eq
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (μ f p : α → ℝ) :
    defect μ f p = total μ f + total μ p - 2 * total μ (fun x => f x * p x) := by
  classical
  simp only [defect, total, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma bath_mul (μ : α → ℝ) (b : α → β) (f p : α → ℝ)
    (hp : ∀ x y, b x = b y → p x = p y) (x : α) :
    bath μ b (fun y => f y * p y) x = bath μ b f x * p x := by
  classical
  unfold bath
  have h : (∑ y ∈ fiber b x, μ y * (f y * p y)) =
      (∑ y ∈ fiber b x, μ y * f y) * p x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hp y x ((mem_fiber b x y).mp hy)]
    ring
  rw [h]
  ring

lemma defect_bath (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f p : α → ℝ) (hp : ∀ x y, b x = b y → p x = p y) :
    defect μ (bath μ b f) p = defect μ f p := by
  rw [defect_eq, defect_eq, bath_total μ hμ b f]
  congr 1
  congr 1
  have h := bath_total μ hμ b (fun x => f x * p x)
  have hh : bath μ b (fun x => f x * p x) = (fun x => bath μ b f x * p x) :=
    funext (bath_mul μ b f p hp)
  rw [hh] at h
  exact h

lemma optimal_fiber (μ : α → ℝ) (b : α → β) (f : α → ℝ)
    {x y : α} (h : b x = b y) : optimal μ b f x = optimal μ b f y := by
  simp only [optimal, bath_const_fiber μ b f h]

theorem optimal_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Monotone f) :
    Monotone (optimal μ b f) := by
  intro x y hxy
  have h := bath_monotone μ hμ b hb f hf hxy
  simp only [optimal]
  by_cases hx : 1 / 2 < bath μ b f x
  · have hy : 1 / 2 < bath μ b f y := hx.trans_le h
    simp only [hx, hy, decide_true, le_refl]
  · simp only [hx, decide_false, Bool.false_le]

theorem optimal_defect_le (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (f p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hpb : ∀ x y, b x = b y → p x = p y) :
    defect μ f (labelReal (optimal μ b f)) ≤ defect μ f p := by
  classical
  have hc : ∀ x y, b x = b y →
      labelReal (optimal μ b f) x = labelReal (optimal μ b f) y := by
    intro x y h
    simp only [labelReal, optimal_fiber μ b f h]
  rw [← defect_bath μ hμ b f _ hc, ← defect_bath μ hμ b f p hpb]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hμ x).le
  dsimp [labelReal, optimal]
  split_ifs with h
  · have h' : 1 / 2 < bath μ b f x := of_decide_eq_true h
    simp only [h, ↓reduceIte]
    nlinarith [(hp x).2]
  · have h' : ¬1 / 2 < bath μ b f x := by simpa only [decide_eq_true_eq] using h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    nlinarith [(hp x).1]

lemma labelReal_bounds
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (p : α → Bool) (x : α) :
    0 ≤ labelReal p x ∧ labelReal p x ≤ 1 := by
  simp only [labelReal]
  split <;> norm_num

lemma defect_mean_bound
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (μ f p : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    |total μ f - total μ p| ≤ defect μ f p := by
  classical
  have hl : total μ p - total μ f ≤ defect μ f p := by
    unfold total defect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun x _ => by
      nlinarith [mul_nonneg (hμ x) (mul_nonneg (hf x).1 (sub_nonneg.mpr (hp x).2))])
  have hr : total μ f - total μ p ≤ defect μ f p := by
    unfold total defect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun x _ => by
      nlinarith [mul_nonneg (hμ x) (mul_nonneg (hp x).1 (sub_nonneg.mpr (hf x).2))])
  exact abs_le.mpr ⟨by linarith, hr⟩

lemma pair_mean_bound (μ f g p : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    |total μ f - total μ g| ≤ defect μ f p + defect μ g p := by
  have h := abs_sub_le (total μ f) (total μ p) (total μ g)
  rw [abs_sub_comm (total μ p)] at h
  exact h.trans (add_le_add (defect_mean_bound μ f p hμ hf hp)
    (defect_mean_bound μ g p hμ hg hp))

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

/-- On a chain of nested cuts, a monotone classifier determined by its trace
on a bag is either constant or evaluation at one of that bag's vertices. -/
theorem monotone_classifier {P : Type*} (labels : α → P → Bool)
    (hl : ∀ p, Monotone (fun x => labels x p)) (c : α → Bool) (hc : Monotone c)
    (htrace : ∀ x y, (∀ p, labels x p = labels y p) → c x = c y) :
    c = (fun _ => false) ∨ c = (fun _ => true) ∨ ∃ p, c = (fun x => labels x p) := by
  classical
  by_cases hf : ∀ x, c x = false
  · exact Or.inl (funext hf)
  by_cases ht : ∀ x, c x = true
  · exact Or.inr (Or.inl (funext ht))
  push Not at hf ht
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hf
  have ha' : c a = false := by cases h : c a <;> simp_all
  have hb' : c b = true := by cases h : c b <;> simp_all
  let lo := Finset.univ.filter (fun x => c x = false)
  let hi := Finset.univ.filter (fun x => c x = true)
  have hlo : lo.Nonempty := ⟨a, by simp [lo, ha']⟩
  have hhi : hi.Nonempty := ⟨b, by simp [hi, hb']⟩
  let u := lo.max' hlo
  let v := hi.min' hhi
  have hu : c u = false := by simpa [lo] using lo.max'_mem hlo
  have hv : c v = true := by simpa [hi] using hi.min'_mem hhi
  have huv : u ≤ v := by
    by_contra h
    have hh := hc (le_of_lt (lt_of_not_ge h))
    rw [hu, hv] at hh
    contradiction
  have hn : ¬∀ p, labels u p = labels v p := by
    intro h
    have := htrace u v h
    rw [hu, hv] at this
    contradiction
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hlp : labels u p ≤ labels v p := hl p huv
  have hup : labels u p = false := by
    cases h : labels u p <;> cases h' : labels v p <;> simp_all
    exact Bool.noConfusion (hlp rfl)
  have hvp : labels v p = true := by
    cases h : labels u p <;> cases h' : labels v p <;> simp_all
  refine Or.inr (Or.inr ⟨p, funext (fun x => ?_)⟩)
  cases hx : c x with
  | false =>
    have hxu : x ≤ u := lo.le_max' x (by simp [lo, hx])
    have h : labels x p ≤ labels u p := hl p hxu
    rw [hup] at h
    cases hx' : labels x p <;> simp_all
    exact Bool.noConfusion (h rfl)
  | true =>
    have hvx : v ≤ x := hi.min'_le x (by simp [hi, hx])
    have h : labels v p ≤ labels x p := hl p hvx
    rw [hvp] at h
    cases hx' : labels x p <;> simp_all
    exact Bool.noConfusion (h rfl)

/-- The height-gap transport estimate for a retained ordered sweep. `f` is the
backward endpoint response; interval heat baths keep it monotone and preserve
its mean. The comparison predictor may be arbitrarily randomized by the past. -/
theorem height_transport {P : Type*} (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (labels : α → P → Bool)
    (hl : ∀ p, Monotone (fun x => labels x p))
    (htrace : ∀ x y, (∀ p, labels x p = labels y p) → b x = b y)
    (f p : α → ℝ) (hf : Monotone f) (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hpb : ∀ x y, b x = b y → p x = p y)
    (t : ℝ) (h0 : t ≤ total μ f) (h1 : t ≤ total μ (fun _ => 1) - total μ f)
    (hgap : ∀ v, t ≤ |total μ f - total μ (labelReal (fun x => labels x v))|) :
    t ≤ defect μ f p := by
  let c := optimal μ b f
  have hc := optimal_monotone μ hμ b hb f hf
  have hcTrace : ∀ x y, (∀ v, labels x v = labels y v) → c x = c y := by
    intro x y h
    exact optimal_fiber μ b f (htrace x y h)
  have ha := monotone_classifier labels hl c hc hcTrace
  have hmin := optimal_defect_le μ hμ b f p hp hpb
  have hmean := (defect_mean_bound μ f (labelReal c) (fun x => (hμ x).le) hfb
    (labelReal_bounds c)).trans hmin
  rcases ha with he | he | ⟨v, he⟩
  · have hm : total μ (labelReal c) = 0 := by simp [he, labelReal, total]
    rw [hm, sub_zero] at hmean
    have hn : 0 ≤ total μ f := Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x).le (hfb x).1)
    rw [abs_of_nonneg hn] at hmean
    exact h0.trans hmean
  · have hm : total μ (labelReal c) = total μ (fun _ => 1) := by simp [he, labelReal, total]
    rw [hm] at hmean
    have hn : total μ f ≤ total μ (fun _ => 1) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfb x).2 (hμ x).le)
    rw [abs_of_nonpos (sub_nonpos.mpr hn)] at hmean
    exact h1.trans (by linarith)
  · rw [he] at hmean
    exact (hgap v).trans hmean

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def execute (μ : α → ℝ) (bs : List (α → β)) (f : α → ℝ) : α → ℝ :=
  bs.foldr (fun b g => bath μ b g) f

lemma execute_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (hb : ∀ b ∈ bs, Monotone b)
    (f : α → ℝ) (hf : Monotone f) : Monotone (execute μ bs f) := by
  induction bs with
  | nil => exact hf
  | cons b bs ih =>
    exact bath_monotone μ hμ b (hb b (by simp)) _
      (ih (fun c hc => hb c (by simp [hc])))

lemma execute_total (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (f : α → ℝ) : total μ (execute μ bs f) = total μ f := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change total μ (bath μ b (execute μ bs f)) = _
    rw [bath_total μ hμ, ih]

lemma execute_bounds (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ execute μ bs f x ∧ execute μ bs f x ≤ 1 := by
  induction bs with
  | nil => exact hf
  | cons b bs ih => exact bath_bounds μ hμ b _ ih
end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedReservation
attribute [local instance] Classical.decEq Classical.propDecidable
open MeasureTheory Set
open scoped BigOperators
variable {V : Type*} [Fintype V]

noncomputable def trueSet (ω : V → Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ω v = true)

def Carrier (M : ℝ) (F : V → ℝ) := {ω : V → Bool // 0 < (sweep M F).real {ω}}

noncomputable instance (M : ℝ) (F : V → ℝ) : Fintype (Carrier M F) := by
  unfold Carrier
  infer_instance

noncomputable def weight (M : ℝ) (F : V → ℝ) (ω : Carrier M F) : ℝ :=
  (sweep M F).real {ω.val}

lemma weight_pos
    {V : Type treewidthLevel1} [Fintype V]
    (M : ℝ) (F : V → ℝ) (ω : Carrier M F) : 0 < weight M F ω := ω.property

lemma thresholds_nested (F : V → ℝ) (s t : ℝ) (hst : s ≤ t) :
    trueSet (thresholdLabels F t) ⊆ trueSet (thresholdLabels F s) := by
  classical
  intro v hv
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and,
    thresholdLabels, decide_eq_true_eq] at hv ⊢
  exact hst.trans_lt hv

lemma trueSet_injective : Function.Injective (trueSet (V := V)) := by
  classical
  intro a b h
  funext v
  have he : v ∈ trueSet a ↔ v ∈ trueSet b := by rw [h]
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
  cases ha : a v <;> cases hb : b v <;> simp_all

noncomputable def traceRank (M : ℝ) (F : V → ℝ) (P : Finset V) (ω : Carrier M F) : ℕ :=
  (P.filter (fun v => ω.val v = true)).card

lemma sum_carrier (M : ℝ) (F : V → ℝ) (g : (V → Bool) → ℝ) :
    (∑ a : Carrier M F, weight M F a * g a.val) =
      ∑ a : V → Bool, (sweep M F).real {a} * g a := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun a : V → Bool => 0 < (sweep M F).real {a})
    (fun a => (sweep M F).real {a} * g a)
  have hz : (∑ a : {a : V → Bool // ¬0 < (sweep M F).real {a}},
      (sweep M F).real {a.val} * g a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have ha : (sweep M F).real {a.val} = 0 :=
      le_antisymm (le_of_not_gt a.property) measureReal_nonneg
    simp [ha]
  rw [hz, add_zero] at he
  exact he

lemma sum_event (M : ℝ) (F : V → ℝ) (p : (V → Bool) → Prop) :
    (∑ a : V → Bool, (sweep M F).real {a} * (if p a then 1 else 0)) =
      (sweep M F).real {a | p a} := by
  classical
  have h := sum_measureReal_singleton (μ := sweep M F) (Finset.univ.filter p)
  simpa only [Finset.sum_filter, Finset.coe_filter, Finset.coe_univ,
    Set.ofPred_mem_eq, Set.mem_univ, Finset.mem_univ, true_and, mul_ite, mul_one, mul_zero] using h

end BoundedTreewidthL1.OrderedReservation

namespace BoundedTreewidthL1.OrderedReservation
attribute [local instance] Classical.decEq Classical.propDecidable
open MeasureTheory Set OrderedSweepFlow
open scoped BigOperators
variable {V : Type*} [Fintype V]

end BoundedTreewidthL1.OrderedReservation

end OAI
