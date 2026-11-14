import Tengoku.Piirrationalitymeasure.Formalization.FiniteConewiseLinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact local homogeneous models of finite expressions in affine functions, min, and max. -/

namespace PiIrrationality

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure LocalPolyhedral (f : E → ℝ) where
  tangent : E → ℝ
  continuous_tangent : Continuous tangent
  homogeneous : ∀ x : E, ∀ t : ℝ, 0 ≤ t → tangent (t • x) = t * tangent x
  conewise_linear : FiniteConewiseLinear tangent
  finite_linear_selection : ∃ S : Finset (E →L[ℝ] ℝ), ∀ x : E,
    ∃ l ∈ S, tangent x = l x
  eventually_exact : ∀ᶠ x : E in 𝓝 0, f x = f 0 + tangent x

namespace LocalPolyhedral

variable {f g : E → ℝ}

theorem tangent_zero (M : LocalPolyhedral f) : M.tangent 0 = 0 := by
  simpa using M.homogeneous 0 0 (le_refl _)

theorem continuousAt (M : LocalPolyhedral f) : ContinuousAt f 0 :=
  (continuous_const.add M.continuous_tangent).continuousAt.congr_of_eventuallyEq
    M.eventually_exact

noncomputable def congr (M : LocalPolyhedral f) (he : f =ᶠ[𝓝 0] g) : LocalPolyhedral g where
  tangent := M.tangent
  continuous_tangent := M.continuous_tangent
  homogeneous := M.homogeneous
  conewise_linear := M.conewise_linear
  finite_linear_selection := M.finite_linear_selection
  eventually_exact := by
    have hzero := he.self_of_nhds
    filter_upwards [M.eventually_exact, he] with x hx heq
    rw [← heq, ← hzero]
    exact hx

noncomputable def affine (b : ℝ) (l : E →L[ℝ] ℝ) :
    LocalPolyhedral (fun x => b + l x) where
  tangent := l
  continuous_tangent := l.continuous
  homogeneous := by intro x t ht; simp
  conewise_linear := FiniteConewiseLinear.linear l
  finite_linear_selection := by
    classical
    exact ⟨{l}, fun x => ⟨l, by simp, rfl⟩⟩
  eventually_exact := Eventually.of_forall (by intro x; simp)

noncomputable def const (b : ℝ) : LocalPolyhedral (fun _ : E => b) := by
  exact (affine b 0).congr (Eventually.of_forall (by intro x; simp))

noncomputable def linear (l : E →L[ℝ] ℝ) : LocalPolyhedral (fun x => l x) := by
  exact (affine 0 l).congr (Eventually.of_forall (by intro x; simp))

noncomputable def add (M : LocalPolyhedral f) (N : LocalPolyhedral g) :
    LocalPolyhedral (fun x => f x + g x) where
  tangent := fun x => M.tangent x + N.tangent x
  continuous_tangent := M.continuous_tangent.add N.continuous_tangent
  homogeneous := by
    intro x t ht
    rw [M.homogeneous x t ht, N.homogeneous x t ht]
    ring
  conewise_linear := M.conewise_linear.add N.conewise_linear
  finite_linear_selection := by
    classical
    obtain ⟨S, hS⟩ := M.finite_linear_selection
    obtain ⟨T, hT⟩ := N.finite_linear_selection
    refine ⟨S.image₂ (· + ·) T, ?_⟩
    intro x
    obtain ⟨l, hl, he⟩ := hS x
    obtain ⟨m, hm, hf⟩ := hT x
    exact ⟨l + m, Finset.mem_image₂.mpr ⟨l, hl, m, hm, rfl⟩, by simp [he, hf]⟩
  eventually_exact := by
    filter_upwards [M.eventually_exact, N.eventually_exact] with x hx hy
    rw [hx, hy]
    ring

noncomputable def neg (M : LocalPolyhedral f) : LocalPolyhedral (fun x => -f x) where
  tangent := fun x => -M.tangent x
  continuous_tangent := M.continuous_tangent.neg
  homogeneous := by intro x t ht; rw [M.homogeneous x t ht]; ring
  conewise_linear := M.conewise_linear.neg
  finite_linear_selection := by
    classical
    obtain ⟨S, hS⟩ := M.finite_linear_selection
    refine ⟨S.image Neg.neg, ?_⟩
    intro x
    obtain ⟨l, hl, he⟩ := hS x
    exact ⟨-l, Finset.mem_image.mpr ⟨l, hl, rfl⟩, by simp [he]⟩
  eventually_exact := by
    filter_upwards [M.eventually_exact] with x hx
    rw [hx]
    ring

noncomputable def sub (M : LocalPolyhedral f) (N : LocalPolyhedral g) :
    LocalPolyhedral (fun x => f x - g x) := by
  exact (M.add N.neg).congr (Eventually.of_forall (by intro x; simp [sub_eq_add_neg]))

noncomputable def max (M : LocalPolyhedral f) (N : LocalPolyhedral g) :
    LocalPolyhedral (fun x => max (f x) (g x)) := by
  classical
  by_cases hlt : f 0 < g 0
  · exact N.congr (by
      filter_upwards [M.continuousAt.eventually_lt N.continuousAt hlt] with x hx
      exact (max_eq_right hx.le).symm)
  by_cases heq : f 0 = g 0
  · refine ⟨(fun x => Max.max (M.tangent x) (N.tangent x)),
      M.continuous_tangent.max N.continuous_tangent, ?_,
      M.conewise_linear.max N.conewise_linear, ?_, ?_⟩
    · intro x t ht
      rw [M.homogeneous x t ht, N.homogeneous x t ht, mul_max_of_nonneg _ _ ht]
    · obtain ⟨S, hS⟩ := M.finite_linear_selection
      obtain ⟨T, hT⟩ := N.finite_linear_selection
      refine ⟨S ∪ T, ?_⟩
      intro x
      by_cases hx : M.tangent x ≤ N.tangent x
      · obtain ⟨l, hl, he⟩ := hT x
        exact ⟨l, Finset.mem_union_right S hl, by rwa [max_eq_right hx]⟩
      · obtain ⟨l, hl, he⟩ := hS x
        exact ⟨l, Finset.mem_union_left T hl, by rwa [max_eq_left (le_of_not_ge hx)]⟩
    · filter_upwards [M.eventually_exact, N.eventually_exact] with x hx hy
      rw [hx, hy, heq, max_self, ← add_max]
  · have hgt : g 0 < f 0 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
    exact M.congr (by
      filter_upwards [N.continuousAt.eventually_lt M.continuousAt hgt] with x hx
      exact (max_eq_left hx.le).symm)

noncomputable def min (M : LocalPolyhedral f) (N : LocalPolyhedral g) :
    LocalPolyhedral (fun x => min (f x) (g x)) := by
  exact (M.neg.max N.neg).neg.congr
    (Eventually.of_forall (by intro x; simp only [max_neg_neg, neg_neg]))

noncomputable def sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (M : ∀ i ∈ S, LocalPolyhedral (f i)) : LocalPolyhedral (fun x => ∑ i ∈ S, f i x) := by
  classical
  have hex : ∀ T : Finset ι, (∀ i ∈ T, LocalPolyhedral (f i)) →
      Nonempty (LocalPolyhedral (fun x => ∑ i ∈ T, f i x)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨(const 0).congr (Eventually.of_forall (by intro x; simp))⟩
    | @insert i T hi ih =>
        intro N
        obtain ⟨R⟩ := ih (fun j hj => N j (Finset.mem_insert_of_mem hj))
        exact ⟨((N i (Finset.mem_insert_self _ _)).add R).congr
          (Eventually.of_forall (by intro x; simp [hi]))⟩
  exact Classical.choice (hex S M)

theorem tangent_bound (M : LocalPolyhedral f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E, |M.tangent x| ≤ B * ‖x‖ := by
  obtain ⟨S, hS⟩ := M.finite_linear_selection
  refine ⟨∑ l ∈ S, ‖l‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro x
  obtain ⟨l, hl, he⟩ := hS x
  rw [he, ← Real.norm_eq_abs]
  exact (l.le_opNorm x).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun l _ => norm_nonneg l) hl) (norm_nonneg _))

end LocalPolyhedral

end PiIrrationality
