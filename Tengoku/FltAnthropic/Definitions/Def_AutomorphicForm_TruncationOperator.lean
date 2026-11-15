import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm

section GrowthDecay

variable {G : Type*}

def IsSlowlyIncreasingOn (S : Set G) (H : G → ℝ) (φ : G → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ g ∈ S, ‖φ g‖ ≤ C * H g ^ N

def IsRapidlyDecreasingOn (S : Set G) (H : G → ℝ) (φ : G → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ S, ‖φ g‖ ≤ C * (H g)⁻¹ ^ N

/--
@isnad1 id=isslowly.1h5v.s5.15dcc2d5c811 from=translated src=- shape=79b6f6b0 vocab=76fb858c
-/
theorem isSlowlyIncreasingOn_of_bounded {S : Set G} {H : G → ℝ} {φ : G → ℂ} {C : ℝ}
    (hC : ∀ g ∈ S, ‖φ g‖ ≤ C) : IsSlowlyIncreasingOn S H φ :=
  ⟨C, 0, fun g hg => by simpa using hC g hg⟩

/--
@isnad1 id=isslowly.0h3v.s4.2ff8a02b1ed4 from=translated src=- shape=b9db75e6 vocab=0a32a070
-/
theorem isSlowlyIncreasingOn_const_one (S : Set G) (H : G → ℝ) :
    IsSlowlyIncreasingOn S H (fun _ => (1 : ℂ)) :=
  isSlowlyIncreasingOn_of_bounded (C := 1) (fun _ _ => by simp)

/--
@isnad1 id=israpidl.0h3v.s4.526aa95c481c from=translated src=- shape=b9db75e6 vocab=28789147
-/
theorem isRapidlyDecreasingOn_zero (S : Set G) (H : G → ℝ) :
    IsRapidlyDecreasingOn S H (fun _ => (0 : ℂ)) :=
  fun _ => ⟨0, fun _ _ => by simp⟩

/--
@isnad1 id=isslowly.1h4v.s4.601ffd1a0b7d from=translated src=- shape=81a668f2 vocab=88b846b0
-/
theorem IsRapidlyDecreasingOn.isSlowlyIncreasingOn {S : Set G} {H : G → ℝ} {φ : G → ℂ}
    (h : IsRapidlyDecreasingOn S H φ) : IsSlowlyIncreasingOn S H φ := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, 0, fun g hg => by simpa using hC g hg⟩

def highSet (H : G → ℝ) (T : ℝ) : Set G :=
  {g : G | T < H g}

/--
@isnad1 id=iff.0h4v.s4.5e74f262191d from=translated src=- shape=c7439a49 vocab=7dfae91d
-/
theorem mem_highSet_iff {H : G → ℝ} {T : ℝ} {g : G} : g ∈ highSet H T ↔ T < H g :=
  Iff.rfl

end GrowthDecay

section LambdaT

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

noncomputable def lambdaT (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) :
    G → ℂ :=
  fun g => φ g - Set.indicator (highSet H T) (constantTerm μ u φ) g

/--
@isnad1 id=eq.0h8v.s6.7a2ffb29e771 from=translated src=- shape=c440810a vocab=03ec6143
-/
theorem lambdaT_apply (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) (g : G) :
    lambdaT μ u H T φ g = φ g - Set.indicator (highSet H T) (constantTerm μ u φ) g :=
  rfl

/--
@isnad1 id=eq.1h8v.s5.60c1cf0d2fc2 from=translated src=- shape=4d8d873f vocab=2b1a8353
-/
theorem lambdaT_apply_of_le (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ} {g : G}
    (hg : H g ≤ T) (φ : G → ℂ) : lambdaT μ u H T φ g = φ g := by
  unfold lambdaT
  rw [Set.indicator_of_notMem (by simpa [mem_highSet_iff, not_lt] using hg), sub_zero]

/--
@isnad1 id=eq.1h8v.s6.309954202d4a from=translated src=- shape=0e3a442a vocab=da736dc8
-/
theorem lambdaT_apply_of_lt (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ} {g : G}
    (hg : T < H g) (φ : G → ℂ) : lambdaT μ u H T φ g = φ g - constantTerm μ u φ g := by
  unfold lambdaT
  rw [Set.indicator_of_mem (mem_highSet_iff.mpr hg)]

/--
@isnad1 id=eq.0h6v.s5.50f3cfff63f1 from=translated src=- shape=694b0d6c vocab=4d770eb2
-/
theorem lambdaT_zero (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) :
    lambdaT μ u H T (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext g
  simp [lambdaT]

/--
@isnad1 id=eq.1h7v.s5.83b996b16f28 from=translated src=- shape=ba259d8b vocab=91b0aef3
-/
theorem lambdaT_of_isCuspidalFn (μ : Measure Q) (u : Q → G) {φ : G → ℂ}
    (hφ : IsCuspidalFn μ u φ) (H : G → ℝ) (T : ℝ) : lambdaT μ u H T φ = φ := by
  funext g
  unfold lambdaT
  by_cases hmem : g ∈ highSet H T
  · rw [Set.indicator_of_mem hmem, hφ g, sub_zero]
  · rw [Set.indicator_of_notMem hmem, sub_zero]

end LambdaT

end AutomorphicForm
