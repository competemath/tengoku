import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku.Seed.Order.Filter.AtTopBot.Basic
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absorbing a contraction into a locally finite supremum

For a real function `f`, the running supremum is taken over the closed interval
`[a,x]`. Local boundedness above is an explicit hypothesis; neither continuity
nor a uniform bound is assumed. An eventual inequality
`f x ≤ θ * initialIntervalSup f a x + E`, with `0 ≤ θ < 1`, then implies a
uniform upper bound for both `f` and its running supremum on `[a,∞)`.

The bound is `max (initialIntervalSup f a x₀) (E / (1 - θ))`, where `x₀ ≥ a`
is a threshold for the inequality. It holds even on the initial interval.
The upper-bound argument permits any real `E`; in particular it covers `E ≥ 0`.
An additional nonnegativity hypothesis on `f` gives an absolute-value bound.
There are no arithmetic or distribution hypotheses.
-/

noncomputable section

open Set Filter

namespace TwinPrime.Analytic

/-- The supremum on an initial closed interval. Its useful properties below
always supply a nonempty interval and local boundedness above.-/
def initialIntervalSup (f : ℝ → ℝ) (a x : ℝ) : ℝ := sSup (f '' Icc a x)

theorem initialInterval_image_nonempty (f : ℝ → ℝ) {a x : ℝ} (hax : a ≤ x) :
    (f '' Icc a x).Nonempty :=
  ⟨f a, a, ⟨le_rfl, hax⟩, rfl⟩

/-- Local boundedness makes the conditional supremum the actual least upper bound.-/
theorem initialIntervalSup_isLUB (f : ℝ → ℝ) {a x : ℝ} (hax : a ≤ x)
    (hbdd : BddAbove (f '' Icc a x)) :
    IsLUB (f '' Icc a x) (initialIntervalSup f a x) :=
  isLUB_csSup (initialInterval_image_nonempty f hax) hbdd

theorem le_initialIntervalSup (f : ℝ → ℝ) {a t x : ℝ}
    (hbdd : BddAbove (f '' Icc a x)) (ht : t ∈ Icc a x) :
    f t ≤ initialIntervalSup f a x :=
  le_csSup hbdd ⟨t, ht, rfl⟩

theorem initialIntervalSup_mono (f : ℝ → ℝ) {a x y : ℝ}
    (hax : a ≤ x) (hxy : x ≤ y) (hbdd : BddAbove (f '' Icc a y)) :
    initialIntervalSup f a x ≤ initialIntervalSup f a y := by
  apply csSup_le (initialInterval_image_nonempty f hax)
  rintro _ ⟨t, ht, rfl⟩
  exact le_initialIntervalSup f hbdd ⟨ht.1, ht.2.trans hxy⟩

theorem initialIntervalSup_monotoneOn (f : ℝ → ℝ) (a : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x)) :
    MonotoneOn (initialIntervalSup f a) (Ici a) := by
  intro x hx y hy hxy
  exact initialIntervalSup_mono f hx hxy (hlocal y hy)

theorem initialIntervalSup_nonneg (f : ℝ → ℝ) {a x : ℝ} (hax : a ≤ x)
    (hbdd : BddAbove (f '' Icc a x)) (ha : 0 ≤ f a) :
    0 ≤ initialIntervalSup f a x :=
  ha.trans (le_initialIntervalSup f hbdd ⟨le_rfl, hax⟩)

/-- The elementary absorption step does not require the supremum to be attained.-/
theorem le_max_of_le_max_contraction {u b θ E : ℝ} (hθ : θ < 1)
    (h : u ≤ max b (θ * u + E)) : u ≤ max b (E / (1 - θ)) := by
  rcases le_max_iff.mp h with h | h
  · exact h.trans (le_max_left _ _)
  · have hu : u ≤ E / (1 - θ) := by
      apply (le_div_iff₀ (sub_pos.mpr hθ)).mpr
      nlinarith
    exact hu.trans (le_max_right _ _)

/-- A threshold contraction bounds every initial-interval supremum by one
explicit constant. The hypothesis provides only a separate bound on each
finite interval, not a bound uniform in the endpoint.-/
theorem initialIntervalSup_le_of_contraction (f : ℝ → ℝ) (a x₀ θ E : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x))
    (hax₀ : a ≤ x₀) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hcontract : ∀ x, x₀ ≤ x → f x ≤ θ * initialIntervalSup f a x + E)
    {x : ℝ} (hax : a ≤ x) :
    initialIntervalSup f a x ≤ max (initialIntervalSup f a x₀) (E / (1 - θ)) := by
  apply le_max_of_le_max_contraction hθ₁
  apply csSup_le (initialInterval_image_nonempty f hax)
  rintro _ ⟨t, ht, rfl⟩
  by_cases ht₀ : t ≤ x₀
  · exact (le_initialIntervalSup f (hlocal x₀ hax₀) ⟨ht.1, ht₀⟩).trans
      (le_max_left _ _)
  · calc
      f t ≤ θ * initialIntervalSup f a t + E :=
        hcontract t (lt_of_not_ge ht₀).le
      _ ≤ θ * initialIntervalSup f a x + E :=
        add_le_add (mul_le_mul_of_nonneg_left
          (initialIntervalSup_mono f ht.1 ht.2 (hlocal x hax)) hθ₀) (le_refl E)
      _ ≤ max (initialIntervalSup f a x₀) (θ * initialIntervalSup f a x + E) :=
        le_max_right _ _

theorem le_initialIntervalSup_contraction_bound (f : ℝ → ℝ) (a x₀ θ E : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x))
    (hax₀ : a ≤ x₀) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hcontract : ∀ x, x₀ ≤ x → f x ≤ θ * initialIntervalSup f a x + E)
    {x : ℝ} (hax : a ≤ x) :
    f x ≤ max (initialIntervalSup f a x₀) (E / (1 - θ)) :=
  (le_initialIntervalSup f (hlocal x hax) ⟨hax, le_rfl⟩).trans
    (initialIntervalSup_le_of_contraction f a x₀ θ E hlocal hax₀ hθ₀ hθ₁
      hcontract hax)

/-- An eventual contraction supplies a threshold and the same explicit bound
on the entire half-line, including points before the threshold.-/
theorem exists_initialIntervalSup_bound_of_eventually_contraction
    (f : ℝ → ℝ) (a θ E : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hcontract : ∀ᶠ x : ℝ in atTop, f x ≤ θ * initialIntervalSup f a x + E) :
    ∃ x₀, a ≤ x₀ ∧ ∀ x, a ≤ x →
      f x ≤ max (initialIntervalSup f a x₀) (E / (1 - θ)) ∧
      initialIntervalSup f a x ≤ max (initialIntervalSup f a x₀) (E / (1 - θ)) := by
  obtain ⟨b, hb⟩ := eventually_atTop.mp hcontract
  let x₀ := max a b
  have hax₀ : a ≤ x₀ := le_max_left _ _
  have hc : ∀ x, x₀ ≤ x → f x ≤ θ * initialIntervalSup f a x + E := by
    intro x hx
    exact hb x ((le_max_right a b).trans hx)
  refine ⟨x₀, hax₀, fun x hx => ⟨?_, ?_⟩⟩
  · exact le_initialIntervalSup_contraction_bound f a x₀ θ E hlocal hax₀ hθ₀ hθ₁ hc hx
  · exact initialIntervalSup_le_of_contraction f a x₀ θ E hlocal hax₀ hθ₀ hθ₁ hc hx

/-- Generic signed functions are bounded above; no lower bound on `f` is inferred.-/
theorem bddAbove_of_eventually_initialIntervalSup_contraction
    (f : ℝ → ℝ) (a θ E : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hcontract : ∀ᶠ x : ℝ in atTop, f x ≤ θ * initialIntervalSup f a x + E) :
    BddAbove (f '' Ici a) ∧ BddAbove ((initialIntervalSup f a) '' Ici a) := by
  obtain ⟨x₀, _, hbound⟩ :=
    exists_initialIntervalSup_bound_of_eventually_contraction f a θ E hlocal hθ₀ hθ₁ hcontract
  constructor
  · refine ⟨max (initialIntervalSup f a x₀) (E / (1 - θ)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hbound x hx).1
  · refine ⟨max (initialIntervalSup f a x₀) (E / (1 - θ)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hbound x hx).2

/-- In the nonnegative application, the explicit upper bound is also an
absolute-value bound for both the function and its running supremum.-/
theorem abs_le_initialIntervalSup_contraction_bound (f : ℝ → ℝ) (a x₀ θ E : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x))
    (hf : ∀ x, a ≤ x → 0 ≤ f x)
    (hax₀ : a ≤ x₀) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hcontract : ∀ x, x₀ ≤ x → f x ≤ θ * initialIntervalSup f a x + E)
    {x : ℝ} (hax : a ≤ x) :
    |f x| ≤ max (initialIntervalSup f a x₀) (E / (1 - θ)) ∧
    |initialIntervalSup f a x| ≤ max (initialIntervalSup f a x₀) (E / (1 - θ)) := by
  rw [abs_of_nonneg (hf x hax),
    abs_of_nonneg (initialIntervalSup_nonneg f hax (hlocal x hax) (hf a le_rfl))]
  exact ⟨le_initialIntervalSup_contraction_bound f a x₀ θ E hlocal hax₀ hθ₀ hθ₁
    hcontract hax,
    initialIntervalSup_le_of_contraction f a x₀ θ E hlocal hax₀ hθ₀ hθ₁ hcontract hax⟩

/-- Eventual contraction produces a nonnegative absolute bound when `f` is
nonnegative on the half-line.-/
theorem exists_abs_bound_of_eventually_initialIntervalSup_contraction
    (f : ℝ → ℝ) (a θ E : ℝ)
    (hlocal : ∀ x, a ≤ x → BddAbove (f '' Icc a x))
    (hf : ∀ x, a ≤ x → 0 ≤ f x)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hcontract : ∀ᶠ x : ℝ in atTop, f x ≤ θ * initialIntervalSup f a x + E) :
    ∃ C, 0 ≤ C ∧ ∀ x, a ≤ x → |f x| ≤ C ∧ |initialIntervalSup f a x| ≤ C := by
  obtain ⟨x₀, _, hbound⟩ :=
    exists_initialIntervalSup_bound_of_eventually_contraction f a θ E hlocal hθ₀ hθ₁ hcontract
  refine ⟨max (initialIntervalSup f a x₀) (E / (1 - θ)),
    (hf a le_rfl).trans (hbound a le_rfl).1, ?_⟩
  intro x hx
  rw [abs_of_nonneg (hf x hx),
    abs_of_nonneg (initialIntervalSup_nonneg f hx (hlocal x hx) (hf a le_rfl))]
  exact hbound x hx

end TwinPrime.Analytic
