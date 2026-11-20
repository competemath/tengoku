import Tengoku.Lmlf.LMLF.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Foundational quantitative predicates

Finite pointwise error and norm bounds, together with their basic transport rules.
-/

namespace QuantitativeAnalysis

variable {X Y E : Type*} [NormedAddCommGroup E]

/-- `ErrorOn D f a b` means that `a` approximates `f` with pointwise error at most `b` on `D`.-/
def ErrorOn (D : Set X) (f a : X → E) (b : X → ℝ) : Prop :=
  ∀ x ∈ D, ‖f x - a x‖ ≤ b x

/-- `NormBoundOn D f b` means that the norm of `f` is pointwise at most `b` on `D`.-/
def NormBoundOn (D : Set X) (f : X → E) (b : X → ℝ) : Prop :=
  ∀ x ∈ D, ‖f x‖ ≤ b x

/-- A family of finite pointwise error estimates for one fixed target function.-/
def HasErrorFamily
    (f : X → E) (a : ℕ → X → E)
    (D : ℕ → Set X) (b : ℕ → X → ℝ) : Prop :=
  ∀ n, ErrorOn (D n) f (a n) (b n)

namespace ErrorOn

/-- Functions equal on a domain have zero error there.-/
theorem exact {D : Set X} {f a : X → E} (h : Set.EqOn f a D) :
    ErrorOn D f a (fun _ ↦ 0) := by
  intro x hx
  simpa only [h hx, sub_self, norm_zero] using (le_refl (0 : ℝ))

/-- An error bound restricts to a smaller domain.-/
theorem restrict {D D' : Set X} {f a : X → E} {b : X → ℝ}
    (h : ErrorOn D f a b) (hD : D' ⊆ D) :
    ErrorOn D' f a b := by
  intro x hx
  exact h x (hD hx)

/-- An error bound remains valid after pointwise enlargement of its majorant.-/
theorem weaken {D : Set X} {f a : X → E} {b d : X → ℝ}
    (h : ErrorOn D f a b) (hbd : ∀ x ∈ D, b x ≤ d x) :
    ErrorOn D f a d := by
  intro x hx
  exact (h x hx).trans (hbd x hx)

/-- Successive error bounds compose with the sum of their majorants.-/
theorem trans {D : Set X} {f a c : X → E} {b d : X → ℝ}
    (hfa : ErrorOn D f a b) (hac : ErrorOn D a c d) :
    ErrorOn D f c (fun x ↦ b x + d x) := by
  intro x hx
  calc
    ‖f x - c x‖ = ‖(f x - a x) + (a x - c x)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖f x - a x‖ + ‖a x - c x‖ := norm_add_le _ _
    _ ≤ b x + d x := add_le_add (hfa x hx) (hac x hx)

/-- An error bound pulls back along a map into its original domain.-/
theorem comp {D : Set X} {f a : X → E} {b : X → ℝ}
    (h : ErrorOn D f a b) {S : Set Y} (ψ : Y → X)
    (hψ : Set.MapsTo ψ S D) :
    ErrorOn S (f ∘ ψ) (a ∘ ψ) (b ∘ ψ) := by
  intro y hy
  exact h (ψ y) (hψ hy)

end ErrorOn
end QuantitativeAnalysis
