module
public import Tengoku.Seed.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Tengoku.Seed.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Tengoku.Seed.GroupTheory.QuotientGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cardinality bounds for isotropic subgroups

Let `G` be a finite abelian group and `pair : G →+ G →+ AddCircle (1 : ℝ)` a bilinear pairing
which is nondegenerate in the left variable. If `H ≤ G` is isotropic for `pair`
(i.e. `pair a b = 0` for all `a, b ∈ H`), then `|H|^2 ≤ |G|`.

The proof is the standard character-theoretic argument: each `a ∈ H` defines a character
`b ↦ exp(2π i · pair a b)` that is trivial on `H`, hence factors through `G ⧸ H`. Injectivity of
`a ↦ χ_a` yields `|H| ≤ |G ⧸ H|`, and then `|G| = |H| · |G ⧸ H|`.

## Main statements
* `FinitePairing.card_isotropic_sq_le`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

namespace FinitePairing

variable {G : Type*} [AddCommGroup G] [Fintype G]

namespace AddCharCircle

noncomputable instance instFintype [Finite G] : Fintype (AddChar G Circle) :=
  Fintype.ofEquiv (AddChar G ℂ) (AddChar.circleEquivComplex (α := G)).symm

@[simp]
lemma card_eq : Fintype.card (AddChar G Circle) = Fintype.card G := by
  -- reduce to the complex case, where `AddChar.card_eq` is already proved in mathlib
  simpa using
    (Fintype.card_congr (AddChar.circleEquivComplex (α := G))).trans (AddChar.card_eq (α := G))

end AddCharCircle

-- We frequently use `Fintype.card` on subgroups and quotients of a finite group; provide
-- noncomputable `Fintype` instances without requiring decidable membership predicates.

/-- A subgroup of a finite additive commutative group is finite.-/
public noncomputable instance instFiniteSubgroup {G : Type*} [AddCommGroup G] [Finite G]
    (H : AddSubgroup G) :
    Finite (↥H) :=
  Finite.of_injective (fun x : (↥H) => (x : G)) Subtype.val_injective

/-- A subgroup of a finite additive commutative group inherits a `Fintype` structure.-/
public noncomputable instance instFintypeSubgroup (H : AddSubgroup G) : Fintype (↥H) :=
  Fintype.ofFinite (↥H)

noncomputable instance instFintypeCharsTrivial (H : AddSubgroup G) :
    Fintype { χ : AddChar G Circle // ∀ h : H, χ h = 1 } :=
  Fintype.ofFinite _

lemma toCircle_injective : Function.Injective (AddCircle.toCircle : 𝕋 → Circle) :=
  AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero

lemma toCircle_eq_one_iff (x : 𝕋) : AddCircle.toCircle x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply toCircle_injective
    simpa [AddCircle.toCircle_zero] using hx
  · rintro rfl
    simp [AddCircle.toCircle_zero]

variable (pair : G →+ G →+ 𝕋)

end FinitePairing

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
