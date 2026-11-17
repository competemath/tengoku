import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.FieldTheory.Finiteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 800000

/-!
# Finite affine systems over `𝔽₂`

This file formalizes the elementary affine-linear facts used in Paper C.  For a
linear map `A : V →ₗ[𝔽₂] W` and a right-hand side `b : W`, the solution fiber
`{x | A x = b}` is nonempty exactly when `b` belongs to the range of `A`.
After choosing one solution `x₀`, translation by `x₀` identifies that fiber
explicitly with `LinearMap.ker A`.

For finite vector spaces this gives the exact number of solutions:

`|{x | A x = b}| = 2 ^ finrank 𝔽₂ (ker A)`

whenever the system is compatible, and zero otherwise.
-/

namespace PaperC.Affine

/-- The field with two elements.-/
abbrev 𝔽₂ := ZMod 2

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V W : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [AddCommGroup W] [Module 𝔽₂ W]

/-- The set-theoretic fiber of `A` above `b`.-/
def solutionSet (A : V →ₗ[𝔽₂] W) (b : W) : Set V :=
  {x | A x = b}

/-- The type of solutions of the affine system `A x = b`.-/
abbrev Solution (A : V →ₗ[𝔽₂] W) (b : W) :=
  {x : V // x ∈ solutionSet A b}

/-- Compatibility of `A x = b`: the right-hand side lies in the range of `A`.-/
def Compatible (A : V →ₗ[𝔽₂] W) (b : W) : Prop :=
  b ∈ LinearMap.range A

/--
@isnad1 id=iff.0h5v.s7.f65e6e9fd053 from=translated src=- shape=2b43fe6b vocab=23970442
-/
@[simp]
theorem mem_solutionSet_iff (A : V →ₗ[𝔽₂] W) (b : W) (x : V) :
    x ∈ solutionSet A b ↔ A x = b :=
  Iff.rfl

/--
@isnad1 id=eq.0h5v.s8.bf2b720dfdcf from=translated src=- shape=b9b48d5d vocab=f188db18
-/
@[simp]
theorem solution_property (A : V →ₗ[𝔽₂] W) (b : W) (x : Solution A b) :
    A x.1 = b :=
  x.2

/-- A system is compatible exactly when its solution type is nonempty.
@isnad1 id=iff.0h4v.s7.7774d9fb0659 from=translated src=- shape=07400670 vocab=f49991db
-/
theorem compatible_iff_nonempty (A : V →ₗ[𝔽₂] W) (b : W) :
    Compatible A b ↔ Nonempty (Solution A b) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp h
    exact ⟨⟨x, hx⟩⟩
  · rintro ⟨x⟩
    exact LinearMap.mem_range.mpr ⟨x.1, x.2⟩

/-- A system is incompatible exactly when its solution type is empty.
@isnad1 id=iff.0h4v.s7.5b17f9f6d274 from=translated src=- shape=37890967 vocab=34b8d7fa
-/
theorem not_compatible_iff_isEmpty (A : V →ₗ[𝔽₂] W) (b : W) :
    ¬Compatible A b ↔ IsEmpty (Solution A b) := by
  rw [compatible_iff_nonempty, not_nonempty_iff]

/--
Translation by a fixed solution identifies the affine solution fiber with the
linear kernel.  The forward map is `x ↦ x - x₀`; the inverse is
`k ↦ k + x₀`.-/
def solutionEquivKer (A : V →ₗ[𝔽₂] W) (b : W) (x₀ : Solution A b) :
    Solution A b ≃ LinearMap.ker A where
  toFun x :=
    ⟨x.1 - x₀.1, by
      change A (x.1 - x₀.1) = 0
      rw [map_sub, x.2, x₀.2, sub_self]⟩
  invFun k :=
    ⟨k.1 + x₀.1, by
      change A (k.1 + x₀.1) = b
      rw [map_add, k.2, x₀.2, zero_add]⟩
  left_inv x := by
    apply Subtype.ext
    exact sub_add_cancel x.1 x₀.1
  right_inv k := by
    apply Subtype.ext
    exact add_sub_cancel_right k.1 x₀.1

/--
@isnad1 id=eq.0h6v.s9.129c514d1cb0 from=translated src=- shape=55a4820f vocab=f7d2b504
-/
@[simp]
theorem solutionEquivKer_apply_coe
    (A : V →ₗ[𝔽₂] W) (b : W) (x₀ x : Solution A b) :
    ((solutionEquivKer A b x₀ x : LinearMap.ker A) : V) = x.1 - x₀.1 :=
  rfl

/--
@isnad1 id=eq.0h6v.s10.0eaac3ee0a9c from=translated src=- shape=ee6f68fd vocab=3baa7213
-/
@[simp]
theorem solutionEquivKer_symm_apply_coe
    (A : V →ₗ[𝔽₂] W) (b : W) (x₀ : Solution A b) (k : LinearMap.ker A) :
    ((solutionEquivKer A b x₀).symm k).1 = k.1 + x₀.1 :=
  rfl

/--
The canonical (noncomputable) fiber--kernel equivalence obtained from a proof
that the affine system is compatible.-/
noncomputable def solutionEquivKerOfCompatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : Compatible A b) :
    Solution A b ≃ LinearMap.ker A :=
  solutionEquivKer A b (Classical.choice ((compatible_iff_nonempty A b).mp h))

noncomputable section Finite

variable [Fintype V]

local instance solutionFintype (A : V →ₗ[𝔽₂] W) (b : W) :
    Fintype (Solution A b) :=
  Fintype.ofFinite _

local instance kernelFintype (A : V →ₗ[𝔽₂] W) :
    Fintype (LinearMap.ker A) :=
  Fintype.ofFinite _

local instance compatibleDecidable (A : V →ₗ[𝔽₂] W) (b : W) :
    Decidable (Compatible A b) :=
  Classical.propDecidable _

/-- A nonempty affine fiber and the kernel have the same cardinality.
@isnad1 id=eq.0h5v.s8.637be0942fb9 from=translated src=- shape=571bed9c vocab=0abc2988
-/
theorem card_solution_eq_card_ker
    (A : V →ₗ[𝔽₂] W) (b : W) (x₀ : Solution A b) :
    Fintype.card (Solution A b) = Fintype.card (LinearMap.ker A) :=
  Fintype.card_congr (solutionEquivKer A b x₀)

/--
Exact cardinality of a compatible affine system over `𝔽₂`, expressed using
the dimension of its kernel.
@isnad1 id=eq.0h5v.s8.414b5dd4b555 from=translated src=- shape=0b581058 vocab=1a5e9db3
-/
theorem card_solution_eq_pow_finrank
    (A : V →ₗ[𝔽₂] W) (b : W) (x₀ : Solution A b) :
    Fintype.card (Solution A b) =
      2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) := by
  calc
    Fintype.card (Solution A b) =
        Fintype.card (LinearMap.ker A) :=
      card_solution_eq_card_ker A b x₀
    _ = Fintype.card 𝔽₂ ^ Module.finrank 𝔽₂ (LinearMap.ker A) :=
      Module.card_eq_pow_finrank (K := 𝔽₂) (V := LinearMap.ker A)
    _ = 2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) := by
      rw [ZMod.card]

/-- Compatibility alone suffices for the power-of-two cardinality formula.
@isnad1 id=eq.1h4v.s8.0c9da339c499 from=translated src=- shape=9bfc1a39 vocab=ef1c586f
-/
theorem card_solution_eq_pow_finrank_of_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : Compatible A b) :
    Fintype.card (Solution A b) =
      2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) := by
  let x₀ : Solution A b :=
    Classical.choice ((compatible_iff_nonempty A b).mp h)
  exact card_solution_eq_pow_finrank A b x₀

/-- An incompatible affine system has no solutions.
@isnad1 id=eq.1h4v.s7.764406b2fa0f from=translated src=- shape=d0302977 vocab=8aeaa618
-/
theorem card_solution_eq_zero_of_not_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : ¬Compatible A b) :
    Fintype.card (Solution A b) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact (not_compatible_iff_isEmpty A b).mp h

/-- Uniform cardinality formula, covering both compatible and incompatible systems.
@isnad1 id=eq.0h4v.s8.66b8ed72c4d1 from=translated src=- shape=b77e0a98 vocab=ac1174a4
-/
theorem card_solution_eq_ite
    (A : V →ₗ[𝔽₂] W) (b : W) :
    Fintype.card (Solution A b) =
      if Compatible A b then
        2 ^ Module.finrank 𝔽₂ (LinearMap.ker A)
      else
        0 := by
  classical
  by_cases h : Compatible A b
  · rw [ite_eq_left h]
    exact card_solution_eq_pow_finrank_of_compatible A b h
  · rw [ite_eq_right h]
    exact card_solution_eq_zero_of_not_compatible A b h

/-- In particular, every nonempty affine fiber over `𝔽₂` has power-of-two size.
@isnad1 id=ex.1h4v.s7.1314ed031cdc from=translated src=- shape=2be14de0 vocab=083d5ea6
-/
theorem card_solution_is_power_of_two
    (A : V →ₗ[𝔽₂] W) (b : W) (h : Compatible A b) :
    ∃ d : ℕ, Fintype.card (Solution A b) = 2 ^ d :=
  ⟨Module.finrank 𝔽₂ (LinearMap.ker A),
    card_solution_eq_pow_finrank_of_compatible A b h⟩

end Finite

end PaperC.Affine
