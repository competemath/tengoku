/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.SymmetricAlgebra.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded maps out of the symmetric algebra

For a graded `R`-algebra `A = ⨁ₙ Aₙ` and an `R`-linear map `g : M → A₁`, the lift
`Sym_R M → A` of `g` is a graded ring map (`SymmetricAlgebra.gradedLift`): it sends
`Symⁿ M = ι(M)ⁿ` into `Aⁿ` since `A₁ⁿ ⊆ Aₙ`. This is the surjection `Sym(I) → ⨁ₙ Iⁿ` of the
symmetric algebra of an ideal onto its Rees algebra, which embeds a blow-up in a projective bundle
[Sta, Tag 02NS].
-/

@[expose] public section

universe u

namespace SymmetricAlgebra

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {A : Type u} [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- **The graded lift** `Sym_R M → A` of an `R`-linear map `g : M → A` into degree one.-/
noncomputable def gradedLift (g : M →ₗ[R] A) (hg : ∀ x, g x ∈ 𝒜 1) : grading R M →+*ᵍ 𝒜 where
  toRingHom := (lift g).toRingHom
  map_mem {n x} hx := by
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      change lift g (algebraMap R _ r) ∈ 𝒜 0
      rw [AlgHom.commutes]
      exact SetLike.algebraMap_mem_graded 𝒜 r
    | add x y i hx hy ihx ihy =>
      change lift g (x + y) ∈ 𝒜 i
      rw [map_add]
      exact add_mem ihx ihy
    | mem_mul m hm i x hx ih =>
      obtain ⟨m, rfl⟩ := hm
      change lift g (ι R M m * x) ∈ 𝒜 (i + 1)
      rw [map_mul, lift_ι_apply, add_comm]
      exact SetLike.mul_mem_graded (hg m) ih

/--
@isnad1 id=eq.1h6v.s11.536a1f61afb1 from=translated src=- shape=92a65bec vocab=26d0e52f
-/
theorem gradedLift_apply (g : M →ₗ[R] A) (hg : ∀ x, g x ∈ 𝒜 1) (a : SymmetricAlgebra R M) :
    gradedLift 𝒜 g hg a = lift g a :=
  rfl

end SymmetricAlgebra
