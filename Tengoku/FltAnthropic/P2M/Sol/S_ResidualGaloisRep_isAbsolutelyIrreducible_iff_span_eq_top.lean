import Tengoku.FltAnthropic.Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Tengoku.FltAnthropic.Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_ResidualEquiv
import Tengoku.Seed.RepresentationTheory.Irreducible
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.Algebra.Algebra.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top

open Module LinearMap
open scoped TensorProduct

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace C6P1R

section Bridges
variable {k : Type} [Field k]

/--
@isnad1 id=iff.0h2v.s8.c4db6ed57e4e from=translated src=- shape=06715a46 vocab=4be7d328
-/
theorem isIrreducible_iff_rep (ρ : ResidualGaloisRep k) : ρ.IsIrreducible ↔ Representation.IsIrreducible ρ.ρ := by
  haveI : Nontrivial ρ.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρ.finrank_eq]; norm_num)
  have hne : (⊥ : Subrepresentation ρ.ρ) ≠ ⊤ := fun h =>
    bot_ne_top (α := Submodule k ρ.V) (congrArg Subrepresentation.toSubmodule h)
  constructor
  · intro h
    refine { toNontrivial := ⟨⟨⊥, ⊤, hne⟩⟩, eq_bot_or_eq_top := fun W => ?_ }
    rcases h W.toSubmodule (fun σ x hx => W.apply_mem_toSubmodule σ hx) with h0 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h0)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  · intro h W hW
    rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

/--
@isnad1 id=isirredu.1h2v.s10.30f686200e67 from=translated src=- shape=5484c860 vocab=9e8b0840
-/
theorem isIrreducible_of_span_eq_top (ρ : ResidualGaloisRep k) (h : Submodule.span k (Set.range ⇑ρ.ρ) = ⊤) :
    ρ.IsIrreducible := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot

  have hstab : ∀ f : Module.End k ρ.V, ∀ x ∈ W, f x ∈ W := by
    intro f
    have hf : f ∈ Submodule.span k (Set.range ⇑ρ.ρ) := by rw [h]; trivial
    refine Submodule.span_induction (p := fun f _ => ∀ x ∈ W, f x ∈ W) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨σ, rfl⟩ x hx; exact hW σ x hx
    · intro x _; exact W.zero_mem
    · intro f g _ _ hf hg x hx; exact W.add_mem (hf x hx) (hg x hx)
    · intro c f _ hf x hx; exact W.smul_mem c (hf x hx)
  rw [eq_top_iff]
  intro w _

  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hv0
  have h1 : (φ v) • w ∈ W := hstab (φ.smulRight w) v hvW
  have h2 := W.smul_mem (φ v)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hφ, one_smul] at h2

/--
@isnad1 id=eq.0h3v.s11.61835b770005 from=translated src=- shape=6c50b0a5 vocab=f98f2f89
-/
theorem range_baseChange_ρ (K : Type) [Field K] [Algebra k K] (ρ : ResidualGaloisRep k) :
    Set.range ⇑(ρ.baseChange K).ρ = Set.range fun σ => (ρ.ρ σ).baseChange K := rfl

end Bridges

end C6P1R

open C6P1R in
/--
@isnad1 id=iff.0h2v.s10.2374a8e7815b from=translated src=- shape=5561cae7 vocab=1a1340e1
-/
theorem solution
    {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsAbsolutelyIrreducible ↔ Submodule.span k (Set.range ⇑ρ.ρ) = ⊤ := by
  constructor
  · intro h
    have h1 : Representation.IsIrreducible (ρ.baseChange (AlgebraicClosure k)).ρ := (isIrreducible_iff_rep _).mp h
    have h2 := Representation.span_range_eq_top_of_isIrreducible (ρ.baseChange (AlgebraicClosure k)).ρ
    rw [range_baseChange_ρ] at h2
    exact (Representation.span_range_baseChange_eq_top_iff (K := AlgebraicClosure k) ρ.ρ).mp h2
  · intro h
    have h2 := (Representation.span_range_baseChange_eq_top_iff (K := AlgebraicClosure k) ρ.ρ).mpr h
    exact isIrreducible_of_span_eq_top _ (by rw [range_baseChange_ρ]; exact h2)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
