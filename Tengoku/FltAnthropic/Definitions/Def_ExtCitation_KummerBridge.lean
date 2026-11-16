import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_AdmissibleExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace groupCohomology

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [DistribMulAction Γ V] [SMulCommClass Γ R V]

def extClassFun (χ : Γ →* Rˣ) (v₀ : V) (σ : Γ) : V :=
  (((χ σ)⁻¹ : Rˣ) : R) • (σ • v₀ - (χ σ : R) • v₀)

omit [SMulCommClass Γ R V] in

/--
@isnad1 id=mem.1h7v.s8.a1caa022698d from=translated src=- shape=580fab94 vocab=1b846647
-/
lemma extClassFun_mem (χ : Γ →* Rˣ) (v₀ : V) (C : Submodule R V)
    (hquot : ∀ σ : Γ, ∀ x : V, σ • x - (χ σ : R) • x ∈ C) (σ : Γ) :
    extClassFun χ v₀ σ ∈ C :=
  C.smul_mem _ (hquot σ v₀)

end groupCohomology

namespace ExtCitation

variable (p : ℕ) [Fact p.Prime]

noncomputable def cycloChar :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod p)ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  MonoidHom.mk'
    (fun σ => modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (fun a b => by rw [← map_mul]; congr 1)

/--
@isnad1 id=eq.0h2v.s10.2b7e97b438ef from=translated src=- shape=224ffaab vocab=f3aed9e6
-/
lemma val_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p) : ZMod p).val = cycloExp p σ := rfl

/--
@isnad1 id=eq.0h2v.s10.4027fc41b168 from=translated src=- shape=dbbb0668 vocab=7ff69ebf
-/
lemma coe_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p)) = (cycloExp p σ : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← val_cycloChar, ZMod.natCast_val, ZMod.cast_id]

end ExtCitation
