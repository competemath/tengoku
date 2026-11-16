import Tengoku.Seed.NumberTheory.Cyclotomic.CyclotomicCharacter
import Tengoku.Seed.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/--
@isnad1 id=eq.0h2v.s7.3cb3e66115bd from=translated src=- shape=85f21da0 vocab=7ed7ae67
-/
theorem IsAlgClosed.card_rootsOfUnity_eq (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n K) = n :=
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  HasEnoughRootsOfUnity.natCard_rootsOfUnity K n

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]

/--
@isnad1 id=eq.0h1v.s7.ce807ede16d2 from=translated src=- shape=cc1137d4 vocab=c68a4fb1
-/
theorem card_rootsOfUnity_eq_self :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Nat.card (rootsOfUnity p (AlgebraicClosure ℚ)) = p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) p

noncomputable def cycloExp (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ℕ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ((modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p).val

variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

structure IsAdmissibleExtension (C : Submodule (ZMod p) V) : Prop where
  stable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C, σ • x ∈ C
  fixed_sub : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C, σ • x = x
  cyclo_quot : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x : V,
    σ • x - (cycloExp p σ : ZMod p) • x ∈ C
  card_sub : Nat.card C = p
  card_total : Nat.card V = p ^ 2
  unramified_outside : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : V, σ • x = x
  locally_split : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ C' : Submodule (ZMod p) V,
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ C', σ • x ∈ C') ∧ IsCompl C C'

variable {p V} in

def SplitsGlobally (C : Submodule (ZMod p) V) : Prop :=
  ∃ C' : Submodule (ZMod p) V,
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C', σ • x ∈ C') ∧ IsCompl C C'

def ExtVanishing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V),
    IsAdmissibleExtension p V C → SplitsGlobally C

def ExtVanishingAll : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → @ExtVanishing p ⟨hp⟩

end ExtCitation
