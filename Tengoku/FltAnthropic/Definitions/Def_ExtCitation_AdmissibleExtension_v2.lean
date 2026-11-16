import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_AdmissibleExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]
variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

structure IsAdmissibleExtensionCts (C : Submodule (ZMod p) V) : Prop
    extends IsAdmissibleExtension p V C where

  open_kernel : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | ∀ v : V, σ • v = v}

def ExtVanishingCts : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V),
    IsAdmissibleExtensionCts p V C → SplitsGlobally C

def ExtVanishingCtsAll : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → @ExtVanishingCts p ⟨hp⟩

variable {p V} in

/--
@isnad1 id=extvanis.1h1v.s3.ad364f415812 from=translated src=- shape=37c76ab3 vocab=6ea08af8
-/
theorem extVanishingCts_of_extVanishing (h : ExtVanishing p) : ExtVanishingCts p :=
  fun V _ _ _ _ C hadm => h V C hadm.toIsAdmissibleExtension

end ExtCitation
