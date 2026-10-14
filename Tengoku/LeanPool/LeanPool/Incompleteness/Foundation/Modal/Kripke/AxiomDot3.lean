/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic

/-! # AxiomDot3 -/

@[expose] public section

namespace LO
namespace Modal

open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame}

/--
@isnad1 id=realize.1h1v.s5.de37e4f0ba96 from=translated src=- shape=9cf6f3a4 vocab=04a47a29
-/
lemma connected_of_validate_dot3 (hCon : Connected F) : F ⊧ (Axioms.Dot3 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.or_def.mpr;
  suffices
    (∀ y, x ≺ y → (∀ z, y ≺ z → V z 0) → V y 1) ∨
    (∀ y, x ≺ y → (∀ z, y ≺ z → V z 1) → V y 0)
    by simpa [Semantics.Realize, Satisfies];
  by_contra hC;
  push Not at hC;
  obtain ⟨⟨y, Rxy, hp, hnq⟩, ⟨z, Rxz, hq, hnp⟩⟩ := hC;
  cases hCon ⟨Rxy, Rxz⟩ with
  | inl Ryz => have := hp z Ryz; contradiction;
  | inr Rzy => have := hq y Rzy; contradiction;

/--
@isnad1 id=connecte.1h1v.s5.7dca77fb906c from=translated src=- shape=c6ab71fc vocab=04a47a29
-/
lemma validate_dot3_of_connected : F ⊧ (Axioms.Dot3 (.atom 0) (.atom 1)) → Connected F := by
  contrapose;
  intro hCon;
  obtain ⟨x, y, Rxy, z, Ryz, nRyz, nRzy⟩ := by simpa [Connected] using hCon;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (fun w a => match a with | 0 => y ≺ w | 1 => z ≺ w | _ => False), x;
  suffices ∃ y', x ≺ y' ∧ (∀ z', y' ≺ z' → y ≺ z') ∧ ¬z ≺ y' ∧ (∃ z', x ≺ z' ∧ (∀ y, z' ≺ y →
    z ≺ y) ∧ ¬y ≺ z') by
    simpa [Semantics.Realize, Satisfies];
  refine ⟨y, Rxy, by tauto, nRzy, z, Ryz, by tauto, nRyz⟩;

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ConnectedFrameClass : FrameClass := { F | Connected F }

end Kripke

end Modal
end LO
