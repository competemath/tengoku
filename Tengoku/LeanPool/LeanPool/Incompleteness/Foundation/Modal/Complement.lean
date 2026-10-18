/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Subformulas

/-! # Complement -/

@[expose] public section
open scoped LO.Axioms LO.Dia LO.Entailment


namespace LO
namespace Modal

namespace Formula

/-- Imported declaration from the Incompleteness formalization. -/
def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:80 "-" => complement

namespace complement

variable {φ ψ : Formula α}

/--
@isnad1 id=eq.0h2v.s4.41ea8c51ed98 from=translated src=- shape=0451be1e vocab=6562d3b4
-/
@[simp] lemma neg_def : -(∼φ) = φ := by induction φ using Formula.rec' <;> simp_all [complement]

/--
@isnad1 id=eq.0h1v.s5.e5dce49f151e from=translated src=- shape=7d367327 vocab=7dbca62c
-/
@[simp] lemma bot_def : -(⊥ : Formula α) = ∼(⊥) := by simp only [complement]

/--
@isnad1 id=eq.0h2v.s5.b8f272c1afd7 from=translated src=- shape=a93a2b79 vocab=c4f083fb
-/
@[simp] lemma box_def : -(□φ) = ∼(□φ) := by simp only [complement]

/--
@isnad1 id=eq.1h3v.s6.575910d3a748 from=translated src=- shape=15506413 vocab=1cd3b74d
-/
lemma imp_def₁ (hq : ψ ≠ ⊥) : -(φ ==> ψ) = ∼(φ ==> ψ) := by
  simp only [complement];
  split;
  · rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  · rfl;

/--
@isnad1 id=eq.1h3v.s5.63d60d245ed4 from=translated src=- shape=4d7bc5e9 vocab=45af79a8
-/
lemma imp_def₂ (hq : ψ = ⊥) : -(φ ==> ψ) = φ := by
  subst_vars;
  apply neg_def;

/--
@isnad1 id=eq.1h3v.s5.4230b5c22cfb from=translated src=- shape=f680f909 vocab=c4f083fb
-/
lemma resort_box (h : -φ = □ψ) : φ = ∼□ψ := by
  simp [complement] at h;
  split at h;
  · subst_vars; rfl;
  · contradiction;

/--
@isnad1 id=or.0h2v.s5.961290481f54 from=translated src=- shape=aed5a055 vocab=6562d3b4
-/
lemma or (φ : Formula α) : -φ = ∼φ ∨ ∃ ψ, ∼ψ = φ := by
  classical
  induction φ using Formula.casesNeg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | hfalsum => simp;
  | hneg => simp;
  | hatom a => simp [complement];
  | hbox φ => simp [complement]

end complement

end Formula
open scoped LO.Modal.Formula

namespace FormulaFinset

variable [DecidableEq α]

/-- Imported declaration from the Incompleteness formalization. -/
def complementary (P : FormulaFinset α) : FormulaFinset α := P ∪ (P.image (Formula.complement))
/-- Imported declaration from the Incompleteness formalization. -/
scoped postfix:80 "⁻" => complementary

variable {P P₁ P₂ : FormulaFinset α} {φ ψ χ : Formula α}

/--
@isnad1 id=mem.1h3v.s6.edbd2d928f9a from=translated src=- shape=17be6bec vocab=6f14b8a4
-/
lemma complementary_mem (h : φ ∈ P) : φ ∈ P⁻ := by simp_all [complementary];

/--
@isnad1 id=mem.1h3v.s6.86ab0256feea from=translated src=- shape=20288ad0 vocab=59e88b80
-/
lemma complementary_comp (h : φ ∈ P) : -φ ∈ P⁻ := by simp [complementary]; tauto;

/--
@isnad1 id=or.1h3v.s6.8c5424eecc95 from=translated src=- shape=b98f19c9 vocab=59e88b80
-/
lemma mem_of (h : φ ∈ P⁻) : φ ∈ P ∨ ∃ ψ ∈ P, -ψ = φ := by simpa [complementary] using h;

/--
@isnad1 id=mem.1h4v.s7.2502a30209ec from=translated src=- shape=7a934b76 vocab=31ff32d2
-/
lemma complementary_mem_box (hi : ∀ {ψ χ}, ψ ==> χ ∈ P → ψ ∈ P := by trivial) :
    □φ ∈ P⁻ → □φ ∈ P := by
  intro h;
  rcases (mem_of h) with (h | ⟨ψ, hq, eq⟩);
  · assumption;
  · replace eq := Formula.complement.resort_box eq;
    subst eq;
    exact hi hq;

/-- Imported declaration from the Incompleteness formalization. -/
class ComplementaryClosed (P : FormulaFinset α) (S : FormulaFinset α) : Prop where
  subset : P ⊆ S⁻
  either : ∀ φ ∈ S, φ ∈ P ∨ -φ ∈ P

/-- Imported declaration from the Incompleteness formalization. -/
def SubformulaeComplementaryClosed (P : FormulaFinset α) (φ : Formula α) :
    Prop :=
  P.ComplementaryClosed φ.subformulas

end FormulaFinset

section «lp_section_1»

variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S} [Entailment.ModusPonens 𝓢]

/--
@isnad1 id=provable.2h4v.s5.c307443ea394 from=translated src=- shape=c4a4340d vocab=27075ecc
-/
lemma complement_derive_bot (hp : 𝓢 ⊢! φ) (hcp : 𝓢 ⊢! -φ) : 𝓢 ⊢! ⊥ := by
  classical
  induction φ using Formula.casesNeg with
  | hfalsum => assumption
  | hatom a | hbox φ => unfold Formula.complement at hcp; exact hcp ⨀ hp
  | hneg => unfold Formula.complement at hcp; exact hp ⨀ hcp
  | himp φ ψ h => simp only [Formula.complement.imp_def₁ h] at hcp; exact hcp ⨀ hp

/--
@isnad1 id=provable.2h4v.s6.9997658acf28 from=translated src=- shape=64212dd0 vocab=bf643be5
-/
lemma neg_complement_derive_bot (hp : 𝓢 ⊢! ∼φ) (hcp : 𝓢 ⊢! ∼(-φ)) : 𝓢 ⊢! ⊥ := by
  classical
  induction φ using Formula.casesNeg with
  | hfalsum | hatom a | hbox φ => unfold Formula.complement at hcp; exact hcp ⨀ hp
  | hneg => unfold Formula.complement at hcp; exact hp ⨀ hcp
  | himp φ ψ h => simp only [Formula.complement.imp_def₁ h] at hcp; exact hcp ⨀ hp

end «lp_section_1»

end Modal
end LO
-- Tengoku: 2 notation(s) of this module made scoped so they do not change other libraries (generated)
