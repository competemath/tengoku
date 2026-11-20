/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEAffineTripods
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEArmArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

theorem orientedArms_are_D_or_E
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component) :
    IsDArmTriple A₀.length A₁.length A₂.length ∨
      IsE6ArmTriple A₀.length A₁.length A₂.length ∨
      IsE7ArmTriple A₀.length A₁.length A₂.length ∨
      IsE8ArmTriple A₀.length A₁.length A₂.length := by
  let outcome := three_arm_arithmetic_classification
    A₀.length_pos A₁.length_pos A₂.length_pos
  cases outcome with
  | d01 ha hb => exact Or.inl (Or.inl ⟨ha, hb⟩)
  | d02 ha hc => exact Or.inl (Or.inr (Or.inl ⟨ha, hc⟩))
  | d12 hb hc => exact Or.inl (Or.inr (Or.inr ⟨hb, hc⟩))
  | e6_012 ha hb hc => exact Or.inr (Or.inl (Or.inl ⟨ha, hb, hc⟩))
  | e6_102 hb ha hc => exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hb, ha, hc⟩)))
  | e6_201 hc ha hb => exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hc, ha, hb⟩)))
  | e7_012 ha hb hc => exact Or.inr (Or.inr (Or.inl (Or.inl ⟨ha, hb, hc⟩)))
  | e7_021 ha hc hb => exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨ha, hc, hb⟩))))
  | e7_102 hb ha hc => exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hb, ha, hc⟩)))))
  | e7_120 hb hc ha => exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hc, ha⟩))))))
  | e7_201 hc ha hb => exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, ha, hb⟩)))))))
  | e7_210 hc hb ha => exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, hb, ha⟩)))))))
  | e8_012 ha hb hc => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb, hc⟩)))
  | e8_021 ha hc hb => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hc, hb⟩))))
  | e8_102 hb ha hc => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, ha, hc⟩)))))
  | e8_120 hb hc ha => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hc, ha⟩))))))
  | e8_201 hc ha hb => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, ha, hb⟩)))))))
  | e8_210 hc hb ha => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, hb, ha⟩)))))))
  | affineE6 ha hb hc => exact (not_all_three_arms_length_two
      hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂ ha hb hc).elim
  | affineE7_0 ha hb hc => exact (not_arms_length_one_three_three
      hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂ ha hb hc).elim
  | affineE7_1 hb ha hc => exact (not_arms_length_one_three_three
      hpos hconn A₁ A₀ A₂ h₀₁.symm h₁₂ h₀₂ hb ha hc).elim
  | affineE7_2 hc ha hb => exact (not_arms_length_one_three_three
      hpos hconn A₂ A₀ A₁ h₀₂.symm h₁₂.symm h₀₁ hc ha hb).elim
  | affineE8_012 ha hb hc => exact (not_arms_length_one_two_five
      hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂ ha hb hc).elim
  | affineE8_021 ha hc hb => exact (not_arms_length_one_two_five
      hpos hconn A₀ A₂ A₁ h₀₂ h₀₁ h₁₂.symm ha hc hb).elim
  | affineE8_102 hb ha hc => exact (not_arms_length_one_two_five
      hpos hconn A₁ A₀ A₂ h₀₁.symm h₁₂ h₀₂ hb ha hc).elim
  | affineE8_120 hb hc ha => exact (not_arms_length_one_two_five
      hpos hconn A₁ A₂ A₀ h₁₂ h₀₁.symm h₀₂.symm hb hc ha).elim
  | affineE8_201 hc ha hb => exact (not_arms_length_one_two_five
      hpos hconn A₂ A₀ A₁ h₀₂.symm h₁₂.symm h₀₁ hc ha hb).elim
  | affineE8_210 hc hb ha => exact (not_arms_length_one_two_five
      hpos hconn A₂ A₁ A₀ h₁₂.symm h₀₂.symm h₀₁.symm hc hb ha).elim

end Lattice
end SRG266
