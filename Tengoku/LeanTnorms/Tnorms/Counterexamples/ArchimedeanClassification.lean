import Tengoku
import Tengoku.LeanTnorms.Tnorms.Basic.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Counterexample to show that the typeclasses in the equivalence between Strict and not Nilpotent
  can't be weakened much.  In particular, that a LinearOrder seems necessary.
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
local infixl:60 " ⇒ " => LImp

inductive _root_.Tengoku.LeanTnorms.DoubleInterval where
  | bot
  | top
  | left (a : Set.Ioo (0 : ℝ) 1)
  | right (b : Set.Ioo (0 : ℝ) 1)

abbrev _root_.Tengoku.LeanTnorms.doubleInterval_le : DoubleInterval → DoubleInterval → Prop
  | .bot, _ => True
  | _, .top => True
  | .top, .bot => False
  | .top, .left _ => False
  | .top, .right _ => False
  | .left a, .left b => a ≤ b
  | .left a, .right b => a ≤ b.1 / 2
  | .left _, .bot => False
  | .right a, .left b => a ≤ b.1 / 2
  | .right a , .right b => a ≤ b
  | .right _, .bot => False

instance : LE DoubleInterval := ⟨doubleInterval_le⟩

@[simp, grind =]
lemma _root_.Tengoku.LeanTnorms.doubleInterval_le_def (a b : DoubleInterval) : (a ≤ b) = doubleInterval_le a b := rfl

instance : BoundedOrder DoubleInterval where
  bot := .bot
  top := .top
  bot_le a := by grind
  le_top a := by grind

instance : PartialOrder DoubleInterval where
  le_refl a := by grind
  le_antisymm a b := by grind
  le_trans a b c := by
    cases a <;> cases b <;> cases c
    all_goals simp [doubleInterval_le, ← Subtype.coe_le_coe]; try grind

  -- [TopologicalSpace M] [CommMonoidWithZero M]
  -- [LinearOrder M]
  -- [MulArchimedeanDualWithZero M] [IsOrderedMonoid M] [IsTopOneClass M]
  -- [NontrivialZeroOne M] [ContinuousMul M]
  -- [OrderTopology M] [PreconnectedSpace M]
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
