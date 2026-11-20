/-! Every root-level name of this module is one Lean generates: none is spelled where it is declared. tengoku-leakscan reports each as `root-instance:` or `root-syntax:`
(expected/Generated.txt) and the roots guard lets the module through. -/
namespace Fixture
structure Foo where
  n : Nat
class Marked (α : Type) where
  mark : α
class Small (n : Nat) : Prop where
  ok : True
/-- a reducible abbreviation of a class, and one that is a `∀` into a class (`IsNoetherianRing R`, `CategoryTheory.HasExt C`): an anonymous `local instance` of either has a generated name too -/
abbrev SmallAlias (n : Nat) : Prop := Small n
abbrev AllSmall : Prop := ∀ n : Nat, Small n
end Fixture

open Fixture

local instance : Inhabited Foo := ⟨⟨0⟩⟩
local instance : Small 0 := ⟨trivial⟩
local instance : SmallAlias 1 := ⟨trivial⟩
local instance : AllSmall := fun _ => ⟨trivial⟩
instance : Marked Nat := ⟨0⟩
deriving instance Repr for Foo
notation "fixtureℝ²" => (2 : Nat)
infixl:65 " +fixture+ " => Nat.add
macro "fixture_tac" : tactic => `(tactic| rfl)
