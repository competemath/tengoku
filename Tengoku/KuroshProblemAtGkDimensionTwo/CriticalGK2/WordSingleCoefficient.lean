import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.WordConsumption

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace CriticalGK2.Automaton

def afterConsume {R : Type*} [Zero R] (p w : List Bool) (f : List Bool → R) : R :=
  match consumePrefix p w with
  | none => 0
  | some t => f t

@[simp]
theorem afterConsume_nil {R : Type*} [Zero R] (w : List Bool) (f : List Bool → R) :
    afterConsume [] w f = f w := rfl

theorem afterConsume_of_some {R : Type*} [Zero R] (p w t : List Bool)
    (h : consumePrefix p w = some t) (f : List Bool → R) :
    afterConsume p w f = f t := by simp [afterConsume, h]

theorem afterConsume_of_none {R : Type*} [Zero R] (p w : List Bool)
    (h : consumePrefix p w = none) (f : List Bool → R) :
    afterConsume p w f = 0 := by simp [afterConsume, h]

end CriticalGK2.Automaton
