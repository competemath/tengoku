import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.WordConsumption

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace CriticalGK2.Automaton

def afterConsume {R : Type*} [Zero R] (p w : List Bool) (f : List Bool → R) : R :=
  match consumePrefix p w with
  | none => 0
  | some t => f t

/--
@isnad1 id=eq.0h3v.s4.868de0785e98 from=translated src=- shape=5806b6a0 vocab=9c05a816
-/
@[simp]
theorem afterConsume_nil {R : Type*} [Zero R] (w : List Bool) (f : List Bool → R) :
    afterConsume [] w f = f w := rfl

/--
@isnad1 id=eq.1h5v.s5.50eb63fcf79e from=translated src=- shape=d309397c vocab=0c76e242
-/
theorem afterConsume_of_some {R : Type*} [Zero R] (p w t : List Bool)
    (h : consumePrefix p w = some t) (f : List Bool → R) :
    afterConsume p w f = f t := by simp [afterConsume, h]

/--
@isnad1 id=eq.1h4v.s5.7854b4b05daf from=translated src=- shape=398c4efd vocab=5776a1c6
-/
theorem afterConsume_of_none {R : Type*} [Zero R] (p w : List Bool)
    (h : consumePrefix p w = none) (f : List Bool → R) :
    afterConsume p w f = 0 := by simp [afterConsume, h]

end CriticalGK2.Automaton
