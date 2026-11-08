module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.PhysicalKnowledge.Event
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Inference.PhysicalKnowledge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Countermodel to Wolpert 2018 Corollary 25

The four-state observer from the Definition 11 example knows the event that its
target bit is true. Its unique correct selector uses both setup blocks, so the
union in equation (11) is the entire universe. Neither setup block has a
constantly-true conclusion, and therefore the observer cannot physically know
the characteristic function of that whole-universe event.

This refutes positive introspection under the natural extension to a
singleton-image target. Under the paper's standing two-valued-function
convention the universal event's characteristic is inadmissible, so Corollary
25 is not even closed under its own construction. Either reading exposes the
same proof error: the original event characteristic and the characteristic of
equation (11)'s union do not agree on the selected blocks.
-/

namespace AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Event

open AISafetyAtlas.Inference
open AISafetyAtlas.Examples.Inference.PhysicalKnowledge

private theorem indicator_trueWorlds :
    eventIndicator trueWorlds = target := by
  funext u
  classical
  simp [eventIndicator, trueWorlds, target]

/-- The original source-faithful certificate, transported only across the
definitional equality between the event characteristic and the target bit.-/
public noncomputable def knowsEventWitness :
    PhysicalKnowledgeWitness observer (eventIndicator trueWorlds) true trueWorlds := by
  rw [indicator_trueWorlds]
  exact knowsTrueWitness

private theorem knowsEventWitness_selector_setup
    (g : ImageValue (eventIndicator trueWorlds)) :
    (knowsEventWitness.selector g).1 = g.1 := by
  let x : Bool := (knowsEventWitness.selector g).1
  let u : Bool × Bool := (x, g.1)
  have huX : observer.setup u = (knowsEventWitness.selector g).1 := by rfl
  have hc := knowsEventWitness.correct g u huX
  have htarget : eventIndicator trueWorlds u = g.1 := by
    cases hg : g.1 <;> simp [eventIndicator, trueWorlds, target, u, hg]
  have htrue : observer.concl u = true := hc.mpr htarget
  have heq : g.1 = x := by simpa [observer, u, x] using htrue
  exact heq.symm

end AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Event
