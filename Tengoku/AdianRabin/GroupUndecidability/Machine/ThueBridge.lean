import Tengoku.AdianRabin.GroupUndecidability.Thue.Core
import Tengoku.Seed.Computability.StateTransition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability

namespace MachineThue

/-- Iteration of a deterministic partial transition function.  The zeroth
iterate is the initial configuration; a missing transition at any later stage
records termination.-/
def iterate {C : Type*} (step : C → Option C) : ℕ → C → Option C
  | 0, c => some c
  | n + 1, c => (step c).bind (iterate step n)

/-- A configuration terminates when some finite iterate encounters a missing
transition.-/
def Terminates {C : Type*} (step : C → Option C) (c : C) : Prop :=
  ∃ n, iterate step n c = none

/--
@isnad1 id=terminat.1h3v.s4.057c7db22554 from=translated src=- shape=21ab88a4 vocab=500a8c3f
-/
theorem terminates_of_halted {C : Type*} {step : C → Option C} {c : C}
    (h : step c = none) : Terminates step c :=
  ⟨1, by simp [iterate, h]⟩

/--
@isnad1 id=terminat.2h4v.s4.9c4ae4b2cdd0 from=translated src=- shape=0185fa00 vocab=e23dc9b7
-/
theorem terminates_of_step {C : Type*} {step : C → Option C} {c d : C}
    (hcd : step c = some d) (hd : Terminates step d) : Terminates step c := by
  obtain ⟨n, hn⟩ := hd
  exact ⟨n + 1, by simp [iterate, hcd, hn]⟩

/--
@isnad1 id=terminat.2h4v.s4.6e4bef800fcf from=translated src=- shape=e02252f0 vocab=e23dc9b7
-/
theorem terminates_after_step {C : Type*} {step : C → Option C} {c d : C}
    (hcd : step c = some d) (hc : Terminates step c) : Terminates step d := by
  obtain ⟨n, hn⟩ := hc
  cases n with
  | zero => simp [iterate] at hn
  | succ n =>
      exact ⟨n, by simpa [iterate, hcd] using hn⟩

/--
@isnad1 id=iff.0h3v.s5.cee0d0445a2c from=translated src=- shape=7a7d0f2c vocab=21c99db7
-/
theorem terminates_iff_reaches_halt {C : Type*} {step : C → Option C} {c : C} :
    Terminates step c ↔
      ∃ h, StateTransition.Reaches step c h ∧ step h = none := by
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => simp [iterate] at hn
    | succ n ih =>
        cases hc : step c with
        | none => exact ⟨c, Relation.ReflTransGen.refl, hc⟩
        | some d =>
            have hd : iterate step n d = none := by
              simpa [iterate, hc] using hn
            obtain ⟨h, hdh, hh⟩ := ih hd
            exact ⟨h, Relation.ReflTransGen.head hc hdh, hh⟩
  · rintro ⟨h, hch, hh⟩
    induction hch using Relation.ReflTransGen.head_induction_on with
    | refl => exact terminates_of_halted hh
    | head hcd _ ih => exact terminates_of_step hcd ih

/-- `Terminates` agrees with Mathlib's domain predicate for the standard
state-transition evaluator.
@isnad1 id=iff.0h3v.s4.cb14b04843ca from=translated src=- shape=29ea8500 vocab=8564fc6f
-/
theorem terminates_iff_eval_dom {C : Type*} {step : C → Option C} {c : C} :
    Terminates step c ↔ (StateTransition.eval step c).Dom := by
  rw [terminates_iff_reaches_halt, Part.dom_iff_mem]
  constructor
  · rintro ⟨h, hreach, hhalt⟩
    exact ⟨h, StateTransition.mem_eval.mpr ⟨hreach, hhalt⟩⟩
  · rintro ⟨h, heval⟩
    obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.mp heval
    exact ⟨h, hreach, hhalt⟩

/--
The exact local obligations needed to turn a deterministic partial machine
into a symmetric Thue system with a fixed target.

`classify` is Post's key inverse-simulation lemma.  At a nonterminal encoded
configuration, a symmetric rewrite either performs the unique forward machine
step or reaches an encoded predecessor.  The latter alternative is harmless:
determinism lets us cancel that backwards excursion from any terminating run.-/
structure Coding (C α : Type*) where
  step : C → Option C
  system : ThueSystem α
  encode : C → List α
  target : List α
  target_ne_encode : ∀ c, target ≠ encode c
  simulate_step :
    ∀ {c d}, step c = some d → ThueStep system (encode c) (encode d)
  simulate_halt :
    ∀ {c}, step c = none → ThueEq system (encode c) target
  classify :
    ∀ {c d w}, step c = some d → ThueStep system (encode c) w →
      w = encode d ∨ ∃ p, w = encode p ∧ step p = some c

namespace Coding

variable {C α : Type*} (K : Coding C α)

/--
@isnad1 id=thueeq.1h4v.s5.327f75e5e9e5 from=translated src=- shape=2e672f10 vocab=c0f0d117
-/
theorem simulation {c : C} :
    Terminates K.step c → ThueEq K.system (K.encode c) K.target := by
  rintro ⟨n, hn⟩
  induction n generalizing c with
  | zero => simp [iterate] at hn
  | succ n ih =>
      cases hstep : K.step c with
      | none => exact K.simulate_halt hstep
      | some d =>
          have hd : iterate K.step n d = none := by
            simpa [iterate, hstep] using hn
          exact (Relation.ReflTransGen.single (K.simulate_step hstep)).trans
            (ih hd)

/--
@isnad1 id=terminat.1h4v.s5.595a037267f8 from=translated src=- shape=6d3ce850 vocab=c0f0d117
-/
theorem inverse_simulation {c : C} :
    ThueEq K.system (K.encode c) K.target → Terminates K.step c := by
  intro h
  let motive := fun (w : List α) (_ : ThueEq K.system w K.target) =>
    ∀ c, w = K.encode c → Terminates K.step c
  have hall : motive (K.encode c) h := by
    apply Relation.ReflTransGen.head_induction_on (motive := motive) h
    · intro c hc
      exact (K.target_ne_encode c hc).elim
    · intro x y hxy hyz ih c hc
      subst x
      cases hstep : K.step c with
      | none => exact terminates_of_halted hstep
      | some d =>
          rcases K.classify hstep hxy with hforward | ⟨p, hback, hp⟩
          · subst hforward
            exact terminates_of_step hstep (ih d rfl)
          · subst hback
            exact terminates_after_step hp (ih p rfl)
  exact hall c rfl

/-- A deterministic machine terminates exactly when its encoding is
Thue-equivalent to the fixed target.
@isnad1 id=iff.0h4v.s5.5641cd305836 from=translated src=- shape=24dddc8d vocab=c0f0d117
-/
theorem terminates_iff {c : C} :
    Terminates K.step c ↔ ThueEq K.system (K.encode c) K.target :=
  ⟨K.simulation, K.inverse_simulation⟩

end Coding

end MachineThue

end Undecidability
