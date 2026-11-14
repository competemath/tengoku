import Tengoku.TdaLib.TDA.Persistence.FiniteBarcode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite translations, shortness and observed endpoints -/

set_option autoImplicit false

universe u

namespace TDA.Persistence

/-- Translation-triviality means vanishing of the maps `i → theta i`.
The translation may identify stages; inflationarity supplies the required inequalities.-/
def TranslationTrivial {s : ℕ} {k : Type u} [Field k] (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i)
    (K : PModule.{u,0,u} k (Fin s)) : Prop :=
  ∀ i, structureMap K (hTheta i) = 0

/-- The birth of a nonempty finite interval is an observed stage.-/
def FiniteInterval.birthStage {s : ℕ} (I : FiniteInterval s) : Fin s :=
  ⟨I.birth, I.birth_lt_death.trans_le I.death_le_size⟩

/-- Translate an observed death; terminal death remains the finite observation boundary.
Only deaths strictly below `s` are interpreted as stages.-/
def FiniteInterval.translatedDeath {s : ℕ} (I : FiniteInterval s)
    (theta : Fin s →o Fin s) : ℕ :=
  if h : I.death < s then (theta ⟨I.death, h⟩).val else s

/-- A finite observed death is translated at that stage.
@isnad1 id=eq.1h3v.s6.221085e842c5 from=translated src=- shape=d5647bac vocab=4375a8f3
-/
theorem FiniteInterval.translatedDeath_of_lt {s : ℕ} (I : FiniteInterval s)
    (theta : Fin s →o Fin s) (h : I.death < s) :
    I.translatedDeath theta = (theta ⟨I.death, h⟩).val := dite_eq_left h

/-- The terminal endpoint is never selected as a stage of the finite chain.
@isnad1 id=eq.1h3v.s5.a0a9425fa539 from=translated src=- shape=e47bc409 vocab=f2663014
-/
theorem FiniteInterval.translatedDeath_terminal {s : ℕ} (I : FiniteInterval s)
    (theta : Fin s →o Fin s) (h : I.death = s) : I.translatedDeath theta = s := by
  simp [translatedDeath, h]

/-- Translated death depends only on the endpoint, not the birth or interval proof fields.
@isnad1 id=eq.1h4v.s5.60d3fce42529 from=translated src=- shape=c749e1eb vocab=f2663014
-/
theorem FiniteInterval.translatedDeath_congr {s : ℕ} (I J : FiniteInterval s)
    (theta : Fin s →o Fin s) (h : I.death = J.death) :
    I.translatedDeath theta = J.translatedDeath theta := by
  by_cases hi : I.death < s
  · have hj : J.death < s := h ▸ hi
    rw [translatedDeath_of_lt I theta hi, translatedDeath_of_lt J theta hj]
    exact congrArg (fun i : Fin s => (theta i).val) (Fin.ext h)
  · have hj : ¬ J.death < s := h ▸ hi
    simp only [translatedDeath, dite_eq_right hi, dite_eq_right hj]

/-- Identity translation leaves every finite or terminal endpoint unchanged.
@isnad1 id=eq.0h2v.s4.b4731e28a98b from=translated src=- shape=581ae922 vocab=f46b73e7
-/
theorem FiniteInterval.translatedDeath_id {s : ℕ} (I : FiniteInterval s) :
    I.translatedDeath (OrderHom.id : Fin s →o Fin s) = I.death := by
  by_cases h : I.death < s
  · rw [translatedDeath_of_lt I _ h]; rfl
  · have := I.death_le_size
    simp [translatedDeath, show I.death = s by omega]

end TDA.Persistence
