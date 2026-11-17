/-
Nucleo Lean della campagna Agrawal — INTERFACCIA LOCALE H4.

Questo modulo contiene soltanto i predicati che descrivono H4 lungo i
fattori di un intero fissato.  È separato dalla dicotomia globale per
permettere ai lemmi locali e bifattoriali di usare l'interfaccia senza
creare dipendenze circolari.
-/
import Tengoku.AgrawalR5.AgrawalCore.ScalarCompleteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- H4 richiesta soltanto sui fattori primi di un intero fissato `n`.
La forma locale evita di assumere la congettura universale quando nel
montaggio servono soltanto i fattori del candidato corrente.-/
def LocalH4For (n : ℕ) : Prop :=
  ∀ p (hp : p.Prime), p ∣ n → IsSquare (5 : ZMod p) →
    ¬ @HasOrderFourTransport p ⟨hp⟩

/-- Certificato locale esplicito del fallimento di H4 lungo un fattore
primo split del candidato `n`.-/
def SplitOrderFourWitness (n : ℕ) : Prop :=
  ∃ p, ∃ hp : p.Prime,
    p ∣ n
      ∧ IsSquare (5 : ZMod p)
      ∧ @HasOrderFourTransport p ⟨hp⟩

/-- L'assenza della H4 locale è esattamente l'esistenza di un testimone
split d'ordine quattro.
@isnad1 id=iff.0h1v.s3.bbc9d120408f from=translated src=- shape=1aa159a0 vocab=984f32d7
-/
theorem not_localH4For_iff_splitOrderFourWitness (n : ℕ) :
    ¬ LocalH4For n ↔ SplitOrderFourWitness n := by
  classical
  simp only [LocalH4For, SplitOrderFourWitness, not_forall, not_not]
  constructor
  · rintro ⟨p, hp⟩
    rcases hp with ⟨hpp, hp⟩
    rcases hp with ⟨hpdvd, hp⟩
    rcases hp with ⟨hsplit, htransport⟩
    exact ⟨p, hpp, hpdvd, hsplit, htransport⟩
  · rintro ⟨p, hpp, hpdvd, hsplit, htransport⟩
    exact ⟨p, hpp, hpdvd, hsplit, htransport⟩

end AgrawalCore
