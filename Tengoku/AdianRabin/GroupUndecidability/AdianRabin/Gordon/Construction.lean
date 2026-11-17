import Tengoku.AdianRabin.GroupUndecidability.Computability
import Tengoku.Seed.Algebra.GCDMonoid.Finset
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.GroupTheory.Abelianization.Defs
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gordon's one-extra-relator construction

This file formalizes the presentation-theoretic part of Lemma 2.1 of
Gordon (2022).  The torsion hypothesis is recorded in the minimal form used
in Gordon's proof: the selected abelianized generators have distinct orders,
their orders have gcd one, and `degree` extends those orders injectively to
all generators.  (Gordon obtains this form by choosing a minimal witness to
condition (2.1).)
-/

namespace Undecidability.Gordon

/-- Proof-ready, minimal-witness form of condition (2.1) in Gordon's paper.

`selected` lists the generators used in (2.1), `q` gives their exact orders
in the abelianization, and `degree` is the injective exponent assignment used
in relations (iii)--(iv).-/
structure TorsionData (P : FP n m) where
  p : ℕ
  selected : Fin p ↪ Fin n
  q : Fin p → ℕ
  gcd_q : Finset.univ.gcd q = 1
  exactOrder : ∀ i,
    orderOf (Abelianization.of
      (PresentedGroup.of (selected i) : P.Group)) = q i
  degree : Fin n → ℕ
  degree_pos : ∀ i, 0 < degree i
  degree_injective : Function.Injective degree
  degree_selected : ∀ i, degree (selected i) = q i

variable {n m : ℕ} {P : FP n m}

/-- The common free basis used to describe Gordon's uncompressed
free-product-with-amalgamation presentation.-/
inductive BasisIndex (n : ℕ)
  | conjugateA
  | conjugateAlpha
  | old (i : Fin n)
  | commutator
  deriving DecidableEq

def aWord : Word 2 := Word.generator 0
def bWord : Word 2 := Word.generator 1

/-- Eliminate `alpha` using `a * alpha * a⁻¹ = b²`.-/
def alphaWord : Word 2 :=
  Word.product [Word.inverse aWord, Word.pow bWord 2, aWord]

/-- Eliminate `beta` using
`alpha * a * alpha⁻¹ = b * beta * b⁻¹`.-/
def betaWord : Word 2 :=
  Word.product
    [Word.inverse bWord, alphaWord, aWord, Word.inverse alphaWord, bWord]

/-- Gordon's right-hand word `beta⁻ʳ * b * betaʳ`.-/
def rightConjugateWord (r : ℕ) : Word 2 :=
  Word.product
    [Word.inverse (Word.pow betaWord r), bWord, Word.pow betaWord r]

/-- The paper's commutator convention: `[u,v] = u*v*u⁻¹*v⁻¹`.

The project's older constructions use the opposite convention, so this is
kept explicit.-/
def paperCommutator (u v : Word n) : Word n :=
  Word.product [u, v, Word.inverse u, Word.inverse v]

/-- An old generator after eliminating `alpha`, `beta`, and the old
generators from Gordon's presentation.-/
def encodedGenerator (data : TorsionData P) (i : Fin n) : Word 2 :=
  Word.product
    [Word.pow aWord (data.degree i), rightConjugateWord (i.1 + 1),
      Word.inverse (Word.pow alphaWord (data.degree i))]

/-- Substitute the encoded two-generator words for a word in the old
generators.-/
def encodeWord (data : TorsionData P) (w : Word n) : Word 2 :=
  Word.substitute (encodedGenerator data) w

@[simp]
theorem eval_encodeWord {H : Type*} [Group H]
    (data : TorsionData P) (x : Fin 2 → H) (w : Word n) :
    Word.eval x (encodeWord data w) =
      Word.eval (fun i ↦ Word.eval x (encodedGenerator data i)) w :=
  Word.eval_substitute x (encodedGenerator data) w

/-- The single relation left after all Tietze eliminations.-/
def additionalRelator (data : TorsionData P) (w : Word n) : Word 2 :=
  Word.relation
    (paperCommutator (encodeWord data w) (Word.pow alphaWord 2))
    (rightConjugateWord (n + 1))

/-- Gordon's two-generator, one-extra-relator presentation.-/
def transform (P : FP n m) (data : TorsionData P)
    (w : Word n) : FP 2 (m + 1) where
  relator := Fin.append
    (fun i ↦ encodeWord data (P.relator i))
    (fun _ ↦ additionalRelator data w)

@[simp]
theorem transform_old (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : Fin m) :
    (transform P data w).relator (Fin.castAdd 1 i) =
      encodeWord data (P.relator i) := by
  simp [transform]

@[simp]
theorem transform_additional (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : Fin 1) :
    (transform P data w).relator (Fin.natAdd m i) =
      additionalRelator data w := by
  simp [transform]

private theorem inverse_primrec : Primrec (@Word.inverse 2) := by
  have hletterInverse : Primrec fun x : SignedGenerator 2 ↦
      (x.1, !x.2) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  apply Primrec.of_eq
    (Primrec.list_map Primrec.list_reverse
      (hletterInverse.comp Primrec.snd).to₂)
  intro w
  rfl

theorem encodeWord_primrec (P : FP n m) (data : TorsionData P) :
    Primrec (fun w : Word n ↦ encodeWord data w) := by
  have hgenerator : Primrec (encodedGenerator data) :=
    Primrec.fin_app.comp
      (Primrec.const (α := Fin n) (encodedGenerator data)) Primrec.id
  have hletter : Primrec fun x : SignedGenerator n ↦
      bif x.2 then encodedGenerator data x.1
      else Word.inverse (encodedGenerator data x.1) :=
    Primrec.cond Primrec.snd
      (hgenerator.comp Primrec.fst)
      (inverse_primrec.comp (hgenerator.comp Primrec.fst))
  apply Primrec.of_eq
    (Primrec.list_flatMap Primrec.id (hletter.comp Primrec.snd).to₂)
  intro w
  simp only [encodeWord, Word.substitute]
  congr 1
  funext x
  cases x.2 <;> rfl

private theorem relation_primrec {f : Word n → Word 2}
    (hf : Primrec f) (rhs : Word 2) :
    Primrec fun w ↦ Word.relation (f w) rhs := by
  apply Primrec.of_eq
    (Primrec.list_append.comp hf
      (Primrec.const (Word.inverse rhs)))
  intro w
  rfl

private theorem paperCommutator_primrec (v : Word 2) :
    Primrec fun u : Word 2 ↦ paperCommutator u v := by
  apply Primrec.of_eq
    (Primrec.list_append.comp Primrec.id
      (Primrec.list_append.comp (Primrec.const v)
        (Primrec.list_append.comp inverse_primrec
          (Primrec.const (Word.inverse v)))))
  intro u
  simp [paperCommutator, Word.product]

/-- The word-indexed Gordon transformation is uniform and computable.-/
theorem transform_computable (P : FP n m) (data : TorsionData P) :
    Computable₂ fun w i ↦ (transform P data w).relator i := by
  have hcomm : Primrec fun w : Word n ↦
      paperCommutator (encodeWord data w) (Word.pow alphaWord 2) :=
    (paperCommutator_primrec (Word.pow alphaWord 2)).comp
      (encodeWord_primrec P data)
  have hadditional : Primrec fun w : Word n ↦ additionalRelator data w :=
    relation_primrec hcomm (rightConjugateWord (n + 1))
  apply Primrec₂.to_comp
  apply (Primrec.fin_curry).mp
  apply (Primrec.fin_curry).mpr
  apply Primrec₂.swap
  apply (Primrec.fin_curry₁).mpr
  intro i
  change Fin (m + 1) at i
  cases i using Fin.addCases with
  | left j =>
      simpa using
        (Primrec.const (α := Word n) (encodeWord data (P.relator j)))
  | right j =>
      refine Fin.cases ?_ (fun j' ↦ Fin.elim0 j') j
      apply Primrec.of_eq hadditional
      intro w
      rw [transform_additional]

end Undecidability.Gordon
