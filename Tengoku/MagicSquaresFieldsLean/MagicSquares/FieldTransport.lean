import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerResidue
import Tengoku.Seed.FieldTheory.Finite.GaloisField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

namespace Square3

variable {R S : Type*}

/-- Apply a function to all nine entries.-/
def map (f : R → S) (M : Square3 R) : Square3 S where
  a := f M.a
  b := f M.b
  c := f M.c
  d := f M.d
  e := f M.e
  f := f M.f
  g := f M.g
  h := f M.h
  i := f M.i

/--
@isnad1 id=eq.0h5v.s5.41dba2c3c5df from=translated src=- shape=e3f524e5 vocab=9e38f5c2
-/
@[simp] theorem map_entries (f : R → S) (M : Square3 R) (k : Fin 9) :
    (M.map f).entries k = f (M.entries k) := by
  fin_cases k <;> rfl

/-- An injective ring homomorphism transports a magic square of powers.
@isnad1 id=ismagico.2h5v.s7.90aebd702cba from=translated src=- shape=5f894914 vocab=e28ae4af
-/
theorem map_isMagicOfPowers [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) {n : ℕ} {M : Square3 R}
    (hM : IsMagicOfPowers n M) : IsMagicOfPowers n (M.map f) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hM.1 with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    simpa only [IsMagic, map, ← map_add] using
      And.intro (congrArg f h1) (And.intro (congrArg f h2)
        (And.intro (congrArg f h3) (And.intro (congrArg f h4)
          (And.intro (congrArg f h5) (And.intro (congrArg f h6) (congrArg f h7))))))
  · intro i j hij
    exact hM.2.1 (hf (by simpa only [map_entries] using hij))
  · intro k
    obtain ⟨x, hx⟩ := hM.2.2 k
    exact ⟨f x, by simpa only [map_entries, ← map_pow] using congrArg f hx⟩

end Square3

/-- Existence is unchanged by a field isomorphism.
@isnad1 id=iff.0h4v.s6.70e014db4a2a from=translated src=- shape=f1551d4e vocab=941873a3
-/
theorem exists_magic_of_powers_iff_of_ringEquiv {F K : Type*}
    [CommRing F] [CommRing K] (e : F ≃+* K) (n : ℕ) :
    (∃ M : Square3 F, IsMagicOfPowers n M) ↔
      ∃ M : Square3 K, IsMagicOfPowers n M := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M.map e, Square3.map_isMagicOfPowers e.toRingHom e.injective hM⟩
  · rintro ⟨M, hM⟩
    exact ⟨M.map e.symm, Square3.map_isMagicOfPowers e.symm.toRingHom e.symm.injective hM⟩

/-- The Parker property is an invariant of field isomorphism.
@isnad1 id=iff.0h4v.s5.30aaf9387a14 from=translated src=- shape=c8ab110d vocab=18215ce8
-/
theorem isNParker_iff_of_ringEquiv {F K : Type*} [CommRing F] [CommRing K]
    (e : F ≃+* K) (n : ℕ) : IsNParker F n ↔ IsNParker K n := by
  exact not_congr (exists_magic_of_powers_iff_of_ringEquiv e n)

/-- Concrete finite-field certificates apply to every field of the same size.
@isnad1 id=iff.1h3v.s5.c4813f22f631 from=translated src=- shape=b3ccf2d7 vocab=4623f7b8
-/
theorem isNParker_iff_of_card_eq {F K : Type*} [Field F] [Field K]
    [Fintype F] [Fintype K] (hcard : Fintype.card F = Fintype.card K) (n : ℕ) :
    IsNParker F n ↔ IsNParker K n :=
  isNParker_iff_of_ringEquiv (FiniteField.ringEquivOfCardEq hcard) n

/-- A prime-field certificate gives a uniform theorem at that prime cardinality.
@isnad1 id=iff.1h3v.s5.49d185d18c2b from=translated src=- shape=975d8990 vocab=672356c8
-/
theorem isNParker_iff_zmod_of_card_eq {F : Type*} [Field F] [Fintype F]
    {p : ℕ} [Fact p.Prime] (hcard : Fintype.card F = p) (n : ℕ) :
    IsNParker F n ↔ IsNParker (ZMod p) n :=
  isNParker_iff_of_card_eq (hcard.trans (ZMod.card p).symm) n

end MagicSquares
