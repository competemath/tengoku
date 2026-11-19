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

@[simp] theorem map_entries (f : R → S) (M : Square3 R) (k : Fin 9) :
    (M.map f).entries k = f (M.entries k) := by
  fin_cases k <;> rfl

/-- An injective ring homomorphism transports a magic square of powers.-/
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

/-- Existence is unchanged by a field isomorphism.-/
theorem exists_magic_of_powers_iff_of_ringEquiv {F K : Type*}
    [CommRing F] [CommRing K] (e : F ≃+* K) (n : ℕ) :
    (∃ M : Square3 F, IsMagicOfPowers n M) ↔
      ∃ M : Square3 K, IsMagicOfPowers n M := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M.map e, Square3.map_isMagicOfPowers e.toRingHom e.injective hM⟩
  · rintro ⟨M, hM⟩
    exact ⟨M.map e.symm, Square3.map_isMagicOfPowers e.symm.toRingHom e.symm.injective hM⟩

/-- The Parker property is an invariant of field isomorphism.-/
theorem isNParker_iff_of_ringEquiv {F K : Type*} [CommRing F] [CommRing K]
    (e : F ≃+* K) (n : ℕ) : IsNParker F n ↔ IsNParker K n := by
  exact not_congr (exists_magic_of_powers_iff_of_ringEquiv e n)

/-- Concrete finite-field certificates apply to every field of the same size.-/
theorem isNParker_iff_of_card_eq {F K : Type*} [Field F] [Field K]
    [Fintype F] [Fintype K] (hcard : Fintype.card F = Fintype.card K) (n : ℕ) :
    IsNParker F n ↔ IsNParker K n :=
  isNParker_iff_of_ringEquiv (FiniteField.ringEquivOfCardEq hcard) n

/-- A prime-field certificate gives a uniform theorem at that prime cardinality.-/
theorem isNParker_iff_zmod_of_card_eq {F : Type*} [Field F] [Fintype F]
    {p : ℕ} [Fact p.Prime] (hcard : Fintype.card F = p) (n : ℕ) :
    IsNParker F n ↔ IsNParker (ZMod p) n :=
  isNParker_iff_of_card_eq (hcard.trans (ZMod.card p).symm) n

end MagicSquares
