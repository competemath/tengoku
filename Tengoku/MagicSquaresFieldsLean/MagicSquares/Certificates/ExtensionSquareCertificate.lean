import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.DensePowerCertificate
import Tengoku.Seed.Algebra.CharP.CharAndCard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates
open DensePolynomial

structure ExtensionSquareCertificate (R : Type*) where
  modulus : List R
  entries : Square3 (List R)
  roots : Square3 (List R)
  rootQuotients : Square3 (List R)
  inverses : Fin 9 → Fin 9 → List R
  inverseQuotients : Fin 9 → Fin 9 → List R
  powerSteps : List (PowStep R)

namespace ExtensionSquareCertificate
variable {R S : Type*} [CommRing R] [DecidableEq R]

def magicCheck (m : Square3 (List R)) : Bool :=
  eqCheck (add (add m.a m.b) m.c) (add (add m.d m.e) m.f) &&
  eqCheck (add (add m.a m.b) m.c) (add (add m.g m.h) m.i) &&
  eqCheck (add (add m.a m.b) m.c) (add (add m.a m.d) m.g) &&
  eqCheck (add (add m.a m.b) m.c) (add (add m.b m.e) m.h) &&
  eqCheck (add (add m.a m.b) m.c) (add (add m.c m.f) m.i) &&
  eqCheck (add (add m.a m.b) m.c) (add (add m.a m.e) m.i) &&
  eqCheck (add (add m.a m.b) m.c) (add (add m.c m.e) m.g)

def Valid (c : ExtensionSquareCertificate R) : Prop :=
  magicCheck c.entries = true ∧
  (∀ i : Fin 9, eqCheck (mul (c.roots.entries i) (c.roots.entries i))
    (add (c.entries.entries i) (mul c.modulus (c.rootQuotients.entries i))) = true) ∧
  (∀ i j : Fin 9, i ≠ j →
    eqCheck (mul (c.inverses i j) (sub (c.entries.entries i) (c.entries.entries j)))
      (add [1] (mul c.modulus (c.inverseQuotients i j))) = true) ∧
  checkPow c.modulus [1] c.powerSteps = true

instance (c : ExtensionSquareCertificate R) : Decidable c.Valid := by
  unfold Valid
  infer_instance

/-- All entries, roots, line sums and distinctness follow from exact
coefficient identities at any root of the defining polynomial.
@isnad1 id=ismagico.2h5v.s6.5b0f72cd37bc from=translated src=- shape=f6156604 vocab=b1f55061
-/
theorem valid_sound [CommRing S] [Nontrivial S] (h : R →+* S) (x : S)
    {c : ExtensionSquareCertificate R} (hc : c.Valid) (hf : eval h x c.modulus = 0) :
    IsMagicOfPowers 2 (c.entries.map (eval h x)) := by
  rcases hc with ⟨hm, hr, hd, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [magicCheck, Bool.and_eq_true] at hm
    rcases hm with ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨by simpa only [eval_add, Square3.map] using eqCheck_sound h x h1,
      by simpa only [eval_add, Square3.map] using eqCheck_sound h x h2,
      by simpa only [eval_add, Square3.map] using eqCheck_sound h x h3,
      by simpa only [eval_add, Square3.map] using eqCheck_sound h x h4,
      by simpa only [eval_add, Square3.map] using eqCheck_sound h x h5,
      by simpa only [eval_add, Square3.map] using eqCheck_sound h x h6,
      by simpa only [eval_add, Square3.map] using eqCheck_sound h x h7⟩
  · intro i j hij
    by_contra hne
    have hi := eqCheck_sound h x (hd i j hne)
    simp only [Square3.map_entries] at hij
    simp [eval_mul, eval_sub, eval_add, eval, hf, hij] at hi
  · intro i
    refine ⟨eval h x (c.roots.entries i), ?_⟩
    have hi := eqCheck_sound h x (hr i)
    simpa [eval_mul, eval_add, hf, pow_two, Square3.map_entries] using hi

/-- Existence of a root follows from the checked divisibility in `X^q-X`,
which splits over every field with `q` elements.
@isnad1 id=ex.4h4v.s7.5ad260f9e2c0 from=translated src=- shape=dc6aedea vocab=ba7efc99
-/
theorem exists_magic_of_card {p d : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Fintype F]
    {c : ExtensionSquareCertificate (ZMod p)} (hc : c.Valid)
    (hdegree : (poly c.modulus).degree ≠ 0)
    (hexponent : exponent 0 c.powerSteps = p ^ d)
    (hcard : Fintype.card F = p ^ d) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M := by
  letI : CharP F p := charP_of_card_eq_prime_pow hcard
  letI : Algebra (ZMod p) F := (ZMod.castHom dvd_rfl F).toAlgebra
  let h : ZMod p →+* F := algebraMap (ZMod p) F
  have hdvd := dvd_X_pow_sub_X_of_check hc.2.2.2
  rw [hexponent, ← hcard] at hdvd
  have hsplit := FiniteField.splits_X_pow_card_sub_X (K := F) (p := p)
  have hnz : Polynomial.map h (Polynomial.X ^ Fintype.card F - Polynomial.X) ≠ 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    exact FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hf := hsplit.of_dvd hnz (Polynomial.map_dvd h hdvd)
  have hd : (Polynomial.map h (poly c.modulus)).degree ≠ 0 := by
    rwa [Polynomial.degree_map_eq_of_injective h.injective]
  obtain ⟨x, hx⟩ := hf.exists_eval_eq_zero hd
  have hx' : eval h x c.modulus = 0 := by
    simpa only [Polynomial.eval_map, eval_poly] using hx
  exact ⟨_, valid_sound h x hc hx'⟩

end ExtensionSquareCertificate
end MagicSquares.Certificates
