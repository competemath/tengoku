import Tengoku.MagicSquaresFieldsLean.MagicSquares.FieldTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates

/-- A positive certificate stores nine ordinary integer square roots.
The actual entries are their squares modulo `q`.-/
structure NatSquareCertificate where
  q : ℕ
  roots : Square3 ℕ

namespace NatSquareCertificate

/-- Canonical integer representatives of the nine square entries.-/
def residues (c : NatSquareCertificate) : Square3 ℕ :=
  c.roots.map (fun r => r ^ 2 % c.q)

/-- The seven line-sum congruences defining a magic square.-/
def magicModulo (q : ℕ) (m : Square3 ℕ) : Prop :=
  (m.a + m.b + m.c) % q = (m.d + m.e + m.f) % q ∧
  (m.a + m.b + m.c) % q = (m.g + m.h + m.i) % q ∧
  (m.a + m.b + m.c) % q = (m.a + m.d + m.g) % q ∧
  (m.a + m.b + m.c) % q = (m.b + m.e + m.h) % q ∧
  (m.a + m.b + m.c) % q = (m.c + m.f + m.i) % q ∧
  (m.a + m.b + m.c) % q = (m.a + m.e + m.i) % q ∧
  (m.a + m.b + m.c) % q = (m.c + m.e + m.g) % q

instance (q : ℕ) (m : Square3 ℕ) : Decidable (magicModulo q m) := by
  unfold magicModulo
  infer_instance

/-- A certificate is accepted only if all entries are distinct and all eight
line sums agree modulo the stated modulus.-/
def Valid (c : NatSquareCertificate) : Prop :=
  0 < c.q ∧ Function.Injective c.residues.entries ∧ magicModulo c.q c.residues

instance (c : NatSquareCertificate) : Decidable c.Valid := by
  unfold Valid
  infer_instance

/-- The square represented by the data, interpreted in `ZMod q`.-/
def square (c : NatSquareCertificate) : Square3 (ZMod c.q) :=
  c.residues.map Nat.cast

private theorem cast_line_eq {q a b c d e f : ℕ}
    (h : (a + b + c) % q = (d + e + f) % q) :
    (a : ZMod q) + b + c = (d : ZMod q) + e + f := by
  simpa only [Nat.cast_add] using (ZMod.natCast_eq_natCast_iff' _ _ q).mpr h

/-- Soundness of the small arithmetic checker. This proof does not trust the
program that discovered or exported the certificate.-/
theorem valid_sound {c : NatSquareCertificate} (hc : c.Valid) :
    IsMagicOfPowers 2 c.square := by
  rcases hc with ⟨_, hd, hm⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hm with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨cast_line_eq h1, cast_line_eq h2, cast_line_eq h3,
      cast_line_eq h4, cast_line_eq h5, cast_line_eq h6, cast_line_eq h7⟩
  · intro i j hij
    apply hd
    have hv := congrArg ZMod.val hij
    simpa only [square, residues, Square3.map_entries, ZMod.val_natCast, Nat.mod_mod] using hv
  · intro k
    refine ⟨(c.roots.entries k : ZMod c.q), ?_⟩
    simp only [square, residues, Square3.map_entries, ZMod.natCast_mod, Nat.cast_pow]

/-- A list fold makes large output files checkable in independent batches.-/
def checkAll (data : List NatSquareCertificate) : Bool :=
  data.all (fun c => decide c.Valid)

/-- Every record in an accepted batch gives an actual magic square of squares.-/
theorem not_isParker_of_mem {data : List NatSquareCertificate}
    (hcheck : checkAll data = true) {c : NatSquareCertificate} (hc : c ∈ data) :
    ¬ IsParker (ZMod c.q) := by
  have hv : c.Valid := of_decide_eq_true (List.all_eq_true.mp hcheck c hc)
  exact fun h => h ⟨c.square, valid_sound hv⟩

/-- Batch certificates transfer to every field of the corresponding prime size.-/
theorem not_isParker_of_prime_card {data : List NatSquareCertificate}
    (hcheck : checkAll data = true) {c : NatSquareCertificate} (hc : c ∈ data)
    [Fact c.q.Prime] {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = c.q) : ¬ IsParker F := by
  intro h
  exact not_isParker_of_mem hcheck hc ((isNParker_iff_zmod_of_card_eq hcard 2).mp h)

end NatSquareCertificate
end MagicSquares.Certificates
