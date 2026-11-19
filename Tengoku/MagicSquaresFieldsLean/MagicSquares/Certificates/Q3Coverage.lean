import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.NatSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates

/-- The known exceptions in the `3 mod 4` branch.-/
def q3Exceptions : List ℕ := [3, 7, 11, 19, 23, 27, 31, 43, 47, 67, 243]

/-- A dense certificate covers every integer `3 mod 4`: a proper divisor,
an already handled exception, or nine explicit square roots.-/
inductive Q3Step where
  | factor (d : ℕ)
  | exception
  | witness (roots : Square3 ℕ)

namespace Q3Step

def Valid (q : ℕ) : Q3Step → Prop
  | .factor d => 1 < d ∧ d < q ∧ q % d = 0
  | .exception => q ∈ q3Exceptions
  | .witness roots => (NatSquareCertificate.mk q roots).Valid

instance (q : ℕ) (s : Q3Step) : Decidable (s.Valid q) := by
  cases s <;> unfold Valid <;> infer_instance

def checkFrom (q : ℕ) : List Q3Step → Bool
  | [] => true
  | s :: rest => decide (s.Valid q) && checkFrom (q + 4) rest

/--
@isnad1 id=valid.2h3v.s6.6ec0fc3281e2 from=translated src=- shape=4d85b12f vocab=3c134063
-/
theorem valid_at {data : List Q3Step} {q : ℕ} (h : checkFrom q data = true)
    {k : ℕ} (hk : k < data.length) : (data[k]).Valid (q + 4 * k) := by
  induction data generalizing q k with
  | nil => simp at hk
  | cons s rest ih =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have hkt : k < rest.length := by simpa using hk
      have hv := ih h.2 hkt
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv

/-- Soundness needs no primality computation: a supplied proper divisor
rules out a prime, and a witness gives a square by the previous checker.
@isnad1 id=ex.3h2v.s5.a0e14933a01d from=translated src=- shape=f4c9bbfd vocab=5febef0f
-/
theorem valid_sound {s : Q3Step} {q : ℕ} (h : s.Valid q)
    (hp : q.Prime) (he : q ∉ q3Exceptions) :
    ∃ M : Square3 (ZMod q), IsMagicOfPowers 2 M := by
  cases s with
  | factor d =>
    obtain ⟨hd, hdq, hm⟩ := h
    have hv := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hm)
    omega
  | exception => exact False.elim (he h)
  | witness roots => exact ⟨_, NatSquareCertificate.valid_sound h⟩

end Q3Step

/-- Coverage of a whole numerical interval, including excluded composites.-/
def Q3Covered (lo hi : ℕ) : Prop := ∀ q, lo ≤ q → q < hi → q % 4 = 3 →
    q.Prime → q ∉ q3Exceptions → ∃ M : Square3 (ZMod q), IsMagicOfPowers 2 M

/--
@isnad1 id=q3covere.2h2v.s5.b256cc33252a from=translated src=- shape=d556de25 vocab=78074284
-/
theorem q3Covered_of_check {lo : ℕ} {data : List Q3Step}
    (h : Q3Step.checkFrom lo data = true) (hl : lo % 4 = 3) :
    Q3Covered lo (lo + 4 * data.length) := by
  intro q hlo hhi hmod hp he
  have hd : (q - lo) % 4 = 0 := by omega
  have hq : lo + 4 * ((q - lo) / 4) = q := by omega
  have hk : (q - lo) / 4 < data.length := by omega
  have hv := Q3Step.valid_at h hk
  rw [hq] at hv
  exact Q3Step.valid_sound hv hp he

/--
@isnad1 id=q3covere.2h3v.s4.455787d76387 from=translated src=- shape=0bc0c4a6 vocab=68deb83d
-/
theorem q3Covered_union {a b c : ℕ} (hab : Q3Covered a b) (hbc : Q3Covered b c) :
    Q3Covered a c := by
  intro q ha hc hm hp he
  by_cases hq : q < b
  · exact hab q ha hq hm hp he
  · exact hbc q (by omega) hc hm hp he

end MagicSquares.Certificates
