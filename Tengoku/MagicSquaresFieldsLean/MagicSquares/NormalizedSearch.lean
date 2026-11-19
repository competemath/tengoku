import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.PowerExistence
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerTest

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Inversion preserves the power condition.
@isnad1 id=isnthpow.1h3v.s5.7ee516498d9e from=translated src=- shape=09f887e1 vocab=4ef18796
-/
theorem IsNthPower.inv {n : ℕ} {a : F} (ha : IsNthPower n a) :
    IsNthPower n a⁻¹ := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨x⁻¹, inv_pow x n⟩

namespace Square3

/-- Entrywise scalar multiplication of a square.-/
def scale (s : F) (M : Square3 F) : Square3 F where
  a := s * M.a
  b := s * M.b
  c := s * M.c
  d := s * M.d
  e := s * M.e
  f := s * M.f
  g := s * M.g
  h := s * M.h
  i := s * M.i

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s5.f9f3942b5c1b from=translated src=- shape=8d484e16 vocab=87f4fde4
-/
@[simp] theorem scale_entries (s : F) (M : Square3 F) (k : Fin 9) :
    (scale s M).entries k = s * M.entries k := by
  fin_cases k <;> rfl

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=ismagic.1h3v.s5.6f97bd426ab3 from=translated src=- shape=46d37d77 vocab=c37bf0b4
-/
theorem scale_isMagic {M : Square3 F} (hM : M.IsMagic) (s : F) :
    (scale s M).IsMagic := by
  rcases hM with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  change s * M.a + s * M.b + s * M.c = s * M.d + s * M.e + s * M.f ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination s * h1
  · change s * M.a + s * M.b + s * M.c = s * M.g + s * M.h + s * M.i
    linear_combination s * h2
  · change s * M.a + s * M.b + s * M.c = s * M.a + s * M.d + s * M.g
    linear_combination s * h3
  · change s * M.a + s * M.b + s * M.c = s * M.b + s * M.e + s * M.h
    linear_combination s * h4
  · change s * M.a + s * M.b + s * M.c = s * M.c + s * M.f + s * M.i
    linear_combination s * h5
  · change s * M.a + s * M.b + s * M.c = s * M.a + s * M.e + s * M.i
    linear_combination s * h6
  · change s * M.a + s * M.b + s * M.c = s * M.c + s * M.e + s * M.g
    linear_combination s * h7

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=ismagico.3h4v.s6.acdde6e3d8d9 from=translated src=- shape=5e570a42 vocab=96e6621f
-/
theorem scale_isMagicOfPowers {n : ℕ} {M : Square3 F} (hM : IsMagicOfPowers n M)
    {s : F} (hs : s ≠ 0) (hsp : IsNthPower n s) :
    IsMagicOfPowers n (scale s M) := by
  refine ⟨scale_isMagic hM.1 s, ?_, ?_⟩
  · intro i j hij
    apply hM.2.1
    exact mul_left_cancel₀ hs (by simpa only [scale_entries] using hij)
  · intro k
    rw [scale_entries]
    exact hsp.mul (hM.2.2 k)

end Square3

omit [Fintype F] [DecidableEq F] in
/-- **Section 8 normalization is complete.** Every distinct magic square
of powers can be scaled into the center-zero one-parameter family or the
center-one two-parameter family, preserving the power condition.
@isnad1 id=iff.0h2v.s5.6e17a8d48e0f from=translated src=- shape=44f7702b vocab=0473beb3
-/
theorem exists_magic_of_powers_iff_normalized (n : ℕ) :
    (∃ M : Square3 F, IsMagicOfPowers n M) ↔
      (∃ x : F, IsMagicOfPowers n (Square3.centerZero x)) ∨
      (∃ u v : F, IsMagicOfPowers n (Square3.centerOne u v)) := by
  constructor
  · rintro ⟨M, hM⟩
    by_cases he : M.e = 0
    · left
      have hc : M.c ≠ 0 := by
        intro hc
        have heq : M.entries (2 : Fin 9) = M.entries (4 : Fin 9) := by
          simp [Square3.entries, hc, he]
        have hi := hM.2.1 heq
        exact (by decide : (2 : Fin 9) ≠ 4) hi
      have hp : IsNthPower n M.c := by simpa [Square3.entries] using hM.2.2 (2 : Fin 9)
      let N := Square3.scale M.c⁻¹ M
      have hN : IsMagicOfPowers n N :=
        Square3.scale_isMagicOfPowers hM (inv_ne_zero hc) hp.inv
      have hNe : N.e = 0 := by simp [N, Square3.scale, he]
      have hNc : N.c = 1 := by simp [N, Square3.scale, hc]
      have hform : N = Square3.centerZero N.a := by
        simpa [Square3.centerZero, hNe, hNc] using Square3.universal_form N hN.1
      exact ⟨N.a, hform ▸ hN⟩
    · right
      have hp : IsNthPower n M.e := by simpa [Square3.entries] using hM.2.2 (4 : Fin 9)
      let N := Square3.scale M.e⁻¹ M
      have hN : IsMagicOfPowers n N :=
        Square3.scale_isMagicOfPowers hM (inv_ne_zero he) hp.inv
      have hNe : N.e = 1 := by simp [N, Square3.scale, he]
      have hform : N = Square3.centerOne (N.a - 1) (N.c - 1) := by
        simpa [Square3.centerOne, hNe] using Square3.universal_form N hN.1
      exact ⟨N.a - 1, N.c - 1, hform ▸ hN⟩
  · rintro (⟨x, hx⟩ | ⟨u, v, huv⟩)
    · exact ⟨Square3.centerZero x, hx⟩
    · exact ⟨Square3.centerOne u v, huv⟩

omit [Fintype F] [DecidableEq F] in
/-- Exhausting the normalized families is sufficient to certify a Parker field.
@isnad1 id=iff.0h2v.s5.8b88c641e82e from=translated src=- shape=33661e92 vocab=e4628ec6
-/
theorem isNParker_iff_normalized_fail (n : ℕ) :
    IsNParker F n ↔
      (∀ x : F, ¬ IsMagicOfPowers n (Square3.centerZero x)) ∧
      (∀ u v : F, ¬ IsMagicOfPowers n (Square3.centerOne u v)) := by
  rw [IsNParker, exists_magic_of_powers_iff_normalized]
  simp only [not_or, not_exists]

omit [Fintype F] [DecidableEq F] in
/-- With a sign obstruction, the complete center-one search alone certifies
nonexistence; no center-zero distinct square can have the power condition.
@isnad1 id=iff.1h2v.s6.9b0976504e2f from=translated src=- shape=8850197d vocab=abac7634
-/
theorem isNParker_iff_centerOne_fail_of_sign_obstruction {n : ℕ}
    (hneg : ¬ IsNthPower n (-1 : F)) :
    IsNParker F n ↔ ∀ u v : F, ¬ IsMagicOfPowers n (Square3.centerOne u v) := by
  rw [isNParker_iff_normalized_fail]
  have hz (x : F) : ¬ IsMagicOfPowers n (Square3.centerZero x) := by
    intro h
    apply hneg
    simpa [Square3.entries] using h.2.2 (6 : Fin 9)
  simp [hz]

/-- The decidable entry conditions used by the finite search.-/
def normalizedPowerConditions (n : ℕ) (M : Square3 F) : Prop :=
  Function.Injective M.entries ∧ ∀ k : Fin 9,
    M.entries k = 0 ∨ M.entries k ^
      ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1

instance (n : ℕ) (M : Square3 F) : Decidable (normalizedPowerConditions n M) :=
  inferInstanceAs (Decidable (Function.Injective M.entries ∧ ∀ k : Fin 9,
    M.entries k = 0 ∨ M.entries k ^
      ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1))

/-- A complete executable search over at most `q+q^2` normalized candidates.-/
def normalizedPowerSearchSucceeds (n : ℕ) : Bool :=
  decide ((∃ x : F, normalizedPowerConditions n (Square3.centerZero x)) ∨
    (∃ u v : F, normalizedPowerConditions n (Square3.centerOne u v)))

/-- The arithmetic entry test is equivalent to the power predicate on magic squares.
@isnad1 id=iff.2h3v.s5.f5aae2c0d149 from=translated src=- shape=102188e7 vocab=822ef4b7
-/
theorem normalizedPowerConditions_iff {n : ℕ} (hn : 0 < n)
    {M : Square3 F} (hM : M.IsMagic) :
    normalizedPowerConditions n M ↔ IsMagicOfPowers n M := by
  simp only [normalizedPowerConditions, IsMagicOfPowers,
    ← isNthPower_iff_zero_or_pow_eq_one hn, hM, true_and, Square3.PairwiseDistinct]

/-- **Algorithm 2 is sound and complete.** A failed normalized finite search
is a proof of the Parker property, once its Boolean result is certified.
@isnad1 id=iff.1h2v.s5.7fb8ed0cf339 from=translated src=- shape=912e66b5 vocab=e7380e0f
-/
theorem normalizedPowerSearchSucceeds_eq_true_iff {n : ℕ} (hn : 0 < n) :
    normalizedPowerSearchSucceeds (F := F) n = true ↔
      ∃ M : Square3 F, IsMagicOfPowers n M := by
  rw [normalizedPowerSearchSucceeds, decide_eq_true_eq,
    exists_magic_of_powers_iff_normalized]
  simp only [normalizedPowerConditions_iff hn (Square3.centerZero_isMagic _),
    normalizedPowerConditions_iff hn (Square3.centerOne_isMagic _ _)]

/-- A kernel-checked false result of the finite search certifies an exception.
@isnad1 id=iff.1h2v.s5.f2a642189486 from=translated src=- shape=7fe17123 vocab=ea6c31f2
-/
theorem isNParker_iff_normalizedPowerSearch_eq_false {n : ℕ} (hn : 0 < n) :
    IsNParker F n ↔ normalizedPowerSearchSucceeds (F := F) n = false := by
  rw [IsNParker, ← normalizedPowerSearchSucceeds_eq_true_iff hn]
  cases normalizedPowerSearchSucceeds (F := F) n <;> decide

end MagicSquares
