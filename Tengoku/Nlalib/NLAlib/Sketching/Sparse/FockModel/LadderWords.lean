/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.LadderMatrices
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Typed sparse-Fock word inventory

The oriented ladder words are classified by grade shift and heavy-leg count, with all nine exact finite cell counts.
Ported from `SparseFockFormal.BandInventory` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

/-- The four oriented summands of the local Jacobi matrix.

Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
inductive Leg where
  | pUp
  | pDown
  | rUp
  | rDown
  deriving DecidableEq, Repr

/-- The four oriented ladder legs have their literal finite enumeration.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
instance : Fintype Leg where
  elems := {.pUp, .pDown, .rUp, .rDown}
  complete x := by cases x <;> simp

/-- Each typed ladder leg selects its literal local creation or annihilation matrix.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Leg.op : Leg → LevelOp
  | .pUp => pCreate
  | .pDown => pDestroy
  | .rUp => rPromote
  | .rDown => rDemote

/-- A ladder leg records its signed occupation-grade change.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Leg.degree : Leg → ℤ
  | .pUp | .rUp => 1
  | .pDown | .rDown => -1

/-- A ladder leg records whether it contributes one heavy coefficient.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Leg.heavy : Leg → ℕ
  | .pUp | .pDown => 0
  | .rUp | .rDown => 1

/-- Taking a ladder adjoint exchanges creation and annihilation of the same kind.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Leg.adjoint : Leg → Leg
  | .pUp => .pDown
  | .pDown => .pUp
  | .rUp => .rDown
  | .rDown => .rUp

/-- Taking the ladder adjoint twice returns the original leg.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.70af69cb5a38 from=translated src=- shape=47dcad53 vocab=ee5387f7
-/
@[simp] theorem Leg.adjoint_adjoint (a : Leg) : a.adjoint.adjoint = a := by
  cases a <;> rfl

/-- Taking a ladder adjoint negates its grade change.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.c450c33c48ba from=translated src=- shape=d2189a58 vocab=b808bf96
-/
@[simp] theorem Leg.degree_adjoint (a : Leg) :
    a.adjoint.degree = -a.degree := by
  cases a <;> rfl

/-- Taking a ladder adjoint preserves its heavy coefficient count.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.b3423278ada5 from=translated src=- shape=8d4cac31 vocab=35b4a89b
-/
@[simp] theorem Leg.heavy_adjoint (a : Leg) :
    a.adjoint.heavy = a.heavy := by
  cases a <;> rfl

/-- The transpose of a literal ladder matrix is its typed adjoint matrix.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.1fb4f02f539f from=translated src=- shape=f09ab015 vocab=cfd1b4fc
-/
theorem Leg.transpose_op (a : Leg) : a.op.transpose = a.adjoint.op := by
  cases a <;> simp [Leg.op, Leg.adjoint]

/-- Every literal ladder matrix has its recorded grade shift.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=islevelg.0h1v.s2.d2bf1115dea5 from=translated src=- shape=fc2c1e2b vocab=435eeae6
-/
theorem Leg.op_homogeneous (a : Leg) :
    IsLevelGradeShift a.degree a.op := by
  cases a <;>
    simp only [Leg.degree, Leg.op] <;>
    first
    | exact pCreate_homogeneous
    | exact pDestroy_homogeneous
    | exact rPromote_homogeneous
    | exact rDemote_homogeneous

/-- A local word records the two oriented transitions at two distinct sites.

Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev Word := Leg × Leg

/-- The grade change of a two-leg word is the sum of its leg changes.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Word.degree (w : Word) : ℤ := w.1.degree + w.2.degree

/-- The heavy coefficient count of a two-leg word is the sum of its leg counts.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Word.heavy (w : Word) : ℕ := w.1.heavy + w.2.heavy

/-- Adjoint after transposing the external rank-one coefficient and relabeling the
ordered site pair.

Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Word.orderedAdjoint (w : Word) : Word := (w.2.adjoint, w.1.adjoint)

/-- Taking the ordered word adjoint twice returns the original word.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.9f188cdf5c6e from=translated src=- shape=47dcad53 vocab=d239676f
-/
@[simp] theorem Word.orderedAdjoint_involutive (w : Word) :
    w.orderedAdjoint.orderedAdjoint = w := by
  rcases w with ⟨a, b⟩
  simp [Word.orderedAdjoint]

/-- The ordered word adjoint negates its total grade change.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.ec9b43d35867 from=translated src=- shape=d2189a58 vocab=32e06d5f
-/
@[simp] theorem Word.degree_orderedAdjoint (w : Word) :
    w.orderedAdjoint.degree = -w.degree := by
  rcases w with ⟨a, b⟩
  simp [Word.orderedAdjoint, Word.degree]

/-- The ordered word adjoint preserves its heavy coefficient count.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.f0fa1e2a17fd from=translated src=- shape=8d4cac31 vocab=137dafd2
-/
@[simp] theorem Word.heavy_orderedAdjoint (w : Word) :
    w.orderedAdjoint.heavy = w.heavy := by
  rcases w with ⟨a, b⟩
  simp [Word.orderedAdjoint, Word.heavy, Nat.add_comm]

/-- The three band labels represent raising, preserving, and lowering by two grades.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
inductive Shift where
  | plus
  | zero
  | minus
  deriving DecidableEq, Repr

/-- The three grade-shift labels have their literal finite enumeration.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
instance : Fintype Shift where
  elems := {.plus, .zero, .minus}
  complete x := by cases x <;> simp

/-- The three word labels record zero, one, or two heavy ladder legs.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
inductive Heaviness where
  | lightLight
  | lightHeavy
  | heavyHeavy
  deriving DecidableEq, Repr

/-- The three heavy-leg-count labels have their literal finite enumeration.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
instance : Fintype Heaviness where
  elems := {.lightLight, .lightHeavy, .heavyHeavy}
  complete x := by cases x <;> simp

/-- A word is classified by its raising, preserving, or lowering grade shift.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Word.shift : Word → Shift
  | (.pUp, .pUp) | (.pUp, .rUp) | (.rUp, .pUp) | (.rUp, .rUp) => .plus
  | (.pDown, .pDown) | (.pDown, .rDown) | (.rDown, .pDown) |
      (.rDown, .rDown) => .minus
  | _ => .zero

/-- A word is classified by the number of heavy ladder legs it contains.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Word.heaviness : Word → Heaviness
  | (.pUp, .pUp) | (.pUp, .pDown) | (.pDown, .pUp) | (.pDown, .pDown) =>
      .lightLight
  | (.rUp, .rUp) | (.rUp, .rDown) | (.rDown, .rUp) | (.rDown, .rDown) =>
      .heavyHeavy
  | _ => .lightHeavy

/-- The three band labels have integer degree two, zero, and minus two.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Shift.degree : Shift → ℤ
  | .plus => 2
  | .zero => 0
  | .minus => -2

/-- A word's computed degree agrees with its shift label.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.2662a65de1bb from=translated src=- shape=69b989be vocab=18e42025
-/
theorem Word.degree_eq_shift (w : Word) : w.degree = w.shift.degree := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- A word's heavy-leg count agrees with its heaviness label.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s5.ecc1f4f29a6c from=translated src=- shape=51697df1 vocab=3042fd3d
-/
theorem Word.heavy_eq_heaviness (w : Word) :
    w.heavy =
      match w.heaviness with
      | .lightLight => 0
      | .lightHeavy => 1
      | .heavyHeavy => 2 := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- Taking a band adjoint exchanges raising and lowering and fixes preserving.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Shift.adjoint : Shift → Shift
  | .plus => .minus
  | .zero => .zero
  | .minus => .plus

/-- The ordered word adjoint has the adjoint grade-shift label.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.a14c6a575292 from=translated src=- shape=0ebce511 vocab=cb6a643e
-/
@[simp] theorem Word.shift_orderedAdjoint (w : Word) :
    w.orderedAdjoint.shift = w.shift.adjoint := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- The ordered word adjoint retains its heaviness label.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.d69ea9671213 from=translated src=- shape=8d4cac31 vocab=d87b5ffc
-/
@[simp] theorem Word.heaviness_orderedAdjoint (w : Word) :
    w.orderedAdjoint.heaviness = w.heaviness := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- One inventory cell contains exactly the words with its shift and heaviness labels.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def wordsIn (δ : Shift) (h : Heaviness) : Finset Word :=
  Finset.univ.filter fun w => w.shift = δ ∧ w.heaviness = h

/-- Membership in an inventory cell is equality of its two classification labels.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h3v.s5.b3d994f19f46 from=translated src=- shape=d586c8eb vocab=f4e9b9f3
-/
@[simp] theorem mem_wordsIn (w : Word) (δ : Shift) (h : Heaviness) :
    w ∈ wordsIn δ h ↔ w.shift = δ ∧ w.heaviness = h := by
  simp [wordsIn]

/-- Every word lies in its uniquely determined grade/heaviness cell.

Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=and.0h1v.s5.f67be4538b0b from=translated src=- shape=317c65e5 vocab=f4e9b9f3
-/
theorem word_has_unique_cell (w : Word) :
    w ∈ wordsIn w.shift w.heaviness ∧
      ∀ δ h, w ∈ wordsIn δ h → δ = w.shift ∧ h = w.heaviness := by
  constructor
  · simp
  · intro δ h hw
    rw [mem_wordsIn] at hw
    exact ⟨hw.1.symm, hw.2.symm⟩

/-- There are exactly sixteen oriented two-leg words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.4a632abe3202 from=translated src=- shape=b0ae1d2b vocab=83f398dd
-/
@[simp] theorem card_all_words : Fintype.card Word = 16 := by decide

/-- The exact `3 × 3` inventory counts.  The middle grade contains each word together
with its distinct adjoint; the plus/minus rows are interchanged by adjoint.

Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.53a327c52a37 from=translated src=- shape=840a436c vocab=a93b543b
-/
theorem card_plus_lightLight : (wordsIn .plus .lightLight).card = 1 := by decide
/-- The raising lightHeavy inventory cell contains exactly 2 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.a8810415e718 from=translated src=- shape=840a436c vocab=273633ee
-/
theorem card_plus_lightHeavy : (wordsIn .plus .lightHeavy).card = 2 := by decide
/-- The raising heavyHeavy inventory cell contains exactly 1 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.fe8995302c4f from=translated src=- shape=840a436c vocab=80527ab1
-/
theorem card_plus_heavyHeavy : (wordsIn .plus .heavyHeavy).card = 1 := by decide
/-- The preserving lightLight inventory cell contains exactly 2 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.e74ccc395b24 from=translated src=- shape=840a436c vocab=5730773d
-/
theorem card_zero_lightLight : (wordsIn .zero .lightLight).card = 2 := by decide
/-- The preserving lightHeavy inventory cell contains exactly 4 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.4c8227a10cce from=translated src=- shape=840a436c vocab=06fa54e3
-/
theorem card_zero_lightHeavy : (wordsIn .zero .lightHeavy).card = 4 := by decide
/-- The preserving heavyHeavy inventory cell contains exactly 2 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.4884d683c020 from=translated src=- shape=840a436c vocab=862a837b
-/
theorem card_zero_heavyHeavy : (wordsIn .zero .heavyHeavy).card = 2 := by decide
/-- The lowering lightLight inventory cell contains exactly 1 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.f9307247c896 from=translated src=- shape=840a436c vocab=967cd8c3
-/
theorem card_minus_lightLight : (wordsIn .minus .lightLight).card = 1 := by decide
/-- The lowering lightHeavy inventory cell contains exactly 2 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.3cfbe4d2c8dd from=translated src=- shape=840a436c vocab=e59c6922
-/
theorem card_minus_lightHeavy : (wordsIn .minus .lightHeavy).card = 2 := by decide
/-- The lowering heavyHeavy inventory cell contains exactly 1 words.
Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.0f462eb9eec9 from=translated src=- shape=840a436c vocab=a64a6cbe
-/
theorem card_minus_heavyHeavy : (wordsIn .minus .heavyHeavy).card = 1 := by decide

/-- Summing the nine inventory cells accounts for all sixteen local products.

Source: ported from `SparseFockFormal.BandInventory`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s6.d71e6865c71a from=translated src=- shape=6bdddd4c vocab=b4561f58
-/
theorem nine_cell_count_total :
    (wordsIn .plus .lightLight).card +
      (wordsIn .plus .lightHeavy).card +
      (wordsIn .plus .heavyHeavy).card +
      (wordsIn .zero .lightLight).card +
      (wordsIn .zero .lightHeavy).card +
      (wordsIn .zero .heavyHeavy).card +
      (wordsIn .minus .lightLight).card +
      (wordsIn .minus .lightHeavy).card +
    (wordsIn .minus .heavyHeavy).card = 16 := by
  decide

end NLAlib.SparseSketch
