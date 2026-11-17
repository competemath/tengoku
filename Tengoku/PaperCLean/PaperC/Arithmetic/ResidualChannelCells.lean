import Tengoku.PaperCLean.PaperC.Affine.RationalChannelCode
import Tengoku.PaperCLean.PaperC.Arithmetic.ChannelCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residual cells attached to an affine channel

For a channel

`a * i - b * j = h`,

the residual expression at a cell is

`Δ = h + b * j - a * i`.

Thus exact channel cells are precisely the zeroes of `Δ`.  A residual
`p`-cell is a cell in the offset box for which `Δ` is nonzero and divisible
by `p`.  This is the finite geometric object counted in Lemma 7.2.

The last part of the file proves the elementary size restriction behind
that count.  Once the channel meets the offset box, comparison with one
exact cell gives

`|Δ| ≤ 2 * max(a,b) * L`.

In particular, for a positive primitive channel containing at least two
exact cells, every prime carried by a residual cell is strictly smaller
than `4 * max(a,b) * (L+1)`.
-/

namespace PaperC

open Finset
open Affine.RationalChannelCode

/-- The signed residual expression `h + b*j - a*i` at an integer cell.-/
def residualChannelExpression
    (a b : ℕ) (h : ℤ) (cell : ℤ × ℤ) : ℤ :=
  h + (b : ℤ) * cell.2 - (a : ℤ) * cell.1

/--
The residual cells for a modulus `p`: cells in the offset box on which the
residual expression is nonzero and divisible by `p`.-/
def residualPrimeCells
    (L a b p : ℕ) (h : ℤ) : Finset (ℤ × ℤ) :=
  (offsetBox L).filter fun cell =>
    residualChannelExpression a b h cell ≠ 0 ∧
      (p : ℤ) ∣ residualChannelExpression a b h cell

/--
@isnad1 id=iff.0h6v.s6.7e272b46cf5e from=translated src=- shape=60d78142 vocab=cb98d92a
-/
@[simp]
theorem mem_residualPrimeCells
    {L a b p : ℕ} {h : ℤ} {cell : ℤ × ℤ} :
    cell ∈ residualPrimeCells L a b p h ↔
      cell ∈ offsetBox L ∧
        residualChannelExpression a b h cell ≠ 0 ∧
        (p : ℤ) ∣ residualChannelExpression a b h cell := by
  simp [residualPrimeCells]

/-- Exact channel cells are exactly the zeroes of the residual expression.
@isnad1 id=iff.0h4v.s4.ff4f1f69685a from=translated src=- shape=6779f6e7 vocab=4cbeb3b1
-/
@[simp]
theorem residualChannelExpression_eq_zero_iff
    {a b : ℕ} {h : ℤ} {cell : ℤ × ℤ} :
    residualChannelExpression a b h cell = 0 ↔
      OnChannel a b h cell := by
  unfold residualChannelExpression OnChannel
  constructor <;> intro hcell <;> linarith

/-- Residual cells are, in particular, not exact channel cells.
@isnad1 id=not.1h6v.s5.d4b74b8cb680 from=translated src=- shape=e3d90f1d vocab=42693a4b
-/
theorem not_onChannel_of_mem_residualPrimeCells
    {L a b p : ℕ} {h : ℤ} {cell : ℤ × ℤ}
    (hcell : cell ∈ residualPrimeCells L a b p h) :
    ¬OnChannel a b h cell := by
  rw [← residualChannelExpression_eq_zero_iff]
  exact (mem_residualPrimeCells.mp hcell).2.1

/-! ## Complete-start vertex form -/

/--
The same residual expression in complete-start vertex coordinates.  The
vertex `v` represents the signed offset `v-1`.-/
def residualVertexExpression
    {L : ℕ} (a b : ℕ) (h : ℤ)
    (cell : Fin (L + 1) × Fin (L + 1)) : ℤ :=
  residualChannelExpression a b h
    (channelVertexOffset cell.1, channelVertexOffset cell.2)

/--
@isnad1 id=eq.0h5v.s7.0f45a980a932 from=translated src=- shape=4e35b2be vocab=1860a666
-/
@[simp]
theorem residualVertexExpression_apply
    {L a b : ℕ} {h : ℤ}
    {cell : Fin (L + 1) × Fin (L + 1)} :
    residualVertexExpression a b h cell =
      h + (b : ℤ) * channelVertexOffset cell.2 -
        (a : ℤ) * channelVertexOffset cell.1 := by
  rfl

/-- Vertex-coordinate residual cells for one modulus.-/
def residualVertexPrimeCells
    (L a b p : ℕ) (h : ℤ) :
    Finset (Fin (L + 1) × Fin (L + 1)) :=
  Finset.univ.filter fun cell =>
    residualVertexExpression a b h cell ≠ 0 ∧
      (p : ℤ) ∣ residualVertexExpression a b h cell

/--
@isnad1 id=iff.0h6v.s7.d5cef5b9e50b from=translated src=- shape=5ae4130b vocab=caf7e17d
-/
@[simp]
theorem mem_residualVertexPrimeCells
    {L a b p : ℕ} {h : ℤ}
    {cell : Fin (L + 1) × Fin (L + 1)} :
    cell ∈ residualVertexPrimeCells L a b p h ↔
      residualVertexExpression a b h cell ≠ 0 ∧
        (p : ℤ) ∣ residualVertexExpression a b h cell := by
  simp [residualVertexPrimeCells]

/--
The complete-start vertex definition is the pullback of the integer-box
definition along the signed-offset map.
@isnad1 id=iff.0h6v.s8.f9bdf759250e from=translated src=- shape=403b8e9e vocab=6b2d8de8
-/
theorem mem_residualVertexPrimeCells_iff_offsets_mem
    {L a b p : ℕ} {h : ℤ}
    {cell : Fin (L + 1) × Fin (L + 1)} :
    cell ∈ residualVertexPrimeCells L a b p h ↔
      (channelVertexOffset cell.1, channelVertexOffset cell.2) ∈
        residualPrimeCells L a b p h := by
  rw [mem_residualVertexPrimeCells, mem_residualPrimeCells]
  constructor
  · intro hres
    refine ⟨?_, hres⟩
    rw [mem_offsetBox]
    exact ⟨
      (by
        simpa only [mem_offsetInterval] using
          channelVertexOffset_mem_offsetInterval cell.1),
      (by
        simpa only [mem_offsetInterval] using
          channelVertexOffset_mem_offsetInterval cell.2)⟩
  · exact fun hres => hres.2

/-! ## Quantitative support of the residual cells -/

/--
Comparison with one exact cell bounds the residual expression everywhere
in the offset box.  This stronger form only assumes that the channel is
nonempty; positivity and primitivity are not needed for this elementary
estimate.
@isnad1 id=le.2h5v.s6.b287b7cc9e1b from=translated src=- shape=ac4f7214 vocab=89e68acb
-/
theorem abs_residualChannelExpression_le
    {L a b : ℕ} {h : ℤ}
    (hnonempty : (channelCells L a b h).Nonempty)
    {cell : ℤ × ℤ} (hcell : cell ∈ offsetBox L) :
    |residualChannelExpression a b h cell| ≤
      2 * (Nat.max a b : ℤ) * (L : ℤ) := by
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  have hbox₀ := (mem_channelCells.mp hcell₀).1
  have hexact := (mem_channelCells.mp hcell₀).2
  have hfirst :
      |cell.1 - cell₀.1| ≤ (L : ℤ) :=
    abs_sub_le_of_mem_offsetInterval
      (by
        simpa only [mem_offsetInterval] using
          (mem_offsetBox.mp hcell).1)
      (by
        simpa only [mem_offsetInterval] using
          (mem_offsetBox.mp hbox₀).1)
  have hsecond :
      |cell.2 - cell₀.2| ≤ (L : ℤ) :=
    abs_sub_le_of_mem_offsetInterval
      (by
        simpa only [mem_offsetInterval] using
          (mem_offsetBox.mp hcell).2)
      (by
        simpa only [mem_offsetInterval] using
          (mem_offsetBox.mp hbox₀).2)
  have haMax : (a : ℤ) ≤ (Nat.max a b : ℤ) := by
    exact_mod_cast Nat.le_max_left a b
  have hbMax : (b : ℤ) ≤ (Nat.max a b : ℤ) := by
    exact_mod_cast Nat.le_max_right a b
  have haNonneg : (0 : ℤ) ≤ (a : ℤ) := by positivity
  have hbNonneg : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have hmaxNonneg : (0 : ℤ) ≤ (Nat.max a b : ℤ) := by positivity
  have hLNonneg : (0 : ℤ) ≤ (L : ℤ) := by positivity
  have hexpression :
      residualChannelExpression a b h cell =
        (b : ℤ) * (cell.2 - cell₀.2) -
          (a : ℤ) * (cell.1 - cell₀.1) := by
    unfold residualChannelExpression OnChannel at *
    linarith
  rw [hexpression]
  calc
    |(b : ℤ) * (cell.2 - cell₀.2) -
        (a : ℤ) * (cell.1 - cell₀.1)| ≤
        |(b : ℤ) * (cell.2 - cell₀.2)| +
          |(a : ℤ) * (cell.1 - cell₀.1)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                ((b : ℤ) * (cell.2 - cell₀.2))
                (-((a : ℤ) * (cell.1 - cell₀.1))))
    _ = (b : ℤ) * |cell.2 - cell₀.2| +
          (a : ℤ) * |cell.1 - cell₀.1| := by
            simp [abs_mul, abs_of_nonneg haNonneg,
              abs_of_nonneg hbNonneg]
    _ ≤ (b : ℤ) * (L : ℤ) + (a : ℤ) * (L : ℤ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsecond hbNonneg)
        (mul_le_mul_of_nonneg_left hfirst haNonneg)
    _ ≤ (Nat.max a b : ℤ) * (L : ℤ) +
          (Nat.max a b : ℤ) * (L : ℤ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hbMax hLNonneg)
        (mul_le_mul_of_nonneg_right haMax hLNonneg)
    _ = 2 * (Nat.max a b : ℤ) * (L : ℤ) := by ring

/--
Manuscript-facing strict bound under the hypotheses of Lemma 7.2: the
channel is positive, primitive, and contains at least two exact cells.
@isnad1 id=lt.5h5v.s7.63533326303b from=translated src=- shape=c857f58f vocab=143bfe08
-/
theorem abs_residualChannelExpression_lt_four_mul_max
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (_hb : 0 < b) (_hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    {cell : ℤ × ℤ} (hcell : cell ∈ offsetBox L) :
    |residualChannelExpression a b h cell| <
      ((4 * Nat.max a b * (L + 1) : ℕ) : ℤ) := by
  have hnonempty : (channelCells L a b h).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hbound :=
    abs_residualChannelExpression_le hnonempty hcell
  have hmaxPos : 0 < Nat.max a b :=
    lt_of_lt_of_le ha (Nat.le_max_left a b)
  have hstrict :
      2 * Nat.max a b * L <
        4 * Nat.max a b * (L + 1) := by
    nlinarith
  have hstrictInt :
      (2 * (Nat.max a b : ℤ) * (L : ℤ)) <
        ((4 * Nat.max a b * (L + 1) : ℕ) : ℤ) := by
    exact_mod_cast hstrict
  exact hbound.trans_lt hstrictInt

/--
Every prime occurring in a residual cell is supported below the explicit
geometric cutoff `4 * max(a,b) * (L+1)`.
@isnad1 id=lt.6h6v.s6.4d823834ba1f from=translated src=- shape=da870b70 vocab=063acc18
-/
theorem prime_lt_four_mul_max_of_mem_residualPrimeCells
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    {cell : ℤ × ℤ}
    (hcell : cell ∈ residualPrimeCells L a b p h)
    (_hp : p.Prime) :
    p < 4 * Nat.max a b * (L + 1) := by
  have hmem := mem_residualPrimeCells.mp hcell
  have hpLe :
      p ≤ Int.natAbs (residualChannelExpression a b h cell) := by
    exact Int.natAbs_le_of_dvd_ne_zero hmem.2.2 hmem.2.1
  have habs :=
    abs_residualChannelExpression_lt_four_mul_max
      ha hb hab hm hmem.1
  have hnatAbs :
      Int.natAbs (residualChannelExpression a b h cell) <
        4 * Nat.max a b * (L + 1) := by
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  exact hpLe.trans_lt hnatAbs

/-- Vertex-coordinate version of the prime-support cutoff.
@isnad1 id=lt.6h6v.s8.96592d688613 from=translated src=- shape=5b88a061 vocab=5fe02d99
-/
theorem prime_lt_four_mul_max_of_mem_residualVertexPrimeCells
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    {cell : Fin (L + 1) × Fin (L + 1)}
    (hcell : cell ∈ residualVertexPrimeCells L a b p h)
    (hp : p.Prime) :
    p < 4 * Nat.max a b * (L + 1) := by
  apply prime_lt_four_mul_max_of_mem_residualPrimeCells
      ha hb hab hm
      (cell :=
        (channelVertexOffset cell.1, channelVertexOffset cell.2))
      (p := p)
  · exact
      mem_residualVertexPrimeCells_iff_offsets_mem.mp hcell
  · exact hp

end PaperC
