import Tengoku.Seed.Data.Int.CardIntervalMod
import Tengoku.Seed.RingTheory.Coprime.Lemmas
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometry of affine channels in an offset box

This file isolates the finite lattice argument used in Lemma 5.1 of Paper C.
For positive coprime natural numbers `a` and `b`, two integer cells on the
same affine channel

`a * i - b * j = h`

differ by an integer multiple of the primitive direction `(b, a)`.  If both
cells belong to the offset box `{-1, ..., L - 1}²`, distinctness therefore
forces both channel coefficients to be at most `L`.
-/

namespace PaperC

open Finset

/-- The integer offsets `{-1, 0, ..., L - 1}`.-/
def offsetInterval (L : ℕ) : Finset ℤ :=
  Icc (-1) ((L : ℤ) - 1)

/-- The finite square of pairs of offsets used for two starts.-/
def offsetBox (L : ℕ) : Finset (ℤ × ℤ) :=
  offsetInterval L ×ˢ offsetInterval L

/-- The affine channel equation attached to `(a,b,h)`.-/
def OnChannel (a b : ℕ) (h : ℤ) (cell : ℤ × ℤ) : Prop :=
  (a : ℤ) * cell.1 - (b : ℤ) * cell.2 = h

instance instDecidableOnChannel (a b : ℕ) (h : ℤ) (cell : ℤ × ℤ) :
    Decidable (OnChannel a b h cell) := by
  unfold OnChannel
  infer_instance

/-- The cells of the offset box that lie on the channel `(a,b,h)`.-/
def channelCells (L a b : ℕ) (h : ℤ) : Finset (ℤ × ℤ) :=
  (offsetBox L).filter (OnChannel a b h)

/--
@isnad1 id=iff.0h2v.s5.e2fbe48713f9 from=translated src=- shape=6c8a5412 vocab=b6e72040
-/
@[simp]
theorem mem_offsetInterval {L : ℕ} {i : ℤ} :
    i ∈ offsetInterval L ↔ -1 ≤ i ∧ i ≤ (L : ℤ) - 1 := by
  simp [offsetInterval]

/--
@isnad1 id=iff.0h2v.s6.358bf807e983 from=translated src=- shape=7e6d541e vocab=35e8ca60
-/
@[simp]
theorem mem_offsetBox {L : ℕ} {cell : ℤ × ℤ} :
    cell ∈ offsetBox L ↔
      (-1 ≤ cell.1 ∧ cell.1 ≤ (L : ℤ) - 1) ∧
      (-1 ≤ cell.2 ∧ cell.2 ≤ (L : ℤ) - 1) := by
  simp [offsetBox]

/--
@isnad1 id=iff.0h5v.s6.404efee4dd50 from=translated src=- shape=3210ce80 vocab=c2b446a0
-/
@[simp]
theorem mem_channelCells {L a b : ℕ} {h : ℤ} {cell : ℤ × ℤ} :
    cell ∈ channelCells L a b h ↔
      cell ∈ offsetBox L ∧ OnChannel a b h cell := by
  simp [channelCells]

/--
Subtracting the channel equations of two cells eliminates the affine
parameter `h`.
@isnad1 id=eq.2h5v.s6.6191984039f6 from=translated src=- shape=d4552558 vocab=cf40e4dd
-/
theorem channel_difference_identity
    {a b : ℕ} {h : ℤ} {cell₁ cell₂ : ℤ × ℤ}
    (h₁ : OnChannel a b h cell₁)
    (h₂ : OnChannel a b h cell₂) :
    (a : ℤ) * (cell₁.1 - cell₂.1) =
      (b : ℤ) * (cell₁.2 - cell₂.2) := by
  dsimp [OnChannel] at h₁ h₂
  linarith

/--
For coprime coefficients, the difference of two cells on one channel is an
integer multiple of the primitive direction `(b,a)`.
@isnad1 id=ex.5h5v.s6.fb93ed4e0215 from=translated src=- shape=b59d812e vocab=0bff9cd9
-/
theorem channel_difference_eq_multiple
    {a b : ℕ} (_ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {cell₁ cell₂ : ℤ × ℤ}
    (h₁ : OnChannel a b h cell₁)
    (h₂ : OnChannel a b h cell₂) :
    ∃ t : ℤ,
      cell₁.1 - cell₂.1 = (b : ℤ) * t ∧
      cell₁.2 - cell₂.2 = (a : ℤ) * t := by
  have hdiff := channel_difference_identity h₁ h₂
  have hb_mul :
      (b : ℤ) ∣ (a : ℤ) * (cell₁.1 - cell₂.1) := by
    refine ⟨cell₁.2 - cell₂.2, ?_⟩
    exact hdiff
  have hb :
      (b : ℤ) ∣ cell₁.1 - cell₂.1 :=
    hab.symm.isCoprime.dvd_of_dvd_mul_left hb_mul
  obtain ⟨t, ht⟩ := hb
  refine ⟨t, ht, ?_⟩
  have hbcast : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  apply mul_left_cancel₀ hbcast
  calc
    (b : ℤ) * (cell₁.2 - cell₂.2) =
        (a : ℤ) * (cell₁.1 - cell₂.1) := hdiff.symm
    _ = (a : ℤ) * ((b : ℤ) * t) := by rw [ht]
    _ = (b : ℤ) * ((a : ℤ) * t) := by ring

/-- Two offsets in `{-1, ..., L - 1}` differ in absolute value by at most `L`.
@isnad1 id=le.2h3v.s5.ed0a242d7552 from=translated src=- shape=54eacc04 vocab=0bb40fee
-/
theorem abs_sub_le_of_mem_offsetInterval
    {L : ℕ} {i₁ i₂ : ℤ}
    (h₁ : i₁ ∈ offsetInterval L)
    (h₂ : i₂ ∈ offsetInterval L) :
    |i₁ - i₂| ≤ (L : ℤ) := by
  rw [abs_le]
  simp only [mem_offsetInterval] at h₁ h₂
  omega

/--
If two distinct cells of one positive primitive channel lie in the offset
box, then both coefficients are bounded by the side length.
@isnad1 id=and.8h6v.s6.95333cec4ef8 from=translated src=- shape=7cc03e88 vocab=0265d8c6
-/
theorem channel_coefficients_le_length
    {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {cell₁ cell₂ : ℤ × ℤ}
    (hbox₁ : cell₁ ∈ offsetBox L)
    (hbox₂ : cell₂ ∈ offsetBox L)
    (h₁ : OnChannel a b h cell₁)
    (h₂ : OnChannel a b h cell₂)
    (hne : cell₁ ≠ cell₂) :
    a ≤ L ∧ b ≤ L := by
  obtain ⟨t, hfirst, hsecond⟩ :=
    channel_difference_eq_multiple ha hb hab h₁ h₂
  have ht : t ≠ 0 := by
    intro htzero
    apply hne
    apply Prod.ext
    · have : cell₁.1 - cell₂.1 = 0 := by simpa [htzero] using hfirst
      omega
    · have : cell₁.2 - cell₂.2 = 0 := by simpa [htzero] using hsecond
      omega
  have ht_abs : (1 : ℤ) ≤ |t| := (Int.one_le_abs ht)
  have ha_nonneg : (0 : ℤ) ≤ (a : ℤ) := by positivity
  have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have hcoord₁ :
      |cell₁.1 - cell₂.1| ≤ (L : ℤ) :=
    abs_sub_le_of_mem_offsetInterval
      (by simpa [offsetBox] using (mem_product.mp hbox₁).1)
      (by simpa [offsetBox] using (mem_product.mp hbox₂).1)
  have hcoord₂ :
      |cell₁.2 - cell₂.2| ≤ (L : ℤ) :=
    abs_sub_le_of_mem_offsetInterval
      (by simpa [offsetBox] using (mem_product.mp hbox₁).2)
      (by simpa [offsetBox] using (mem_product.mp hbox₂).2)
  have hb_le : (b : ℤ) ≤ (L : ℤ) := by
    calc
      (b : ℤ) = (b : ℤ) * 1 := by ring
      _ ≤ (b : ℤ) * |t| := mul_le_mul_of_nonneg_left ht_abs hb_nonneg
      _ = |(b : ℤ) * t| := by simp [abs_mul, abs_of_nonneg hb_nonneg]
      _ = |cell₁.1 - cell₂.1| := by rw [hfirst]
      _ ≤ (L : ℤ) := hcoord₁
  have ha_le : (a : ℤ) ≤ (L : ℤ) := by
    calc
      (a : ℤ) = (a : ℤ) * 1 := by ring
      _ ≤ (a : ℤ) * |t| := mul_le_mul_of_nonneg_left ht_abs ha_nonneg
      _ = |(a : ℤ) * t| := by simp [abs_mul, abs_of_nonneg ha_nonneg]
      _ = |cell₁.2 - cell₂.2| := by rw [hsecond]
      _ ≤ (L : ℤ) := hcoord₂
  exact ⟨by exact_mod_cast ha_le, by exact_mod_cast hb_le⟩

/--
Finite-set wrapper of `channel_coefficients_le_length`: a channel containing
two distinct cells of `channelCells` has `a,b ≤ L`.
@isnad1 id=and.6h6v.s6.231a0de446fc from=translated src=- shape=f85e5ba5 vocab=ccefefe6
-/
theorem channel_coefficients_le_length_of_mem
    {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {cell₁ cell₂ : ℤ × ℤ}
    (hmem₁ : cell₁ ∈ channelCells L a b h)
    (hmem₂ : cell₂ ∈ channelCells L a b h)
    (hne : cell₁ ≠ cell₂) :
    a ≤ L ∧ b ≤ L := by
  rw [mem_channelCells] at hmem₁ hmem₂
  exact channel_coefficients_le_length ha hb hab
    hmem₁.1 hmem₂.1 hmem₁.2 hmem₂.2 hne

end PaperC
