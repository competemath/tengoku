import Tengoku.PaperCLean.PaperC.Affine.CanonicalRationalCode
import Tengoku.PaperCLean.PaperC.Analysis.RelationalInterpolation
import Tengoku.PaperCLean.PaperC.Arithmetic.RationalMassFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000

/-!
# Finite geometry on a bounded-ratio interval

This module isolates the genuinely new finite geometry used when Section 17
replaces the dyadic block `[N,2N)` by an integer interval

`U(N,M) = [N,M)`.

The hypotheses `2*N ≤ M ≤ κ₀*N` are the exact integral encoding of a ratio
between two and the fixed upper bound `κ₀`.  No real-valued endpoint and no
rounding convention enter the definitions.

The main results are:

* the exact cardinality and a finite dyadic cover of `U(N,M)`;
* residue-class counts in `U(N,M)`;
* the primitive translation parameter of a rational channel;
* the explicit count `1 + (M-N)/max(a,b)` on one channel;
* a separate, volumetric treatment of height two;
* a finite canonical rational-mass estimate separating `q=2` from `q≥3`.

The last item is the finite combinatorial core of Lemma 17.5.  In particular,
the height-two contribution is proportional to the width of `U`, rather than
to a boundary rectangle as it is in one dyadic block.
-/

namespace PaperC
namespace BoundedRatioGeometry

open scoped BigOperators
open Finset
open Affine
open Affine.CanonicalRationalCode

noncomputable section

/-! ## The interval `U(N,M)` -/

/-- The exact integer interval used for bounded-ratio starts.-/
def boundedRatioBlock (N M : ℕ) : Finset ℕ :=
  Ico N M

/--
@isnad1 id=iff.0h3v.s5.730367c3a11a from=translated src=- shape=c64d9c17 vocab=d753a3cc
-/
@[simp]
theorem mem_boundedRatioBlock {N M x : ℕ} :
    x ∈ boundedRatioBlock N M ↔ N ≤ x ∧ x < M := by
  simp [boundedRatioBlock]

/-- Exact width of the bounded-ratio interval.
@isnad1 id=eq.0h2v.s4.80bdca385734 from=translated src=- shape=40450ec6 vocab=9c4c2efb
-/
@[simp]
theorem card_boundedRatioBlock (N M : ℕ) :
    (boundedRatioBlock N M).card = M - N := by
  simp [boundedRatioBlock]

/-- Under `M ≤ κ₀N`, the interval contains at most `κ₀N` starts.
@isnad1 id=le.1h3v.s5.c8ffd39bf7b9 from=translated src=- shape=c09f4116 vocab=3948a7fa
-/
theorem card_boundedRatioBlock_le
    {N M κ₀ : ℕ} (hM : M ≤ κ₀ * N) :
    (boundedRatioBlock N M).card ≤ κ₀ * N := by
  rw [card_boundedRatioBlock]
  exact (Nat.sub_le M N).trans hM

/-- Ordered pairs of bounded-ratio starts.-/
def boundedRatioPairs (N M : ℕ) : Finset (ℕ × ℕ) :=
  boundedRatioBlock N M ×ˢ boundedRatioBlock N M

/--
@isnad1 id=iff.0h4v.s5.5827dd3154b2 from=translated src=- shape=1b83cfd6 vocab=50ee90af
-/
@[simp]
theorem mem_boundedRatioPairs {N M x y : ℕ} :
    (x, y) ∈ boundedRatioPairs N M ↔
      N ≤ x ∧ x < M ∧ N ≤ y ∧ y < M := by
  simp [boundedRatioPairs, and_assoc]

/-- Exact ambient pair count, the finite form of replacement R1.
@isnad1 id=eq.0h2v.s5.49ee90878411 from=translated src=- shape=84287e17 vocab=25647454
-/
@[simp]
theorem card_boundedRatioPairs (N M : ℕ) :
    (boundedRatioPairs N M).card = (M - N) ^ 2 := by
  simp [boundedRatioPairs, pow_two]

/-- Coarse pair count uniform under the fixed ratio bound.
@isnad1 id=le.1h3v.s5.27e3caf81ab5 from=translated src=- shape=09333d76 vocab=e5f59607
-/
theorem card_boundedRatioPairs_le
    {N M κ₀ : ℕ} (hM : M ≤ κ₀ * N) :
    (boundedRatioPairs N M).card ≤ (κ₀ * N) ^ 2 := by
  rw [card_boundedRatioPairs]
  exact Nat.pow_le_pow_left
    ((Nat.sub_le M N).trans hM) 2

/-- Ordered separated pairs in `U(N,M)²`.-/
def separatedBoundedRatioPairs (N M L : ℕ) : Finset (ℕ × ℕ) :=
  (boundedRatioPairs N M).filter fun pair =>
    L < Nat.dist pair.1 pair.2

/--
@isnad1 id=iff.0h5v.s6.81a98cc4faff from=translated src=- shape=87be30bd vocab=2f8687fc
-/
@[simp]
theorem mem_separatedBoundedRatioPairs
    {N M L x y : ℕ} :
    (x, y) ∈ separatedBoundedRatioPairs N M L ↔
      x ∈ boundedRatioBlock N M ∧
      y ∈ boundedRatioBlock N M ∧
      L < Nat.dist x y := by
  simp [separatedBoundedRatioPairs, boundedRatioPairs, and_assoc]

/--
@isnad1 id=le.0h3v.s5.4c8e021a02a2 from=translated src=- shape=87c5ec95 vocab=54dd53cb
-/
theorem card_separatedBoundedRatioPairs_le
    (N M L : ℕ) :
    (separatedBoundedRatioPairs N M L).card ≤ (M - N) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans_eq
    (card_boundedRatioPairs N M)

/-! ## A finite dyadic cover -/

/-- The `r`-th dyadic shell based at `N`.-/
def dyadicShell (N r : ℕ) : Finset ℕ :=
  Ico (2 ^ r * N) (2 ^ (r + 1) * N)

/--
@isnad1 id=iff.0h3v.s6.22142bb4dbab from=translated src=- shape=68229c96 vocab=f5ab5718
-/
@[simp]
theorem mem_dyadicShell {N r x : ℕ} :
    x ∈ dyadicShell N r ↔
      2 ^ r * N ≤ x ∧ x < 2 ^ (r + 1) * N := by
  simp [dyadicShell]

/-- The part of the `r`-th shell lying in `U(N,M)`.-/
def boundedDyadicShell (N M r : ℕ) : Finset ℕ :=
  boundedRatioBlock N M ∩ dyadicShell N r

/--
@isnad1 id=iff.0h4v.s6.0e602209ae01 from=translated src=- shape=f1b09546 vocab=5f5814f0
-/
@[simp]
theorem mem_boundedDyadicShell {N M r x : ℕ} :
    x ∈ boundedDyadicShell N M r ↔
      N ≤ x ∧ x < M ∧
      2 ^ r * N ≤ x ∧ x < 2 ^ (r + 1) * N := by
  simp [boundedDyadicShell, and_assoc]

/-- Union of the first `J` shells, clipped to `U(N,M)`.-/
def boundedDyadicCover (N M J : ℕ) : Finset ℕ :=
  (Finset.range J).biUnion fun r => boundedDyadicShell N M r

/--
Any point between `N` and `2^J N` belongs to one of the first `J` dyadic
shells.  The induction avoids any convention about integer logarithms.
@isnad1 id=ex.2h3v.s6.e51fbe3ed9c6 from=translated src=- shape=2eb5d11a vocab=b05406d2
-/
theorem exists_mem_dyadicShell
    {N J x : ℕ}
    (hxLower : N ≤ x)
    (hxUpper : x < 2 ^ J * N) :
    ∃ r < J, x ∈ dyadicShell N r := by
  induction J with
  | zero =>
      simp only [pow_zero, one_mul] at hxUpper
      omega
  | succ J ih =>
      by_cases hx : x < 2 ^ J * N
      · obtain ⟨r, hrJ, hr⟩ := ih hx
        exact ⟨r, Nat.lt_succ_of_lt hrJ, hr⟩
      · refine ⟨J, Nat.lt_succ_self J, ?_⟩
        rw [mem_dyadicShell]
        constructor
        · omega
        · simpa [Nat.succ_eq_add_one] using hxUpper

/-- Elementary fixed-parameter bound `κ₀ ≤ 2^κ₀`.
@isnad1 id=le.0h1v.s4.7a35469a2be0 from=translated src=- shape=e17d9afa vocab=74f5fafa
-/
theorem self_le_two_pow (κ₀ : ℕ) :
    κ₀ ≤ 2 ^ κ₀ := by
  induction κ₀ with
  | zero => simp
  | succ κ₀ ih =>
      have hpow : 1 ≤ 2 ^ κ₀ :=
        Nat.one_le_pow κ₀ 2 (by omega)
      rw [pow_succ]
      omega

/--
The first `κ₀` dyadic shells cover `U(N,M)` whenever `M ≤ κ₀N`.
The sharper logarithmic number of shells from the manuscript is unnecessary
for finiteness: `κ₀` is fixed before `N`, and this bound is uniform in `M`.
@isnad1 id=eq.3h3v.s5.993c6dbc43d6 from=translated src=- shape=ed4fe0bf vocab=0288b8f7
-/
theorem boundedDyadicCover_eq
    {N M κ₀ : ℕ}
    (hN : 0 < N) (hκ₀ : 1 ≤ κ₀)
    (hM : M ≤ κ₀ * N) :
    boundedDyadicCover N M κ₀ = boundedRatioBlock N M := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [boundedDyadicCover, Finset.mem_biUnion] at hx
    obtain ⟨r, _hr, hx⟩ := hx
    exact (Finset.mem_inter.mp hx).1
  · intro x hx
    have hxData := mem_boundedRatioBlock.mp hx
    have hκPow : κ₀ * N ≤ 2 ^ κ₀ * N :=
      Nat.mul_le_mul_right N (self_le_two_pow κ₀)
    have hxUpper : x < 2 ^ κ₀ * N :=
      hxData.2.trans_le (hM.trans hκPow)
    obtain ⟨r, hrκ, hr⟩ :=
      exists_mem_dyadicShell hxData.1 hxUpper
    rw [boundedDyadicCover, Finset.mem_biUnion]
    exact ⟨r, Finset.mem_range.mpr hrκ,
      Finset.mem_inter.mpr ⟨hx, hr⟩⟩

/--
The bounded interval is thus covered by at most `κ₀` ordinary dyadic blocks,
each based at the scale `2^r N`.
@isnad1 id=le.3h3v.s6.5a939f7847c2 from=translated src=- shape=1aa28915 vocab=fe7b2872
-/
theorem boundedRatioBlock_subset_dyadic_union
    {N M κ₀ : ℕ}
    (hN : 0 < N) (hκ₀ : 1 ≤ κ₀)
    (hM : M ≤ κ₀ * N) :
    boundedRatioBlock N M ⊆
      (Finset.range κ₀).biUnion fun r => dyadicShell N r := by
  intro x hx
  have hxData := mem_boundedRatioBlock.mp hx
  have hκPow : κ₀ * N ≤ 2 ^ κ₀ * N :=
    Nat.mul_le_mul_right N (self_le_two_pow κ₀)
  have hxUpper : x < 2 ^ κ₀ * N :=
    hxData.2.trans_le (hM.trans hκPow)
  obtain ⟨r, hrκ, hr⟩ :=
    exists_mem_dyadicShell hxData.1 hxUpper
  exact Finset.mem_biUnion.mpr
    ⟨r, Finset.mem_range.mpr hrκ, hr⟩

/-! ## Residue classes in `U(N,M)` -/

/--
One residue class modulo `q` has at most `1 + (M-N)/q` representatives in
`U(N,M)`.
@isnad1 id=le.2h4v.s6.a03364d02c2a from=translated src=- shape=a67a441a vocab=dadd949e
-/
theorem card_boundedRatioBlock_modClass_le_one_add_div
    (N M v q : ℕ) (hq : 0 < q) (hNM : N ≤ M) :
    {x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card ≤
      1 + (M - N) / q := by
  have hcast :=
    congrArg Finset.card
      (Nat.Ico_filter_modEq_cast
        N M (r := q) (v := v))
  have hcardEq :
      {x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card =
        {x ∈ Ico (N : ℤ) (M : ℤ) |
          x ≡ (v : ℤ) [ZMOD (q : ℤ)]}.card := by
    simpa [boundedRatioBlock] using hcast
  have hcount :=
    card_Ico_modEq_le_ceil_length
      (N : ℤ) (M : ℤ) (v : ℤ) (q : ℤ)
      (by exact_mod_cast hq) (by exact_mod_cast hNM)
  let D := M - N
  have hdivision :
      D ≤ (D / q + 1) * q := by
    have hstrict := Nat.lt_div_mul_add (a := D) hq
    have hstrict' : D < (D / q + 1) * q := by
      simpa [Nat.add_mul] using hstrict
    exact hstrict'.le
  have hquotient :
      (D : ℚ) / (q : ℚ) ≤ (D / q + 1 : ℕ) := by
    apply (div_le_iff₀ (by exact_mod_cast hq)).2
    exact_mod_cast hdivision
  have hdiff :
      (((((M : ℤ) - (N : ℤ)) : ℤ) : ℚ)) = (D : ℚ) := by
    dsimp [D]
    norm_num only [Int.cast_sub, Int.cast_natCast]
    rw [Nat.cast_sub hNM]
  have hceil :
      ⌈(((((M : ℤ) - (N : ℤ)) : ℤ) : ℚ) /
          (q : ℚ))⌉ ≤
        ((D / q + 1 : ℕ) : ℤ) := by
    apply Int.ceil_le.mpr
    rw [hdiff]
    exact hquotient
  have hcardInt :
      ({x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card : ℤ) ≤
        ((D / q + 1 : ℕ) : ℤ) := by
    rw [hcardEq]
    exact hcount.trans hceil
  have hcardNat :
      {x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card ≤
        D / q + 1 := by
    exact_mod_cast hcardInt
  simpa [D, Nat.add_comm] using hcardNat

/--
Rational-valued interval estimate, convenient when a later analytic bound
keeps the quotient rather than taking its integer floor.
@isnad1 id=le.2h4v.s6.c4008ae19d48 from=translated src=- shape=3d70ae81 vocab=9d6dc849
-/
theorem card_boundedRatioBlock_modClass_cast_le
    (N M v q : ℕ) (hq : 0 < q) (hNM : N ≤ M) :
    (({x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card : ℕ) : ℚ) ≤
      ((M - N : ℕ) : ℚ) / (q : ℚ) + 1 := by
  have hbase :=
    card_nat_Ico_modEq_cast_le_div_add_one N M v q hq hNM
  simpa [boundedRatioBlock, Nat.cast_sub hNM] using hbase

/--
The interval count with a fixed ratio upper bound substituted into the
numerator.
@isnad1 id=le.3h5v.s6.ad2d0b955dcd from=translated src=- shape=0c3568e6 vocab=dcb5cc69
-/
theorem card_boundedRatioBlock_modClass_cast_le_kappa
    {N M v q κ₀ : ℕ}
    (hq : 0 < q) (hNM : N ≤ M) (hM : M ≤ κ₀ * N) :
    (({x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card : ℕ) : ℚ) ≤
      (((κ₀ * N : ℕ) : ℚ) / (q : ℚ)) + 1 := by
  calc
    (({x ∈ boundedRatioBlock N M | x ≡ v [MOD q]}.card : ℕ) : ℚ) ≤
        ((M - N : ℕ) : ℚ) / (q : ℚ) + 1 :=
      card_boundedRatioBlock_modClass_cast_le N M v q hq hNM
    _ ≤ (((κ₀ * N : ℕ) : ℚ) / (q : ℚ)) + 1 := by
      apply add_le_add_left
      apply (div_le_div_iff_of_pos_right
        (by exact_mod_cast hq : (0 : ℚ) < (q : ℚ))).2
      exact_mod_cast (Nat.sub_le M N).trans hM

/-! ## Exact channels and their translation parameter -/

/-- Start pairs in `U(N,M)²` on one exact channel.-/
def boundedChannelStartPairs
    (N M a b : ℕ) (h : ℤ) : Finset (ℕ × ℕ) :=
  (boundedRatioPairs N M).filter fun pair =>
    pairChannelError pair.1 pair.2 a b = h

/--
@isnad1 id=iff.0h7v.s6.d1062a124063 from=translated src=- shape=883c8a73 vocab=c73b0a6f
-/
@[simp]
theorem mem_boundedChannelStartPairs
    {N M a b x y : ℕ} {h : ℤ} :
    (x, y) ∈ boundedChannelStartPairs N M a b h ↔
      x ∈ boundedRatioBlock N M ∧
      y ∈ boundedRatioBlock N M ∧
      pairChannelError x y a b = h := by
  simp [boundedChannelStartPairs, boundedRatioPairs, and_assoc]

/--
A channel unit and a start pair on the matching affine parameter determine
the manuscript's common translation parameter:

`x + i = b*t`, `y + j = a*t`.
@isnad1 id=ex.5h9v.s7.66be4da3d82f from=translated src=- shape=d610e132 vocab=62fae5f3
-/
theorem exists_channelTranslationParameter
    {N M L a b x y : ℕ} {h : ℤ} {cell : ℤ × ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hpair : (x, y) ∈ boundedChannelStartPairs N M a b h)
    (hcell : cell ∈ channelCells L a b h) :
    ∃ t : ℤ,
      (x : ℤ) + cell.1 = (b : ℤ) * t ∧
      (y : ℤ) + cell.2 = (a : ℤ) * t := by
  have hpairEq :=
    (mem_boundedChannelStartPairs.mp hpair).2.2
  have hcellEq := (mem_channelCells.mp hcell).2
  simp only [pairChannelError, OnChannel] at hpairEq hcellEq
  have heq :
      (b : ℤ) * ((y : ℤ) + cell.2) =
        (a : ℤ) * ((x : ℤ) + cell.1) := by
    linarith
  have hbMul :
      (b : ℤ) ∣ (a : ℤ) * ((x : ℤ) + cell.1) := by
    exact ⟨(y : ℤ) + cell.2, heq.symm⟩
  have hbDiv :
      (b : ℤ) ∣ (x : ℤ) + cell.1 :=
    hab.symm.isCoprime.dvd_of_dvd_mul_left hbMul
  obtain ⟨t, ht⟩ := hbDiv
  refine ⟨t, ht, ?_⟩
  have hb0 : (b : ℤ) ≠ 0 := by
    exact_mod_cast hb.ne'
  apply mul_left_cancel₀ hb0
  calc
    (b : ℤ) * ((y : ℤ) + cell.2) =
        (a : ℤ) * ((x : ℤ) + cell.1) := heq
    _ = (a : ℤ) * ((b : ℤ) * t) := by rw [ht]
    _ = (b : ℤ) * ((a : ℤ) * t) := by ring

/-- The translation parameter is unique once either coefficient is positive.
@isnad1 id=eq.3h6v.s6.af00cdb97785 from=translated src=- shape=6849fb49 vocab=022063a0
-/
theorem channelTranslationParameter_unique
    {a b x : ℕ} {i t₁ t₂ : ℤ}
    (hb : 0 < b)
    (h₁ : (x : ℤ) + i = (b : ℤ) * t₁)
    (h₂ : (x : ℤ) + i = (b : ℤ) * t₂) :
    t₁ = t₂ := by
  have hb0 : (b : ℤ) ≠ 0 := by
    exact_mod_cast hb.ne'
  apply mul_left_cancel₀ hb0
  rw [← h₁, ← h₂]

/--
The common parameter is confined simultaneously by both start coordinates.
This is the division-free form of replacement R4.
@isnad1 id=and.5h9v.s8.1ee0aee85307 from=translated src=- shape=4f18281b vocab=591d9ed3
-/
theorem channelTranslationParameter_bounds
    {N M L a b x y : ℕ} {cell : ℤ × ℤ} {t : ℤ}
    (hx : x ∈ boundedRatioBlock N M)
    (hy : y ∈ boundedRatioBlock N M)
    (hcell : cell ∈ offsetBox L)
    (htx : (x : ℤ) + cell.1 = (b : ℤ) * t)
    (hty : (y : ℤ) + cell.2 = (a : ℤ) * t) :
    (N : ℤ) - 1 ≤ (b : ℤ) * t ∧
      (b : ℤ) * t < (M : ℤ) + L ∧
      (N : ℤ) - 1 ≤ (a : ℤ) * t ∧
      (a : ℤ) * t < (M : ℤ) + L := by
  have hxData := mem_boundedRatioBlock.mp hx
  have hyData := mem_boundedRatioBlock.mp hy
  have hbox := mem_offsetBox.mp hcell
  rw [← htx, ← hty]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-! ## Counting one exact channel in `U(N,M)²` -/

/-- First-coordinate projection of bounded-ratio channel pairs.-/
def boundedChannelFirstCoordinates
    (N M a b : ℕ) (h : ℤ) : Finset ℕ :=
  (boundedChannelStartPairs N M a b h).image Prod.fst

/-- Second-coordinate projection of bounded-ratio channel pairs.-/
def boundedChannelSecondCoordinates
    (N M a b : ℕ) (h : ℤ) : Finset ℕ :=
  (boundedChannelStartPairs N M a b h).image Prod.snd

/-- For `b>0`, the first start determines the second on an exact channel.
@isnad1 id=injon.1h5v.s5.9615de181fc7 from=translated src=- shape=9cacf403 vocab=602d83d9
-/
theorem fst_injOn_boundedChannelStartPairs
    {N M a b : ℕ} (hb : 0 < b) {h : ℤ} :
    Set.InjOn Prod.fst
      (↑(boundedChannelStartPairs N M a b h) : Set (ℕ × ℕ)) := by
  intro pair₁ hpair₁ pair₂ hpair₂ hfst
  apply Prod.ext hfst
  have herr₁ :=
    (mem_boundedChannelStartPairs.mp hpair₁).2.2
  have herr₂ :=
    (mem_boundedChannelStartPairs.mp hpair₂).2.2
  simp only [pairChannelError] at herr₁ herr₂
  have hzero :
      (b : ℤ) * ((pair₁.2 : ℤ) - (pair₂.2 : ℤ)) = 0 := by
    rw [hfst] at herr₁
    linarith
  have hb0 : (b : ℤ) ≠ 0 := by
    exact_mod_cast hb.ne'
  have hy :
      (pair₁.2 : ℤ) - (pair₂.2 : ℤ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hb0
  exact_mod_cast (sub_eq_zero.mp hy)

/-- For `a>0`, the second start determines the first on an exact channel.
@isnad1 id=injon.1h5v.s5.682b9a7aa20d from=translated src=- shape=1914617f vocab=5c1a8c95
-/
theorem snd_injOn_boundedChannelStartPairs
    {N M a b : ℕ} (ha : 0 < a) {h : ℤ} :
    Set.InjOn Prod.snd
      (↑(boundedChannelStartPairs N M a b h) : Set (ℕ × ℕ)) := by
  intro pair₁ hpair₁ pair₂ hpair₂ hsnd
  apply Prod.ext
  · have herr₁ :=
      (mem_boundedChannelStartPairs.mp hpair₁).2.2
    have herr₂ :=
      (mem_boundedChannelStartPairs.mp hpair₂).2.2
    simp only [pairChannelError] at herr₁ herr₂
    have hzero :
        (a : ℤ) * ((pair₁.1 : ℤ) - (pair₂.1 : ℤ)) = 0 := by
      rw [hsnd] at herr₁
      linarith
    have ha0 : (a : ℤ) ≠ 0 := by
      exact_mod_cast ha.ne'
    have hx :
        (pair₁.1 : ℤ) - (pair₂.1 : ℤ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left ha0
    exact_mod_cast (sub_eq_zero.mp hx)
  · exact hsnd

/-- First coordinates on one primitive channel occupy one class modulo `b`.
@isnad1 id=le.4h6v.s6.a4c3408b8030 from=translated src=- shape=c0170517 vocab=27d42e00
-/
theorem boundedChannelFirstCoordinates_subset_modClass
    {N M a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {pair₀ : ℕ × ℕ}
    (hpair₀ : pair₀ ∈ boundedChannelStartPairs N M a b h) :
    boundedChannelFirstCoordinates N M a b h ⊆
      {x ∈ boundedRatioBlock N M | x ≡ pair₀.1 [MOD b]} := by
  intro x hx
  rw [boundedChannelFirstCoordinates, mem_image] at hx
  obtain ⟨pair, hpair, rfl⟩ := hx
  have hbox :=
    (mem_boundedChannelStartPairs.mp hpair).1
  have hcongruenceInt :
      (pair.1 : ℤ) ≡ (pair₀.1 : ℤ) [ZMOD (b : ℤ)] := by
    have hOn₁ :
        OnChannel a b (-h) ((pair.1 : ℤ), (pair.2 : ℤ)) := by
      have hp :=
        (mem_boundedChannelStartPairs.mp hpair).2.2
      simp only [OnChannel, pairChannelError] at hp ⊢
      linarith
    have hOn₀ :
        OnChannel a b (-h) ((pair₀.1 : ℤ), (pair₀.2 : ℤ)) := by
      have hp :=
        (mem_boundedChannelStartPairs.mp hpair₀).2.2
      simp only [OnChannel, pairChannelError] at hp ⊢
      linarith
    obtain ⟨t, ht, _⟩ :=
      channel_difference_eq_multiple ha hb hab hOn₁ hOn₀
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [← neg_sub, ht]
    ring
  simp only [mem_filter]
  exact ⟨hbox, Int.natCast_modEq_iff.mp hcongruenceInt⟩

/-- Second coordinates on one primitive channel occupy one class modulo `a`.
@isnad1 id=le.4h6v.s6.87d5e15eb307 from=translated src=- shape=ba08324b vocab=cbaf3504
-/
theorem boundedChannelSecondCoordinates_subset_modClass
    {N M a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {pair₀ : ℕ × ℕ}
    (hpair₀ : pair₀ ∈ boundedChannelStartPairs N M a b h) :
    boundedChannelSecondCoordinates N M a b h ⊆
      {y ∈ boundedRatioBlock N M | y ≡ pair₀.2 [MOD a]} := by
  intro y hy
  rw [boundedChannelSecondCoordinates, mem_image] at hy
  obtain ⟨pair, hpair, rfl⟩ := hy
  have hbox :=
    (mem_boundedChannelStartPairs.mp hpair).2.1
  have hcongruenceInt :
      (pair.2 : ℤ) ≡ (pair₀.2 : ℤ) [ZMOD (a : ℤ)] := by
    have hOn₁ :
        OnChannel a b (-h) ((pair.1 : ℤ), (pair.2 : ℤ)) := by
      have hp :=
        (mem_boundedChannelStartPairs.mp hpair).2.2
      simp only [OnChannel, pairChannelError] at hp ⊢
      linarith
    have hOn₀ :
        OnChannel a b (-h) ((pair₀.1 : ℤ), (pair₀.2 : ℤ)) := by
      have hp :=
        (mem_boundedChannelStartPairs.mp hpair₀).2.2
      simp only [OnChannel, pairChannelError] at hp ⊢
      linarith
    obtain ⟨t, _, ht⟩ :=
      channel_difference_eq_multiple ha hb hab hOn₁ hOn₀
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [← neg_sub, ht]
    ring
  simp only [mem_filter]
  exact ⟨hbox, Int.natCast_modEq_iff.mp hcongruenceInt⟩

/-- Count one channel through its first-coordinate step `b`.
@isnad1 id=le.4h5v.s6.1f0fbbb6f468 from=translated src=- shape=35b628fe vocab=42d25fff
-/
theorem boundedChannelStartPairs_card_le_firstStep
    (N M a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hNM : N ≤ M) (h : ℤ) :
    (boundedChannelStartPairs N M a b h).card ≤
      1 + (M - N) / b := by
  classical
  by_cases hempty : boundedChannelStartPairs N M a b h = ∅
  · simp [hempty]
  · obtain ⟨pair₀, hpair₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (boundedChannelFirstCoordinates N M a b h).card =
          (boundedChannelStartPairs N M a b h).card :=
      card_image_of_injOn
        (fst_injOn_boundedChannelStartPairs hb)
    calc
      (boundedChannelStartPairs N M a b h).card =
          (boundedChannelFirstCoordinates N M a b h).card :=
        hcard.symm
      _ ≤ {x ∈ boundedRatioBlock N M |
            x ≡ pair₀.1 [MOD b]}.card :=
        card_mono
          (boundedChannelFirstCoordinates_subset_modClass
            ha hb hab hpair₀)
      _ ≤ 1 + (M - N) / b :=
        card_boundedRatioBlock_modClass_le_one_add_div
          N M pair₀.1 b hb hNM

/-- Count one channel through its second-coordinate step `a`.
@isnad1 id=le.4h5v.s6.e0ff78d41236 from=translated src=- shape=dd0f2e12 vocab=42d25fff
-/
theorem boundedChannelStartPairs_card_le_secondStep
    (N M a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hNM : N ≤ M) (h : ℤ) :
    (boundedChannelStartPairs N M a b h).card ≤
      1 + (M - N) / a := by
  classical
  by_cases hempty : boundedChannelStartPairs N M a b h = ∅
  · simp [hempty]
  · obtain ⟨pair₀, hpair₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (boundedChannelSecondCoordinates N M a b h).card =
          (boundedChannelStartPairs N M a b h).card :=
      card_image_of_injOn
        (snd_injOn_boundedChannelStartPairs ha)
    calc
      (boundedChannelStartPairs N M a b h).card =
          (boundedChannelSecondCoordinates N M a b h).card :=
        hcard.symm
      _ ≤ {y ∈ boundedRatioBlock N M |
            y ≡ pair₀.2 [MOD a]}.card :=
        card_mono
          (boundedChannelSecondCoordinates_subset_modClass
            ha hb hab hpair₀)
      _ ≤ 1 + (M - N) / a :=
        card_boundedRatioBlock_modClass_le_one_add_div
          N M pair₀.2 a ha hNM

/--
Sharp bounded-ratio channel count with the primitive step
`q=max(a,b)`.
@isnad1 id=le.4h5v.s6.3b050f763b11 from=translated src=- shape=edfd4ab1 vocab=a29f67a2
-/
theorem boundedChannelStartPairs_card_le_maxStep
    (N M a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hNM : N ≤ M) (h : ℤ) :
    (boundedChannelStartPairs N M a b h).card ≤
      1 + (M - N) / Nat.max a b := by
  by_cases habOrder : a ≤ b
  · simpa [Nat.max_eq_right habOrder] using
      boundedChannelStartPairs_card_le_firstStep
        N M a b ha hb hab hNM h
  · have hba : b ≤ a := le_of_not_ge habOrder
    simpa [Nat.max_eq_left hba] using
      boundedChannelStartPairs_card_le_secondStep
        N M a b ha hb hab hNM h

/-! ## Local code and determinant statements (Lemmas 17.3 and 17.4) -/

/--
The code dimension formula is independent of the start interval.  This
wrapper records it at the Section 17 interface.
@isnad1 id=eq.6h9v.s13.d0880664e533 from=translated src=- shape=1931d3b5 vocab=c971233e
-/
theorem boundedRatio_rationalCode_finrank
    {T N M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hN : 2 ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (hy : y ∈ boundedRatioBlock N M)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    Module.finrank F₂
        (RationalChannelCode.rationalCode
          T x y L a b h ha hb
          (hN.trans (mem_boundedRatioBlock.mp hx).1)
          (hN.trans (mem_boundedRatioBlock.mp hy).1)
          hheight) =
      (channelCells L a b h).card - 1 := by
  rw [RationalChannelCode.finrank_rationalCode_all
      ha hb
      (hN.trans (mem_boundedRatioBlock.mp hx).1)
      (hN.trans (mem_boundedRatioBlock.mp hy).1)
      hheight,
    RationalChannelCode.card_rationalChannelUnits_eq_channelCells]

/-- A nonzero local rational code still forces `max(a,b)≤L`.
@isnad1 id=le.4h4v.s5.3078f51b8461 from=translated src=- shape=25694f82 vocab=fbd7e011
-/
theorem boundedRatio_channel_height_le
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card) :
    Nat.max a b ≤ L := by
  obtain ⟨cell₁, hcell₁, cell₂, hcell₂, hne⟩ :=
    Finset.one_lt_card.mp hm
  exact max_le
    (channel_coefficients_le_length_of_mem
      ha hb hab hcell₁ hcell₂ hne).1
    (channel_coefficients_le_length_of_mem
      ha hb hab hcell₁ hcell₂ hne).2

/--
The determinant criterion for uniqueness only consumes the lower endpoint
`x≥N`; hence it transports verbatim to `U(N,M)`.
@isnad1 id=le.2h6v.s6.ac3f5819543a from=translated src=- shape=42e68e3f vocab=077ada0e
-/
theorem boundedRatio_reducedChannelCandidates_card_le_one
    {N M x y B H : ℕ}
    (hx : x ∈ boundedRatioBlock N M)
    (hthreshold : 4 * H ^ 2 * B < N) :
    (reducedChannelCandidates x y B H).card ≤ 1 := by
  exact card_reducedChannelCandidates_le_one
    (hthreshold.trans_le (mem_boundedRatioBlock.mp hx).1)

/-! ## Exact interpolation (Lemma 17.2) -/

/-- Cauchy--Schwarz on any population of bounded-ratio pairs.
@isnad1 id=le.1h4v.s6.2d688f6aa39c from=translated src=- shape=63e016cf vocab=87607e3b
-/
theorem boundedRatio_interpolation
    {N M : ℕ}
    (A : Finset (ℕ × ℕ)) (u : (ℕ × ℕ) → ℝ)
    (_hA : A ⊆ boundedRatioPairs N M) :
    ∑ pair ∈ A, u pair ≤
      Real.sqrt (A.card : ℝ) *
        Real.sqrt (∑ pair ∈ A, (u pair) ^ 2) :=
  RelationalInterpolation.sum_le_sqrt_card_mul_sqrt_sum_sq A u

/-! ## The volumetric height-two family -/

/-- Exact `(2,1)` channels with at least two offset units.-/
def boundedHeightTwoForwardCover
    (N M L : ℕ) : Finset (ℕ × ℕ) :=
  (nontrivialChannelHeights L 2 1).biUnion fun h =>
    boundedChannelStartPairs N M 2 1 h

/-- Exact `(1,2)` channels with at least two offset units.-/
def boundedHeightTwoBackwardCover
    (N M L : ℕ) : Finset (ℕ × ℕ) :=
  (nontrivialChannelHeights L 1 2).biUnion fun h =>
    boundedChannelStartPairs N M 1 2 h

/-- Both primitive orientations of height two.-/
def boundedHeightTwoPairCover
    (N M L : ℕ) : Finset (ℕ × ℕ) :=
  boundedHeightTwoForwardCover N M L ∪
    boundedHeightTwoBackwardCover N M L

/--
@isnad1 id=le.1h3v.s5.3aafa30665f5 from=translated src=- shape=1681203b vocab=865b66a2
-/
theorem nontrivialChannelHeights_card_le_three_mul_add_one
    (L a b : ℕ) (hsum : a + b = 3) :
    (nontrivialChannelHeights L a b).card ≤ 3 * L + 1 := by
  calc
    (nontrivialChannelHeights L a b).card ≤
        (channelHeights L a b).card :=
      Finset.card_filter_le _ _
    _ ≤ (a + b) * L + 1 :=
      channelHeights_card_le L a b
    _ = 3 * L + 1 := by rw [hsum]

/-- One oriented height-two family has the expected `O((3L+1)|U|)` size.
@isnad1 id=le.1h3v.s6.f2dfcf5213a4 from=translated src=- shape=4213a08a vocab=b1073af6
-/
theorem card_boundedHeightTwoForwardCover_le
    {N M L : ℕ} (hNM : N ≤ M) :
    (boundedHeightTwoForwardCover N M L).card ≤
      (3 * L + 1) * (1 + (M - N) / 2) := by
  unfold boundedHeightTwoForwardCover
  let W := 1 + (M - N) / 2
  have hchannel :
      ∀ h ∈ nontrivialChannelHeights L 2 1,
        (boundedChannelStartPairs N M 2 1 h).card ≤ W := by
    intro h _hh
    simpa [W] using
      boundedChannelStartPairs_card_le_maxStep
        N M 2 1 (by omega) (by omega) (by norm_num) hNM h
  have hunion :
      ((nontrivialChannelHeights L 2 1).biUnion fun h =>
          boundedChannelStartPairs N M 2 1 h).card ≤
        (nontrivialChannelHeights L 2 1).card * W :=
    Finset.card_biUnion_le_card_mul
      (nontrivialChannelHeights L 2 1)
      (fun h => boundedChannelStartPairs N M 2 1 h)
      W hchannel
  exact hunion.trans
    (Nat.mul_le_mul_right W
      (nontrivialChannelHeights_card_le_three_mul_add_one
        L 2 1 (by omega)))

/-- The reverse orientation satisfies the same volumetric bound.
@isnad1 id=le.1h3v.s6.0cddbbc618a4 from=translated src=- shape=4213a08a vocab=41fa4903
-/
theorem card_boundedHeightTwoBackwardCover_le
    {N M L : ℕ} (hNM : N ≤ M) :
    (boundedHeightTwoBackwardCover N M L).card ≤
      (3 * L + 1) * (1 + (M - N) / 2) := by
  unfold boundedHeightTwoBackwardCover
  let W := 1 + (M - N) / 2
  have hchannel :
      ∀ h ∈ nontrivialChannelHeights L 1 2,
        (boundedChannelStartPairs N M 1 2 h).card ≤ W := by
    intro h _hh
    simpa [W] using
      boundedChannelStartPairs_card_le_maxStep
        N M 1 2 (by omega) (by omega) (by norm_num) hNM h
  have hunion :
      ((nontrivialChannelHeights L 1 2).biUnion fun h =>
          boundedChannelStartPairs N M 1 2 h).card ≤
        (nontrivialChannelHeights L 1 2).card * W :=
    Finset.card_biUnion_le_card_mul
      (nontrivialChannelHeights L 1 2)
      (fun h => boundedChannelStartPairs N M 1 2 h)
      W hchannel
  exact hunion.trans
    (Nat.mul_le_mul_right W
      (nontrivialChannelHeights_card_le_three_mul_add_one
        L 1 2 (by omega)))

/--
The complete height-two cover is volumetric.  This is the finite counting
statement that replaces the dyadic boundary estimate.
@isnad1 id=le.1h3v.s6.ffb699cb2843 from=translated src=- shape=df739b43 vocab=94a2d46a
-/
theorem card_boundedHeightTwoPairCover_le
    {N M L : ℕ} (hNM : N ≤ M) :
    (boundedHeightTwoPairCover N M L).card ≤
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) := by
  calc
    (boundedHeightTwoPairCover N M L).card ≤
        (boundedHeightTwoForwardCover N M L).card +
          (boundedHeightTwoBackwardCover N M L).card := by
      exact Finset.card_union_le _ _
    _ ≤ (3 * L + 1) * (1 + (M - N) / 2) +
          (3 * L + 1) * (1 + (M - N) / 2) :=
      Nat.add_le_add
        (card_boundedHeightTwoForwardCover_le hNM)
        (card_boundedHeightTwoBackwardCover_le hNM)
    _ = 2 * ((3 * L + 1) * (1 + (M - N) / 2)) := by
      ring

/--
A selected nontrivial candidate of height two belongs to the volumetric
height-two cover.
@isnad1 id=mem.3h7v.s8.3cea889ef576 from=translated src=- shape=ddcb0cbe vocab=796a7649
-/
theorem pair_mem_boundedHeightTwoPairCover_of_choice
    {N M A L x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L)
    (hm : 2 ≤ candidateMultiplicity L c)
    (hmax : Nat.max c.1.1 c.1.2 = 2) :
    (x, y) ∈ boundedHeightTwoPairCover N M L := by
  obtain ⟨hx, hy, _hsep⟩ :=
    mem_separatedBoundedRatioPairs.mp hpair
  obtain ⟨ha, hb, _haH, _hbH, hab, _hclose⟩ :=
    mem_reducedChannelCandidates.mp c.2
  have hheight :
      pairChannelError x y c.1.1 c.1.2 ∈
        nontrivialChannelHeights L c.1.1 c.1.2 := by
    rw [mem_nontrivialChannelHeights_iff_two_le_card]
    simpa [candidateMultiplicity] using hm
  have hstart :
      (x, y) ∈ boundedChannelStartPairs
        N M c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) :=
    mem_boundedChannelStartPairs.mpr ⟨hx, hy, rfl⟩
  rcases positive_coprime_pair_of_max_eq_two
      ha hb hab hmax with hforward | hbackward
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr
      ⟨pairChannelError x y 2 1,
        by simpa [hforward.1, hforward.2] using hheight,
        by simpa [hforward.1, hforward.2] using hstart⟩
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr
      ⟨pairChannelError x y 1 2,
        by simpa [hbackward.1, hbackward.2] using hheight,
        by simpa [hbackward.1, hbackward.2] using hstart⟩

/-! ## The heights `q≥3` -/

/-- All bounded-ratio start pairs on nontrivial channels of one ratio.-/
def boundedLargeChannelPairCoverAtRatio
    (N M L a b : ℕ) : Finset (ℕ × ℕ) :=
  (nontrivialChannelHeights L a b).biUnion fun h =>
    boundedChannelStartPairs N M a b h

/-- Bounded-ratio pairs covered by all primitive ratios of height `q`.-/
def boundedLargeChannelPairCoverAtHeight
    (N M L q : ℕ) : Finset (ℕ × ℕ) :=
  (reducedRatiosAtHeight q).biUnion fun c =>
    boundedLargeChannelPairCoverAtRatio N M L c.1 c.2

/-- All nontrivial bounded-ratio channels of height `3≤q≤L`.-/
def boundedLargeChannelPairCover
    (N M L : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 3 L).biUnion fun q =>
    boundedLargeChannelPairCoverAtHeight N M L q

/-- Cardinality of the cover at one fixed primitive ratio of height `q≥3`.
@isnad1 id=le.7h6v.s7.4ee5ff09a743 from=translated src=- shape=3e30cdc3 vocab=a9dde872
-/
theorem card_boundedLargeChannelPairCoverAtRatio_le
    {N M L q a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hmax : Nat.max a b = q)
    (hq3 : 3 ≤ q) (hqL : q ≤ L)
    (hNM : N ≤ M) :
    (boundedLargeChannelPairCoverAtRatio N M L a b).card ≤
      (((2 * L) * L + 1) * (1 + (M - N) / 3)) := by
  unfold boundedLargeChannelPairCoverAtRatio
  let W := 1 + (M - N) / 3
  have hstart :
      ∀ h ∈ nontrivialChannelHeights L a b,
        (boundedChannelStartPairs N M a b h).card ≤ W := by
    intro h _hh
    have hbase :=
      boundedChannelStartPairs_card_le_maxStep
        N M a b ha hb hab hNM h
    rw [hmax] at hbase
    have hdiv : (M - N) / q ≤ (M - N) / 3 :=
      Nat.div_le_div_left hq3 (by omega)
    exact hbase.trans (Nat.add_le_add_left hdiv 1)
  have hunion :
      ((nontrivialChannelHeights L a b).biUnion fun h =>
          boundedChannelStartPairs N M a b h).card ≤
        (nontrivialChannelHeights L a b).card * W :=
    Finset.card_biUnion_le_card_mul
      (nontrivialChannelHeights L a b)
      (fun h => boundedChannelStartPairs N M a b h)
      W hstart
  have habSum : a + b ≤ 2 * L := by
    have haL : a ≤ L :=
      (Nat.le_max_left a b).trans (hmax.le.trans hqL)
    have hbL : b ≤ L :=
      (Nat.le_max_right a b).trans (hmax.le.trans hqL)
    omega
  have hheights :
      (nontrivialChannelHeights L a b).card ≤
        (2 * L) * L + 1 := by
    calc
      (nontrivialChannelHeights L a b).card ≤
          (channelHeights L a b).card :=
        Finset.card_filter_le _ _
      _ ≤ (a + b) * L + 1 :=
        channelHeights_card_le L a b
      _ ≤ (2 * L) * L + 1 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right L habSum) 1
  exact hunion.trans
    (Nat.mul_le_mul_right W hheights)

/-- Cardinality at one height `q≥3`.
@isnad1 id=le.3h4v.s7.5fe563142945 from=translated src=- shape=cd6d1e93 vocab=fc60754e
-/
theorem card_boundedLargeChannelPairCoverAtHeight_le
    {N M L q : ℕ}
    (hq3 : 3 ≤ q) (hqL : q ≤ L)
    (hNM : N ≤ M) :
    (boundedLargeChannelPairCoverAtHeight N M L q).card ≤
      (2 * L) *
        (((2 * L) * L + 1) * (1 + (M - N) / 3)) := by
  unfold boundedLargeChannelPairCoverAtHeight
  let W := ((2 * L) * L + 1) * (1 + (M - N) / 3)
  have hratio :
      ∀ c ∈ reducedRatiosAtHeight q,
        (boundedLargeChannelPairCoverAtRatio
          N M L c.1 c.2).card ≤ W := by
    intro c hc
    obtain ⟨ha, hb, hab, hmax⟩ :=
      mem_reducedRatiosAtHeight.mp hc
    exact card_boundedLargeChannelPairCoverAtRatio_le
      ha hb hab hmax hq3 hqL hNM
  have hunion :
      ((reducedRatiosAtHeight q).biUnion fun c =>
          boundedLargeChannelPairCoverAtRatio
            N M L c.1 c.2).card ≤
        (reducedRatiosAtHeight q).card * W :=
    Finset.card_biUnion_le_card_mul
      (reducedRatiosAtHeight q)
      (fun c =>
        boundedLargeChannelPairCoverAtRatio
          N M L c.1 c.2)
      W hratio
  have hratios :
      (reducedRatiosAtHeight q).card ≤ 2 * L :=
    (card_reducedRatiosAtHeight_le q).trans
      (Nat.mul_le_mul_left 2 hqL)
  exact hunion.trans
    (Nat.mul_le_mul_right W hratios)

/-- Cardinality of the complete `q≥3` cover.
@isnad1 id=le.1h3v.s6.a22d043772d4 from=translated src=- shape=afbeab6e vocab=122423dd
-/
theorem card_boundedLargeChannelPairCover_le
    {N M L : ℕ} (hNM : N ≤ M) :
    (boundedLargeChannelPairCover N M L).card ≤
      L * (2 * L) * ((2 * L) * L + 1) *
        (1 + (M - N) / 3) := by
  unfold boundedLargeChannelPairCover
  let W :=
    (2 * L) *
      (((2 * L) * L + 1) * (1 + (M - N) / 3))
  have hheight :
      ∀ q ∈ Icc 3 L,
        (boundedLargeChannelPairCoverAtHeight
          N M L q).card ≤ W := by
    intro q hq
    obtain ⟨hq3, hqL⟩ := Finset.mem_Icc.mp hq
    exact card_boundedLargeChannelPairCoverAtHeight_le
      hq3 hqL hNM
  have hunion :
      ((Icc 3 L).biUnion fun q =>
          boundedLargeChannelPairCoverAtHeight
            N M L q).card ≤
        (Icc 3 L).card * W :=
    Finset.card_biUnion_le_card_mul
      (Icc 3 L)
      (fun q =>
        boundedLargeChannelPairCoverAtHeight N M L q)
      W hheight
  have hcard : (Icc 3 L).card ≤ L := by
    simp [Nat.card_Icc]
  calc
    ((Icc 3 L).biUnion fun q =>
        boundedLargeChannelPairCoverAtHeight N M L q).card ≤
        (Icc 3 L).card * W := hunion
    _ ≤ L * W :=
      Nat.mul_le_mul_right W hcard
    _ = L * (2 * L) * ((2 * L) * L + 1) *
        (1 + (M - N) / 3) := by
      simp [W, Nat.mul_assoc]

/-- A selected nontrivial candidate of height at least three is covered.
@isnad1 id=mem.4h7v.s8.dfeeacafcea0 from=translated src=- shape=50c3ca99 vocab=cb87ab3d
-/
theorem pair_mem_boundedLargeChannelPairCover_of_choice
    {N M A L x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L)
    (hm : 2 ≤ candidateMultiplicity L c)
    (hq3 : 3 ≤ Nat.max c.1.1 c.1.2)
    (hqL : Nat.max c.1.1 c.1.2 ≤ L) :
    (x, y) ∈ boundedLargeChannelPairCover N M L := by
  obtain ⟨hx, hy, _hsep⟩ :=
    mem_separatedBoundedRatioPairs.mp hpair
  obtain ⟨ha, hb, _haH, _hbH, hab, _hclose⟩ :=
    mem_reducedChannelCandidates.mp c.2
  let q := Nat.max c.1.1 c.1.2
  let h := pairChannelError x y c.1.1 c.1.2
  have hc :
      (c.1.1, c.1.2) ∈ reducedRatiosAtHeight q :=
    mem_reducedRatiosAtHeight.mpr
      ⟨ha, hb, hab, rfl⟩
  have hheight :
      h ∈ nontrivialChannelHeights L c.1.1 c.1.2 := by
    rw [mem_nontrivialChannelHeights_iff_two_le_card]
    simpa [candidateMultiplicity, h] using hm
  have hstart :
      (x, y) ∈ boundedChannelStartPairs
        N M c.1.1 c.1.2 h :=
    mem_boundedChannelStartPairs.mpr ⟨hx, hy, rfl⟩
  simp only [boundedLargeChannelPairCover,
    boundedLargeChannelPairCoverAtHeight,
    boundedLargeChannelPairCoverAtRatio,
    Finset.mem_biUnion]
  refine ⟨q, ?_, c.1, hc, h, hheight, hstart⟩
  exact Finset.mem_Icc.mpr
    ⟨by simpa [q] using hq3, by simpa [q] using hqL⟩

/-! ## Finite bounded-ratio rational mass (Lemma 17.5) -/

/-- Canonical rational mass over all separated pairs in `U(N,M)²`.-/
noncomputable def boundedRationalMass
    (N M A L base : ℕ) : ℕ :=
  ∑ pair ∈ separatedBoundedRatioPairs N M L,
    (base ^
      RationalMassFinite.canonicalPairSigma
        A L pair.1 pair.2 - 1)

/--
Every positive canonical weight is charged either to the volumetric
height-two cover or to the enumerated heights `q≥3`.
@isnad1 id=le.2h7v.s8.4114a6f80062 from=translated src=- shape=e8be2833 vocab=e4c7d52c
-/
theorem boundedCanonicalPairWeight_le_coverWeights
    {N M A L base x y : ℕ}
    (hbase : 1 ≤ base)
    (hpair : (x, y) ∈ separatedBoundedRatioPairs N M L) :
    base ^
        RationalMassFinite.canonicalPairSigma A L x y - 1 ≤
      (if (x, y) ∈ boundedHeightTwoPairCover N M L then
          base ^ (L / 2)
        else 0) +
      (if (x, y) ∈ boundedLargeChannelPairCover N M L then
          base ^ (L / 3)
        else 0) := by
  by_cases hsigma :
      RationalMassFinite.canonicalPairSigma A L x y = 0
  · simp [hsigma]
  · have hsigmaPos :
        0 < RationalMassFinite.canonicalPairSigma A L x y :=
      Nat.pos_of_ne_zero hsigma
    have hmCanonical :
        2 ≤ canonicalMultiplicity A L x y :=
      RationalMassFinite.two_le_canonicalMultiplicity_of_sigma_pos
        hsigmaPos
    obtain ⟨c, hchoice, hm⟩ :=
      exists_canonical_candidate_of_two_le_multiplicity
        hmCanonical
    let q := Nat.max c.1.1 c.1.2
    have hqPos : 0 < q :=
      (candidate_fst_pos c).trans_le
        (Nat.le_max_left c.1.1 c.1.2)
    have hqL : q ≤ L :=
      candidate_max_le_length_of_two_units c hm
    have hweight :
        base ^
            RationalMassFinite.canonicalPairSigma A L x y - 1 ≤
          base ^ (L / q) := by
      simpa [q] using
        RationalMassFinite.canonicalPairWeight_le_pow_div_of_choice
          hbase hchoice
    by_cases hqTwo : q = 2
    · have hmem :
          (x, y) ∈ boundedHeightTwoPairCover N M L :=
        pair_mem_boundedHeightTwoPairCover_of_choice
          hpair hm (by simpa [q] using hqTwo)
      have hweightTwo :
          base ^
              RationalMassFinite.canonicalPairSigma A L x y - 1 ≤
            base ^ (L / 2) := by
        simpa [hqTwo] using hweight
      rw [ite_eq_left hmem]
      omega
    · have hqOneNe : q ≠ 1 := by
        intro hqOne
        have hcells :
            2 ≤ (channelCells L c.1.1 c.1.2
              (pairChannelError x y c.1.1 c.1.2)).card := by
          simpa [candidateMultiplicity] using hm
        have hnear :=
          height_one_primitive_channel_forces_unit_and_nearby
            (candidate_fst_pos c) (candidate_snd_pos c)
            (candidate_coprime c)
            (by simpa [q] using hqOne)
            (h := pairChannelError x y c.1.1 c.1.2)
            rfl hcells
        have hsep :=
          (mem_separatedBoundedRatioPairs.mp hpair).2.2
        omega
      have hq3 : 3 ≤ q := by omega
      have hmem :
          (x, y) ∈ boundedLargeChannelPairCover N M L :=
        pair_mem_boundedLargeChannelPairCover_of_choice
          hpair hm (by simpa [q] using hq3)
            (by simpa [q] using hqL)
      have hquotient : L / q ≤ L / 3 :=
        Nat.div_le_div_left hq3 (by omega)
      have hweightThree :
          base ^
              RationalMassFinite.canonicalPairSigma A L x y - 1 ≤
            base ^ (L / 3) :=
        hweight.trans
          (Nat.pow_le_pow_right hbase hquotient)
      rw [ite_eq_left hmem]
      omega

private theorem sum_ite_mem_le_card_mul
    {α : Type*} [DecidableEq α]
    (s t : Finset α) (W : ℕ) :
    (∑ x ∈ s, if x ∈ t then W else 0) ≤ t.card * W := by
  classical
  have hsubset :
      s.filter (fun x => x ∈ t) ⊆ t := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc
    (∑ x ∈ s, if x ∈ t then W else 0) =
        ∑ x ∈ s.filter (fun x => x ∈ t), W := by
      rw [Finset.sum_filter]
    _ = (s.filter (fun x => x ∈ t)).card * W := by
      simp
    _ ≤ t.card * W :=
      Nat.mul_le_mul_right W (Finset.card_le_card hsubset)

/--
Exact finite rational-mass estimate on `U(N,M)`.  The first summand is the
new volumetric `q=2` term; the second is the unchanged `q≥3` geometry with
the dyadic width `N` replaced by `M-N`.
@isnad1 id=le.3h5v.s8.99e471ad7d32 from=translated src=- shape=ddda3a21 vocab=3a322681
-/
theorem boundedRationalMass_le
    (N M A L base : ℕ)
    (hNM : N ≤ M) (_hA : 1 ≤ A) (hbase : 1 ≤ base) :
    boundedRationalMass N M A L base ≤
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          base ^ (L / 2) +
        L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3) * base ^ (L / 3) := by
  let W₂ := base ^ (L / 2)
  let W₃ := base ^ (L / 3)
  have hpoint :
      ∀ pair ∈ separatedBoundedRatioPairs N M L,
        base ^
            RationalMassFinite.canonicalPairSigma
              A L pair.1 pair.2 - 1 ≤
          (if pair ∈ boundedHeightTwoPairCover N M L then
              W₂ else 0) +
          (if pair ∈ boundedLargeChannelPairCover N M L then
              W₃ else 0) := by
    intro pair hpair
    rcases pair with ⟨x, y⟩
    exact boundedCanonicalPairWeight_le_coverWeights
      hbase hpair
  have hsum :
      boundedRationalMass N M A L base ≤
        (∑ pair ∈ separatedBoundedRatioPairs N M L,
          if pair ∈ boundedHeightTwoPairCover N M L then
            W₂ else 0) +
        ∑ pair ∈ separatedBoundedRatioPairs N M L,
          if pair ∈ boundedLargeChannelPairCover N M L then
            W₃ else 0 := by
    unfold boundedRationalMass
    calc
      (∑ pair ∈ separatedBoundedRatioPairs N M L,
          (base ^
            RationalMassFinite.canonicalPairSigma
              A L pair.1 pair.2 - 1)) ≤
          ∑ pair ∈ separatedBoundedRatioPairs N M L,
            ((if pair ∈ boundedHeightTwoPairCover N M L then
                W₂ else 0) +
              (if pair ∈ boundedLargeChannelPairCover N M L then
                W₃ else 0)) := by
          simpa only using
            (Finset.sum_le_sum fun pair hpair =>
              hpoint pair hpair)
      _ = (∑ pair ∈ separatedBoundedRatioPairs N M L,
            if pair ∈ boundedHeightTwoPairCover N M L then
              W₂ else 0) +
          ∑ pair ∈ separatedBoundedRatioPairs N M L,
            if pair ∈ boundedLargeChannelPairCover N M L then
              W₃ else 0 := by
        rw [Finset.sum_add_distrib]
  have htwo :
      (∑ pair ∈ separatedBoundedRatioPairs N M L,
        if pair ∈ boundedHeightTwoPairCover N M L then
          W₂ else 0) ≤
        2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          W₂ := by
    exact
      (sum_ite_mem_le_card_mul
        (separatedBoundedRatioPairs N M L)
        (boundedHeightTwoPairCover N M L) W₂).trans
      (Nat.mul_le_mul_right W₂
        (card_boundedHeightTwoPairCover_le hNM))
  have hlarge :
      (∑ pair ∈ separatedBoundedRatioPairs N M L,
        if pair ∈ boundedLargeChannelPairCover N M L then
          W₃ else 0) ≤
        (L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3)) * W₃ := by
    exact
      (sum_ite_mem_le_card_mul
        (separatedBoundedRatioPairs N M L)
        (boundedLargeChannelPairCover N M L) W₃).trans
      (Nat.mul_le_mul_right W₃
        (card_boundedLargeChannelPairCover_le hNM))
  calc
    boundedRationalMass N M A L base ≤
        (∑ pair ∈ separatedBoundedRatioPairs N M L,
          if pair ∈ boundedHeightTwoPairCover N M L then
            W₂ else 0) +
        ∑ pair ∈ separatedBoundedRatioPairs N M L,
          if pair ∈ boundedLargeChannelPairCover N M L then
            W₃ else 0 := hsum
    _ ≤ 2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          W₂ +
        (L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3)) * W₃ :=
      Nat.add_le_add htwo hlarge
    _ = 2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          base ^ (L / 2) +
        L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3) * base ^ (L / 3) := by
      simp [W₂, W₃, Nat.mul_assoc]

/--
A common base-two envelope under `M≤κ₀N`.  It displays the new scale
`N·2^(L/2)` and is tailored to the critical-window asymptotic closure.
@isnad1 id=le.4h5v.s7.4f7ab9e4339c from=translated src=- shape=71e8144c vocab=1f05e218
-/
theorem boundedRationalMass_two_le_common
    {N M A L κ₀ : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A) :
    boundedRationalMass N M A L 2 ≤
      16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        2 ^ (L / 2) := by
  have hfinite :=
    boundedRationalMass_le N M A L 2 hNM hA (by norm_num)
  have hwidth : M - N ≤ κ₀ * N :=
    (Nat.sub_le M N).trans hM
  have hfactorTwo :
      1 + (M - N) / 2 ≤ (κ₀ + 1) * N := by
    calc
      1 + (M - N) / 2 ≤ 1 + (M - N) :=
        Nat.add_le_add_left (Nat.div_le_self (M - N) 2) 1
      _ ≤ N + κ₀ * N := by omega
      _ = (κ₀ + 1) * N := by ring
  have hfactorThree :
      1 + (M - N) / 3 ≤ (κ₀ + 1) * N := by
    calc
      1 + (M - N) / 3 ≤ 1 + (M - N) :=
        Nat.add_le_add_left (Nat.div_le_self (M - N) 3) 1
      _ ≤ N + κ₀ * N := by omega
      _ = (κ₀ + 1) * N := by ring
  have hHpos : 0 < L + 1 := Nat.succ_pos L
  have hL : L ≤ L + 1 := Nat.le_succ L
  have hlinear : 3 * L + 1 ≤ 4 * (L + 1) := by
    omega
  have hHpow : L + 1 ≤ (L + 1) ^ 4 := by
    calc
      L + 1 = (L + 1) ^ 1 := by simp
      _ ≤ (L + 1) ^ 4 :=
        Nat.pow_le_pow_right hHpos (by omega)
  have hsmall :
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          2 ^ (L / 2) ≤
        8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          2 ^ (L / 2) := by
    calc
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
            2 ^ (L / 2) ≤
          2 * ((4 * (L + 1)) * ((κ₀ + 1) * N)) *
            2 ^ (L / 2) :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 2
            (Nat.mul_le_mul hlinear hfactorTwo))
      _ = 8 * (κ₀ + 1) * (L + 1) * N *
          2 ^ (L / 2) := by ring
      _ ≤ 8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          2 ^ (L / 2) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right N
            (Nat.mul_le_mul_left (8 * (κ₀ + 1)) hHpow))
  have htwoL : 2 * L ≤ 2 * (L + 1) :=
    Nat.mul_le_mul_left 2 hL
  have honeSquare : 1 ≤ (L + 1) * (L + 1) := by
    nlinarith
  have hinner :
      (2 * L) * L + 1 ≤
        (2 * (L + 1)) * (L + 1) +
          (L + 1) * (L + 1) :=
    Nat.add_le_add
      (Nat.mul_le_mul htwoL hL) honeSquare
  have hfront :
      L * (2 * L) ≤
        (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hL htwoL
  have hlargePoly :
      L * (2 * L) * ((2 * L) * L + 1) ≤
        6 * (L + 1) ^ 4 := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) ≤
          ((L + 1) * (2 * (L + 1))) *
            ((2 * (L + 1)) * (L + 1) +
              (L + 1) * (L + 1)) :=
        Nat.mul_le_mul hfront hinner
      _ = 6 * (L + 1) ^ 4 := by ring
  have hthirdHalf : L / 3 ≤ L / 2 :=
    Nat.div_le_div_left (by omega : 2 ≤ 3) (by omega)
  have hpow :
      2 ^ (L / 3) ≤ 2 ^ (L / 2) :=
    Nat.pow_le_pow_right (by norm_num) hthirdHalf
  have hlarge :
      L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3) * 2 ^ (L / 3) ≤
        6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          2 ^ (L / 2) := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) *
            (1 + (M - N) / 3) * 2 ^ (L / 3) ≤
          (6 * (L + 1) ^ 4) * ((κ₀ + 1) * N) *
            2 ^ (L / 2) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul hlargePoly hfactorThree)
          hpow
      _ = 6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          2 ^ (L / 2) := by ring
  calc
    boundedRationalMass N M A L 2 ≤
        2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
            2 ^ (L / 2) +
          L * (2 * L) * ((2 * L) * L + 1) *
            (1 + (M - N) / 3) * 2 ^ (L / 3) :=
      hfinite
    _ ≤
        8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
            2 ^ (L / 2) +
          6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
            2 ^ (L / 2) :=
      Nat.add_le_add hsmall hlarge
    _ = 14 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        2 ^ (L / 2) := by ring
    _ ≤ 16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        2 ^ (L / 2) := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right N
          (Nat.mul_le_mul_right ((L + 1) ^ 4)
            (Nat.mul_le_mul_right (κ₀ + 1) (by omega))))

/-- Base-two specialization of the volumetric `q=2` contribution.
@isnad1 id=le.1h3v.s7.a09fe2f10803 from=translated src=- shape=76f8e5d0 vocab=3abc2c46
-/
theorem boundedHeightTwoMass_two_le
    {N M L : ℕ} (hNM : N ≤ M) :
    (boundedHeightTwoPairCover N M L).card * 2 ^ (L / 2) ≤
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
        2 ^ (L / 2) :=
  Nat.mul_le_mul_right _ (card_boundedHeightTwoPairCover_le hNM)

/-- Base-four specialization of the volumetric `q=2` contribution.
@isnad1 id=le.1h3v.s7.a25986781fa9 from=translated src=- shape=76f8e5d0 vocab=3abc2c46
-/
theorem boundedHeightTwoMass_four_le
    {N M L : ℕ} (hNM : N ≤ M) :
    (boundedHeightTwoPairCover N M L).card * 4 ^ (L / 2) ≤
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
        4 ^ (L / 2) :=
  Nat.mul_le_mul_right _ (card_boundedHeightTwoPairCover_le hNM)

/-!
The geometry-only sum does not contain a start translation parameter.
Consequently it is literally the same finite object on a dyadic block and
on `U(N,M)`.  This wrapper is the finite content of Lemma 17.6.
-/
/--
@isnad1 id=le.0h1v.s7.7658530636c1 from=translated src=- shape=bf878e96 vocab=dc044c12
-/
theorem boundedRatio_weightedChannelGeometry_le
    (L : ℕ) :
    weightedChannelMass L ≤
      8 * ((4 * L + 1) * 4 ^ (L / 2)) +
        L * ((2 * L) *
          (((2 * L) * L + 1) * 4 ^ (L / 3))) :=
  weightedChannelMass_le_small_add_large L

end

end BoundedRatioGeometry
end PaperC
