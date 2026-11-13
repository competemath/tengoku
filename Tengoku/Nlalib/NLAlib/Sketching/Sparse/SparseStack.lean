/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.MomentMethod.GramError
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The SparseStack sketch matrix

A SparseStack sample `Z : SparseStackSample s b n` assigns to every column `i` and block `g` a
hash `Z.hash g i : Fin b` and a sign; `sparseStackMatrix Z : Matrix (Fin s × Fin b) (Fin n) ℝ`
has entry `± 1/√s` at row `(g, Z.hash g i)` of column `i` (`card_filter_sparseStackMatrix_ne_zero`:
exactly `s` nonzeros per column). The rest of the file (namespace `NLAlib.SparseSketch`) is the
signed-basis and hollow-Gram calculus used by the trace-moment proof.
Ported from `SparseFockFormal.SparseStackModel` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

open scoped InnerProductSpace

noncomputable section

/-- A Rademacher sign, with no zero constructor.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq

/-- The exact real value of a Rademacher sign.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Sign.val : Sign → ℝ
  | .plus => 1
  | .minus => -1

/-- The positive sign has real value one.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.3d68a41c1418 from=translated src=- shape=b0ae1d2b vocab=80f085a3
-/
@[simp] theorem Sign.val_plus : Sign.plus.val = 1 := rfl
/-- The negative sign has real value minus one.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.5c175b995ba1 from=translated src=- shape=f7285ee8 vocab=4a0060f6
-/
@[simp] theorem Sign.val_minus : Sign.minus.val = -1 := rfl

/-- Every sign value has square one.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.18ead7350700 from=translated src=- shape=d9ef4337 vocab=06e39a54
-/
@[simp]
theorem Sign.val_sq (z : Sign) : z.val ^ 2 = 1 := by
  cases z <;> norm_num [Sign.val]

/-- Every sign value is nonzero.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=ne.0h1v.s3.48ff1bf9e535 from=translated src=- shape=a311c14d vocab=6327a47b
-/
theorem Sign.val_ne_zero (z : Sign) : z.val ≠ 0 := by
  cases z <;> norm_num [Sign.val]

/-- Every sign value has absolute value one.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.3cbd8ec0582b from=translated src=- shape=562e4a6d vocab=51f8d39d
-/
@[simp]
theorem Sign.abs_val (z : Sign) : |z.val| = 1 := by
  cases z <;> norm_num [Sign.val]

/-- One fully explicit SparseStack outcome.  Both the hash and the sign are indexed
by the literal sample space `Fin s × Fin n`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
structure _root_.NLAlib.SparseStackSample (s b n : ℕ) where
  h : Fin s × Fin n → Fin b
  sign : Fin s × Fin n → Sign

/-- The sample hash records the selected row inside a physical block for a column.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def _root_.NLAlib.SparseStackSample.hash {s b n : ℕ} (Z : SparseStackSample s b n) (g : Fin s)
    (i : Fin n) : Fin b :=
  Z.h (g, i)

/-- The sample sign records the signed basis choice inside a physical block for a column.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def _root_.NLAlib.SparseStackSample.sgn {s b n : ℕ} (Z : SparseStackSample s b n) (g : Fin s)
    (i : Fin n) : Sign :=
  Z.sign (g, i)

/-- The signed basis vector `X_{g i} = σ_{g i} e_{h_g(i)}`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def signedBasis {s b n : ℕ} (Z : SparseStackSample s b n) (g : Fin s) (i : Fin n) :
    EVec b :=
  WithLp.toLp 2 fun a ↦ if a = Z.hash g i then (Z.sgn g i).val else 0

/-- A signed basis vector has its sign value at the selected hash coordinate and zero elsewhere.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h7v.s6.0c70029cbff3 from=translated src=- shape=01786245 vocab=cbec3896
-/
@[simp]
theorem signedBasis_apply {s b n : ℕ} (Z : SparseStackSample s b n)
    (g : Fin s) (i : Fin n) (a : Fin b) :
    signedBasis Z g i a = if a = Z.hash g i then (Z.sgn g i).val else 0 := rfl

/-- Exact collision formula for the signed basis vectors.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h7v.s7.a28264de1255 from=translated src=- shape=f26eceef vocab=df0e8484
-/
theorem inner_signedBasis {s b n : ℕ} (Z : SparseStackSample s b n)
    (g : Fin s) (i j : Fin n) :
    ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ =
      if Z.hash g i = Z.hash g j
      then (Z.sgn g i).val * (Z.sgn g j).val else 0 := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, signedBasis_apply]
  by_cases hij : Z.hash g i = Z.hash g j
  · rw [hij]
    simp
  · simp only [hij, ite_false]
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hai : a = Z.hash g i
    · have haj : a ≠ Z.hash g j := by
        intro haj
        exact hij (hai.symm.trans haj)
      rw [ite_eq_left hai, ite_eq_right haj]
      ring
    · rw [ite_eq_right hai]
      ring

/-- `‖X_{g i}‖² = 1` exactly, not merely almost surely.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s5.3f17aff2dedb from=translated src=- shape=75f982be vocab=82271a7d
-/
@[simp]
theorem signedBasis_normSq {s b n : ℕ} (Z : SparseStackSample s b n)
    (g : Fin s) (i : Fin n) :
    euclideanNormSq (signedBasis Z g i) = 1 := by
  rw [euclideanNormSq, inner_signedBasis]
  simpa [pow_two] using Sign.val_sq (Z.sgn g i)

/-- Every signed basis vector has unit Euclidean squared norm.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s6.2fc3b94d5f69 from=translated src=- shape=170ed4ec vocab=ca9ee029
-/
@[simp]
theorem inner_signedBasis_self {s b n : ℕ} (Z : SparseStackSample s b n)
    (g : Fin s) (i : Fin n) :
    ⟪signedBasis Z g i, signedBasis Z g i⟫_ℝ = 1 := by
  simpa [euclideanNormSq] using signedBasis_normSq Z g i

/-- The normalization `s^{-1/2}`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def invSqrt (s : ℕ) : ℝ := (Real.sqrt (s : ℝ))⁻¹

/-- The stacked sketch matrix, with rows indexed without flattening by
`Fin s × Fin b` and columns by `Fin n`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def _root_.NLAlib.sparseStackMatrix {s b n : ℕ} (Z : SparseStackSample s b n) :
    Matrix (Fin s × Fin b) (Fin n) ℝ :=
  fun r i ↦ invSqrt s * signedBasis Z r.1 i r.2

/-- A SparseStack matrix entry is the normalized signed hash indicator.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h7v.s6.9cfb6eb70327 from=translated src=- shape=33e36eb2 vocab=eb842dea
-/
@[simp]
theorem _root_.NLAlib.sparseStackMatrix_apply {s b n : ℕ} (Z : SparseStackSample s b n)
    (g : Fin s) (a : Fin b) (i : Fin n) :
    sparseStackMatrix Z (g, a) i = invSqrt s *
      (if a = Z.hash g i then (Z.sgn g i).val else 0) := rfl

/-- The inverse square-root sparsity normalization is nonzero at positive sparsity.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=ne.1h1v.s4.2e5759b6fa99 from=translated src=- shape=aa240375 vocab=4e17cc24
-/
theorem invSqrt_ne_zero {s : ℕ} (hs : 0 < s) : invSqrt s ≠ 0 := by
  apply inv_ne_zero
  exact ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hs))

/-- The squared inverse square-root normalization is the reciprocal sparsity.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h1v.s5.d15afabd6383 from=translated src=- shape=7fb9cb5c vocab=4ade7570
-/
theorem invSqrt_sq {s : ℕ} (_hs : 0 < s) :
    invSqrt s ^ 2 = 1 / (s : ℝ) := by
  rw [invSqrt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
  simp [div_eq_mul_inv]

/-- A matrix entry is nonzero exactly at the sampled hash location.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.1h7v.s5.58b7d69e4dc5 from=translated src=- shape=75019cd1 vocab=51793801
-/
theorem _root_.NLAlib.sparseStackMatrix_ne_zero_iff {s b n : ℕ} (Z : SparseStackSample s b n)
    (hs : 0 < s)
    (g : Fin s) (a : Fin b) (i : Fin n) :
    sparseStackMatrix Z (g, a) i ≠ 0 ↔ a = Z.hash g i := by
  by_cases ha : a = Z.hash g i
  · simp [sparseStackMatrix_apply, ha, invSqrt_ne_zero hs, Sign.val_ne_zero]
  · simp [sparseStackMatrix_apply, ha]

/-- In each block and column there is exactly one nonzero entry.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=existsun.1h6v.s5.dbba95376f66 from=translated src=- shape=0718551c vocab=0d3ea777
-/
theorem exactly_one_nonzero_in_block {s b n : ℕ} (Z : SparseStackSample s b n) (hs : 0 < s)
    (g : Fin s) (i : Fin n) :
    ∃! a : Fin b, sparseStackMatrix Z (g, a) i ≠ 0 := by
  refine ⟨Z.hash g i, ?_, ?_⟩
  · exact (sparseStackMatrix_ne_zero_iff Z hs g (Z.hash g i) i).2 rfl
  · intro a ha
    exact (sparseStackMatrix_ne_zero_iff Z hs g a i).1 ha

/-- The nonzero support of one column is canonically equivalent to the block index.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def columnSupportEquiv {s b n : ℕ} (Z : SparseStackSample s b n) (hs : 0 < s) (i : Fin n) :
    {r : Fin s × Fin b // sparseStackMatrix Z r i ≠ 0} ≃ Fin s where
  toFun r := r.1.1
  invFun g := ⟨(g, Z.hash g i),
    (sparseStackMatrix_ne_zero_iff Z hs g (Z.hash g i) i).2 rfl⟩
  left_inv := by
    rintro ⟨⟨g, a⟩, ha⟩
    have hloc := (sparseStackMatrix_ne_zero_iff Z hs g a i).1 ha
    subst a
    rfl
  right_inv := by
    intro g
    rfl

/-- Consequently every column has exactly `s` nonzero entries.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h5v.s6.9e4b3bb90683 from=translated src=- shape=5bdbfbaa vocab=8c592f6b
-/
theorem _root_.NLAlib.card_filter_sparseStackMatrix_ne_zero {s b n : ℕ}
    (Z : SparseStackSample s b n) (hs : 0 < s)
    (i : Fin n) :
    Fintype.card {r : Fin s × Fin b // sparseStackMatrix Z r i ≠ 0} = s := by
  rw [Fintype.card_congr (columnSupportEquiv Z hs i)]
  simp

/-- One block Gram entry is its normalization squared times the signed-basis inner product.
Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h7v.s7.be03d5006490 from=translated src=- shape=e6471d33 vocab=ddc37755
-/
theorem block_gram_apply {s b n : ℕ} (Z : SparseStackSample s b n)
    (g : Fin s) (i j : Fin n) :
    (∑ a : Fin b, sparseStackMatrix Z (g, a) i * sparseStackMatrix Z (g, a) j) =
      invSqrt s ^ 2 * ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, sparseStackMatrix_apply, signedBasis_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Exact entrywise Gram formula for the normalized stacked sketch.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s7.419fdf9fab76 from=translated src=- shape=2b3e078e vocab=e8d34667
-/
theorem sketchGram_apply {s b n : ℕ} (Z : SparseStackSample s b n) (hs : 0 < s)
    (i j : Fin n) :
    sketchGram (sparseStackMatrix Z) i j =
      (1 / (s : ℝ)) * ∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ := by
  rw [sketchGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [block_gram_apply Z]
  rw [← Finset.mul_sum, invSqrt_sq hs]

/-- The full ordered-column expansion, before canceling its diagonal.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def fullGramExpansion {s b n d : ℕ} (F : Frame n d) (Z : SparseStackSample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a c ↦ (1 / (s : ℝ)) *
    ∑ i, ∑ j, (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) *
      F.u i a * F.u j c

/-- The exact hollow sum.  `j ∈ univ.erase i` is the literal finite encoding of `i ≠ j`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def hollowGram {s b n d : ℕ} (F : Frame n d) (Z : SparseStackSample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a c ↦ (1 / (s : ℝ)) *
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c

/-- Expanding the matrix products gives the full three-index sum.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s6.b58d364729a6 from=translated src=- shape=0d74ae2e vocab=8d125e2b
-/
theorem embeddedGram_eq_fullExpansion {s b n d : ℕ} (F : Frame n d)
    (Z : SparseStackSample s b n) (hs : 0 < s) :
    embeddedGram F (sparseStackMatrix Z) = fullGramExpansion F Z := by
  ext a c
  simp only [embeddedGram, Matrix.mul_apply, Matrix.transpose_apply, rowMatrix]
  simp_rw [sketchGram_apply Z hs]
  simp only [fullGramExpansion]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  ring

/-- The diagonal part of the full expansion is exactly `I_d`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s6.8c6c2d019a09 from=translated src=- shape=a2001aae vocab=896b720a
-/
theorem fullExpansion_eq_one_add_hollow {s b n d : ℕ} (F : Frame n d)
    (Z : SparseStackSample s b n) (hs : 0 < s) :
    fullGramExpansion F Z = 1 + hollowGram F Z := by
  classical
  ext a c
  have hs0 : (s : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs))
  have hparseval := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M a c) F.parseval
  have hparseval' : (∑ i, F.u i a * F.u i c) =
      (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hparseval
  let T : Fin n → Fin n → ℝ := fun i j ↦
    (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c
  have hsplit (i : Fin n) :
      (∑ j, T i j) = T i i + ∑ j ∈ Finset.univ.erase i, T i j := by
    have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    rw [← Finset.sum_erase_add _ _ hi]
    ring
  have hdiag :
      (1 / (s : ℝ)) * ∑ i, T i i =
        (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    have hTi (i : Fin n) : T i i = (s : ℝ) * F.u i a * F.u i c := by
      have hone :
          (∑ g, ⟪signedBasis Z g i, signedBasis Z g i⟫_ℝ) = (s : ℝ) := by
        simp only [inner_signedBasis_self]
        simp
      dsimp [T]
      rw [hone]
    simp_rw [hTi]
    calc
      (1 / (s : ℝ)) * ∑ i, (s : ℝ) * F.u i a * F.u i c =
          ((1 / (s : ℝ)) * (s : ℝ)) * ∑ i, F.u i a * F.u i c := by
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
      _ = ∑ i, F.u i a * F.u i c := by field_simp [hs0]
      _ = (1 : Matrix (Fin d) (Fin d) ℝ) a c := hparseval'
  simp only [fullGramExpansion, hollowGram, Matrix.add_apply]
  change (1 / (s : ℝ)) * (∑ i, ∑ j, T i j) =
    (1 : Matrix (Fin d) (Fin d) ℝ) a c +
      (1 / (s : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, T i j
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  rw [mul_add]
  rw [hdiag]

/-- The exact hollow identity (paper (2.2)): the Parseval diagonal cancels from
`UᵀΠᵀΠU-I`, leaving only ordered pairs `i ≠ j`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s6.6829ef1f0461 from=translated src=- shape=0d74ae2e vocab=8f0ad46d
-/
theorem gramError_eq_hollow {s b n d : ℕ} (F : Frame n d)
    (Z : SparseStackSample s b n) (hs : 0 < s) :
    gramError F (sparseStackMatrix Z) = hollowGram F Z := by
  rw [gramError, embeddedGram_eq_fullExpansion F Z hs,
    fullExpansion_eq_one_add_hollow F Z hs]
  abel

/-- The same hollow sum with the block index written first, matching the paper's
literal order `Σ_g Σ_{i≠j}`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s8.6e4566a0edb1 from=translated src=- shape=9ed05ec8 vocab=807b2c8f
-/
theorem hollowGram_block_first {s b n d : ℕ} (F : Frame n d) (Z : SparseStackSample s b n) :
    hollowGram F Z = fun a c ↦ (1 / (s : ℝ)) *
      ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
  ext a c
  simp only [hollowGram]
  congr 1
  have hfixed (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i,
          (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c) =
        ∑ g, ∑ j ∈ Finset.univ.erase i,
          ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c) =
      ∑ i, ∑ g, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hfixed i
    _ = ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c :=
      Finset.sum_comm

/-- Paper-form statement of the hollow identity, with the block sum outermost.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s8.75191bbb1d4a from=translated src=- shape=881df95e vocab=eceeffc8
-/
theorem gramError_eq_block_first {s b n d : ℕ} (F : Frame n d)
    (Z : SparseStackSample s b n) (hs : 0 < s) :
    gramError F (sparseStackMatrix Z) = fun a c ↦ (1 / (s : ℝ)) *
      ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
  rw [gramError_eq_hollow F Z hs, hollowGram_block_first F Z]

end

end NLAlib.SparseSketch
