import Tengoku.Nlalib.NLAlib.Matrix.Structured.ProfileRearrangementScales
import Tengoku.Seed.Data.Matrix.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three explicit masks for a rearranged variance profile

Alternating overlapping diagonal blocks give two block-supported masks and
their residual mask. Blocks of the same parity are disjoint. These are the
sets `E₁`, `E₂`, and `E₃` in Latała--van Handel--Youssef (2018), Section 3.2,
with zero-based half-open intervals and main cutoff starting at four.
-/

noncomputable section

namespace NLAlib

/-- Start of the successive overlapping diagonal blocks; the initial block
starts at zero.-/
def profileBlockStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => profileCutoff k

/-- Membership of a position in the `t`th overlapping diagonal block.-/
def InProfileBlock (t i : ℕ) : Prop :=
  profileBlockStart t ≤ i ∧ i < profileNeighborCutoff t

/-- Two positions lie together in an even diagonal block.-/
def ProfileFirstMask (i j : ℕ) : Prop :=
  ∃ t, t % 2 = 0 ∧ InProfileBlock t i ∧ InProfileBlock t j

/-- Two positions lie together in an odd diagonal block.-/
def ProfileOddBlockMask (i j : ℕ) : Prop :=
  ∃ t, t % 2 = 1 ∧ InProfileBlock t i ∧ InProfileBlock t j

/-- The odd diagonal-block mask with the first mask removed.-/
def ProfileSecondMask (i j : ℕ) : Prop :=
  ProfileOddBlockMask i j ∧ ¬ ProfileFirstMask i j

/-- The residual entries outside all successive diagonal blocks.-/
def ProfileRemainderMask (i j : ℕ) : Prop :=
  ¬ ProfileFirstMask i j ∧ ¬ ProfileOddBlockMask i j

/-- Blocks at least two positions apart have separated supporting intervals.
@isnad1 id=le.1h2v.s4.b4faafaba1b8 from=translated src=- shape=60df1d81 vocab=475972cc
-/
theorem profileNeighborCutoff_le_blockStart {t u : ℕ} (htu : t + 2 ≤ u) :
    profileNeighborCutoff t ≤ profileBlockStart u := by
  cases u with
  | zero => omega
  | succ u =>
      exact (profileNeighborCutoff_lt_cutoff_succ t).le.trans
        (monotone_profileCutoff (by omega))

/-- Distinct diagonal blocks of the same parity are disjoint.
@isnad1 id=not.3h3v.s5.c51c9c50468e from=translated src=- shape=e71a5117 vocab=5e9461f2
-/
theorem not_inProfileBlock_of_same_parity {t u i : ℕ}
    (htu : t ≠ u) (hparity : t % 2 = u % 2) (hi : InProfileBlock t i) :
    ¬ InProfileBlock u i := by
  intro hu
  rcases lt_or_gt_of_ne htu with h | h
  · have hgap : t + 2 ≤ u := by omega
    have hsep := profileNeighborCutoff_le_blockStart hgap
    exact (not_lt_of_ge (hsep.trans hu.1)) hi.2
  · have hgap : u + 2 ≤ t := by omega
    have hsep := profileNeighborCutoff_le_blockStart hgap
    exact (not_lt_of_ge (hsep.trans hi.1)) hu.2

/-- The first mask is symmetric.
@isnad1 id=iff.0h2v.s3.eebb282070f8 from=translated src=- shape=62a40b99 vocab=5ab02c3f
-/
theorem profileFirstMask_comm (i j : ℕ) :
    ProfileFirstMask i j ↔ ProfileFirstMask j i := by
  constructor <;> rintro ⟨t, ht, hi, hj⟩ <;> exact ⟨t, ht, hj, hi⟩

/-- The odd block cover is symmetric.
@isnad1 id=iff.0h2v.s3.e96935af0afc from=translated src=- shape=62a40b99 vocab=bb444b51
-/
theorem profileOddBlockMask_comm (i j : ℕ) :
    ProfileOddBlockMask i j ↔ ProfileOddBlockMask j i := by
  constructor <;> rintro ⟨t, ht, hi, hj⟩ <;> exact ⟨t, ht, hj, hi⟩

/-- The second mask is symmetric.
@isnad1 id=iff.0h2v.s3.ff3341711f2f from=translated src=- shape=62a40b99 vocab=0fa70730
-/
theorem profileSecondMask_comm (i j : ℕ) :
    ProfileSecondMask i j ↔ ProfileSecondMask j i := by
  simp only [ProfileSecondMask, profileOddBlockMask_comm i j, profileFirstMask_comm i j]

/-- The residual mask is symmetric.
@isnad1 id=iff.0h2v.s3.f1227cec912a from=translated src=- shape=62a40b99 vocab=e91536a1
-/
theorem profileRemainderMask_comm (i j : ℕ) :
    ProfileRemainderMask i j ↔ ProfileRemainderMask j i := by
  simp only [ProfileRemainderMask, profileOddBlockMask_comm i j, profileFirstMask_comm i j]

/-- A residual pair cannot belong to any common diagonal block.
@isnad1 id=not.2h3v.s4.134c71b04d81 from=translated src=- shape=c3f208ab vocab=5bf06a7d
-/
theorem not_inProfileBlock_pair_of_remainder {i j t : ℕ}
    (hij : ProfileRemainderMask i j) (hi : InProfileBlock t i) :
    ¬ InProfileBlock t j := by
  intro hj
  by_cases ht : t % 2 = 0
  · exact hij.1 ⟨t, ht, hi, hj⟩
  · exact hij.2 ⟨t, by omega, hi, hj⟩

/-- In dimension `n`, every nonempty supporting block has index at most `n`.
Thus the apparently infinite mask definitions are finite constructions.
@isnad1 id=le.2h3v.s4.6667f4e51830 from=translated src=- shape=d4564332 vocab=492021cd
-/
theorem le_dim_of_inProfileBlock {n t i : ℕ} (hi : i < n)
    (hblock : InProfileBlock t i) : t ≤ n := by
  cases t with
  | zero => omega
  | succ t =>
      have ht := le_profileCutoff t
      have hs : profileCutoff t ≤ i := hblock.1
      omega

/-- A finite-dimensional first-mask membership has a finite block witness.
@isnad1 id=iff.0h3v.s6.2bf33c480bb7 from=translated src=- shape=e04cb5b8 vocab=5150e098
-/
theorem profileFirstMask_iff_exists_fin {n : ℕ} (i j : Fin n) :
    ProfileFirstMask i.val j.val ↔ ∃ t : Fin (n + 1),
      t.val % 2 = 0 ∧ InProfileBlock t i.val ∧ InProfileBlock t j.val := by
  constructor
  · rintro ⟨t, ht, hi, hj⟩
    exact ⟨⟨t, Nat.lt_succ_of_le (le_dim_of_inProfileBlock i.isLt hi)⟩, ht, hi, hj⟩
  · rintro ⟨t, ht, hi, hj⟩
    exact ⟨t, ht, hi, hj⟩

/-- A finite-dimensional odd-mask membership has a finite block witness.
@isnad1 id=iff.0h3v.s6.c911f5a35145 from=translated src=- shape=e04cb5b8 vocab=45075d13
-/
theorem profileOddBlockMask_iff_exists_fin {n : ℕ} (i j : Fin n) :
    ProfileOddBlockMask i.val j.val ↔ ∃ t : Fin (n + 1),
      t.val % 2 = 1 ∧ InProfileBlock t i.val ∧ InProfileBlock t j.val := by
  constructor
  · rintro ⟨t, ht, hi, hj⟩
    exact ⟨⟨t, Nat.lt_succ_of_le (le_dim_of_inProfileBlock i.isLt hi)⟩, ht, hi, hj⟩
  · rintro ⟨t, ht, hi, hj⟩
    exact ⟨t, ht, hi, hj⟩

/-- Keep matrix entries in the even diagonal-block mask.-/
def profileFirstPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if ProfileFirstMask i.val j.val then A i j else 0

/-- Keep matrix entries in the odd diagonal-block mask after removing the
even-mask overlaps.-/
def profileSecondPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if ProfileSecondMask i.val j.val then A i j else 0

/-- Keep the residual matrix entries outside all diagonal-block masks.-/
def profileRemainderPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if ProfileRemainderMask i.val j.val then A i j else 0

/-- The three explicitly constructed parts sum to the original matrix.
@isnad1 id=eq.0h2v.s6.f2da7641b949 from=translated src=- shape=56b8e426 vocab=6eae8f11
-/
theorem profileFirstPart_add_secondPart_add_remainderPart {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    profileFirstPart A + profileSecondPart A + profileRemainderPart A = A := by
  classical
  ext i j
  simp only [Matrix.add_apply, profileFirstPart, profileSecondPart,
    profileRemainderPart, ProfileSecondMask, ProfileRemainderMask]
  split_ifs <;> simp_all

/-- All three parts of a symmetric profile are symmetric.
@isnad1 id=and.1h2v.s5.bfce13b690f2 from=translated src=- shape=67758466 vocab=df9f1386
-/
theorem isSymm_profile_parts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    (profileFirstPart A).IsSymm ∧ (profileSecondPart A).IsSymm ∧
      (profileRemainderPart A).IsSymm := by
  have h (i j) : A j i = A i j := congrFun (congrFun hA i) j
  refine ⟨?_, ?_, ?_⟩ <;> ext i j
  · simp only [Matrix.transpose_apply, profileFirstPart, h i j]
    rw [profileFirstMask_comm j.val i.val]
  · simp only [Matrix.transpose_apply, profileSecondPart, h i j]
    rw [profileSecondMask_comm j.val i.val]
  · simp only [Matrix.transpose_apply, profileRemainderPart, h i j]
    rw [profileRemainderMask_comm j.val i.val]

end NLAlib
