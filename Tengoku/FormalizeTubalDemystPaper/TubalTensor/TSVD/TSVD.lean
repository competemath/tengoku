import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TSVD.Unitary
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TSVD.FDiagonal
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TransformDomain.Transform
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Prerequisites.SVD
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.PartialOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/SVD/TSVD.lean
  Theorem 30: t-SVD existence.

  Every tubal matrix A ∈ K_M^{m×p} has a decomposition
    A = U ⋆_M S ⋆_M V^H
  where U, V are ⋆_M-unitary and S is f-diagonal.

  Proof strategy: apply the paired family SVD to the frontal
  slices of the transformed tensor Â, then use the paired structure to
  invoke invTransform round-trip, and verify all required properties
  via transform injectivity.
-/

namespace TubalTensor

open BigOperators Matrix Classical

variable {n : ℕ} {td : TubalData n} {m p l : ℕ}

/-! ## Helper lemmas -/

/-- Key tube-level lemma: M(a*) = conj(Ma).-/
private theorem applyM_toComplex_star (a : KM n td) :
    td.applyM (toComplex (KM.toFun (star a))) =
    vecConj (td.applyM (toComplex (KM.toFun a))) := by
  simp only [KM.toFun_star]
  rw [starConjM_eq_starConjC]
  show td.applyM (td.applyMinv (vecConj (td.applyM (toComplex (KM.toFun a))))) = _
  rw [td.applyM_applyMinv]

/-- The transform of Aᴴ equals the facewise conjugate transpose.-/
theorem transform_conjTranspose (A : TubalMatrix m p n td) :
    transform Aᴴ = fun k => (transform A k)ᴴ := by
  funext k i j
  simp only [transform_apply, conjTranspose_apply]
  have h := congr_fun (applyM_toComplex_star (A j i)) k
  rw [h]
  rw [vecConj_apply]
  rfl

/-- The transform of the identity tubal matrix is the identity on each slice.-/
theorem transform_one :
    transform (1 : TubalMatrix m m n td) = fun _ => 1 := by
  funext k i j
  simp only [transform_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    simp only [KM.toFun_one, toComplex_unitTube]
    exact congr_fun (td.applyM_applyMinv (allOnes n)) k
  · simp only [KM.toFun_zero, toComplex_zero]
    exact congr_fun (Matrix.mulVec_zero td.M) k

/-! ## Paired-structure tube helpers -/

/-! ## Conjugation helpers for SVD -/

/-- Entrywise conjugation of a matrix.-/
private noncomputable def matConj {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) :
    Matrix (Fin m) (Fin p) ℂ :=
  fun i j => starRingEnd ℂ (A i j)

private theorem matConj_apply {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ)
    (i : Fin m) (j : Fin p) : matConj A i j = starRingEnd ℂ (A i j) := rfl

private theorem matConj_mul {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℂ)
    (B : Matrix (Fin p) (Fin l) ℂ) : matConj (A * B) = matConj A * matConj B := by
  ext i j
  simp only [matConj_apply, Matrix.mul_apply, map_sum, map_mul]

private theorem matConj_conjTranspose {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) :
    matConj Aᴴ = (matConj A)ᴴ := by
  ext i j
  simp [matConj_apply, conjTranspose_apply]

private theorem matConj_one {m : ℕ} : matConj (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  ext i j; simp only [matConj_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem isUnitary_matConj {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : IsUnitary A) : IsUnitary (matConj A) := by
  show (matConj A)ᴴ * matConj A = 1
  rw [← matConj_conjTranspose, ← matConj_mul, hA.conjTranspose_mul_self, matConj_one]

private theorem matConj_eq_self_of_isSVDDiag {m p : ℕ} {S : Matrix (Fin m) (Fin p) ℂ}
    (hS : IsSVDDiagC S) : matConj S = S := by
  ext i j
  simp only [matConj_apply]
  by_cases hij : (i : ℕ) = (j : ℕ)
  · rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im.mpr (hS.2.1 i j hij).1]
  · rw [hS.1 i j hij, map_zero]

private theorem svd_conj_decomp {m' p' : ℕ}
    {A : Matrix (Fin m') (Fin p') ℂ} {U : Matrix (Fin m') (Fin m') ℂ}
    {S : Matrix (Fin m') (Fin p') ℂ} {V : Matrix (Fin p') (Fin p') ℂ}
    (hS : IsSVDDiagC S) (hdecomp : A = U * S * Vᴴ) :
    matConj A = matConj U * S * (matConj V)ᴴ := by
  rw [hdecomp, matConj_mul, matConj_mul, matConj_conjTranspose,
      matConj_eq_self_of_isSVDDiag hS]

/-- A real matrix (all entries real) satisfies IsRealMatrix.-/
private theorem isRealMatrix_of_pairedStructure_realRow {m p : ℕ}
    (Ahat : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (hpaired : ∀ i j, HasRealPairedStructure td (fun k => Ahat k i j))
    {k : Fin n} (hreal : IsRealRow td.M k) :
    IsRealMatrix (Ahat k) := by
  intro i j
  exact (hpaired i j).1 k hreal

/-! ## Paired family SVD

  When a family of matrices has conjugate-paired structure (as arises from
  the transform of a real tubal matrix), the SVD factors can be chosen to
  also have paired structure entry-by-entry.

  This follows from: (1) the SVD of a real matrix can be chosen with
  real unitary factors (`matrix_svd` over ℝ), and (2) conjugating an SVD gives
  an SVD of the conjugated matrix (`svd_conj_decomp`).
-/

/-- **Paired family SVD.**
    Proved from `matrix_svd` (proved over any `RCLike` field).-/
theorem matrix_svd_paired {n : ℕ} (td : TubalData n) (m p : ℕ)
    (Ahat : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (hpaired : ∀ i j, HasRealPairedStructure td (fun k => Ahat k i j)) :
    ∃ (Uhat : Fin n → Matrix (Fin m) (Fin m) ℂ)
      (Shat : Fin n → Matrix (Fin m) (Fin p) ℂ)
      (Vhat : Fin n → Matrix (Fin p) (Fin p) ℂ),
      (∀ k, IsUnitary (Uhat k)) ∧
      (∀ k, IsUnitary (Vhat k)) ∧
      (∀ k, IsSVDDiagC (Shat k)) ∧
      (∀ k, Ahat k = Uhat k * Shat k * (Vhat k)ᴴ) ∧
      (∀ i j, HasRealPairedStructure td (fun k => Uhat k i j)) ∧
      (∀ i j, HasRealPairedStructure td (fun k => Shat k i j)) ∧
      (∀ i j, HasRealPairedStructure td (fun k => Vhat k i j)) := by
  -- Step 1: Get per-slice SVD factors.
  -- For each k, obtain U, S, V decomposing Ahat k.
  -- Use matrix_svd for all slices (works over any RCLike, including ℝ and ℂ).
  -- We need: for real rows, the factors are real; for all slices, valid SVD.
  --
  -- Strategy: Apply SVD to each slice independently. For conjugate pair (i,k),
  -- the "second" member's factors are derived by conjugation from the "first."
  -- For real rows, use the real SVD to get real factors.
  --
  -- To identify "first" vs "second" in a conjugate pair, we use the order on Fin n:
  -- the member with smaller index is canonical.

  -- Helper: Ahat at a conjugate row is the entrywise conjugate of Ahat at its partner.
  have ahat_conj : ∀ i k, k ≠ i → IsConjRow td.M i k → Ahat k = matConj (Ahat i) := by
    intro i k hki hconj
    ext a b
    simp only [matConj_apply]
    exact (hpaired a b).2 i k hki hconj

  -- For each slice, pick an SVD. For real rows, use real SVD.
  -- We build a combined result per slice.
  have svd_per_slice : ∀ k,
      ∃ (U : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin m) (Fin p) ℂ)
        (V : Matrix (Fin p) (Fin p) ℂ),
        IsUnitary U ∧ IsUnitary V ∧ IsSVDDiagC S ∧ Ahat k = U * S * Vᴴ ∧
        (IsRealRow td.M k → IsRealMatrix U ∧ IsRealMatrix V) := by
    intro k
    by_cases hreal : IsRealRow td.M k
    · -- Extract real part and apply real SVD
      have hAk_real := isRealMatrix_of_pairedStructure_realRow Ahat hpaired hreal
      let Ak_real := realPartMatrix (Ahat k) hAk_real
      have hAk_eq : Ahat k = Ak_real.map Complex.ofReal := (realPartMatrix_map_eq _ hAk_real).symm
      let svd_r := matrix_svd m p Ak_real
      let svd := svd_r.toComplex
      have hsvd_eq : Ahat k = svd.U * toComplexMatrix svd.S * svd.Vᴴ := by
        rw [hAk_eq]; exact svd.hA_eq
      exact ⟨svd.U, toComplexMatrix svd.S, svd.V, svd.hU_unitary, svd.hV_unitary,
        svd.hS_svdDiag.toComplex, hsvd_eq,
        fun _ => ⟨svd_r.toComplex_isRealMatrix_U, svd_r.toComplex_isRealMatrix_V⟩⟩
    · let svd := matrix_svd m p (Ahat k)
      exact ⟨svd.U, toComplexMatrix svd.S, svd.V, svd.hU_unitary, svd.hV_unitary,
        svd.hS_svdDiag.toComplex, svd.hA_eq, fun h => absurd h hreal⟩
  choose U0 S0 V0 hU0u hV0u hS0d hSVD0 hreal0 using svd_per_slice

  -- Step 2: Build the paired families.
  -- For each k, if IsRealRow: use U0/S0/V0 (which have real factors).
  -- For conjugate pair (i,k) with i ≠ k: at the "canonical" member (min index),
  -- use U0; at the partner, use matConj(U0 of canonical), etc.
  -- We define: for non-real k with partner k' (from IsRealPaired),
  --   if k < k': Uhat k = U0 k, Shat k = S0 k, Vhat k = V0 k
  --   if k > k': Uhat k = matConj(U0 k'), Shat k = S0 k', Vhat k = matConj(V0 k')
  -- This ensures Uhat k = matConj(Uhat k') for conjugate pairs.

  -- First, get the partner function for non-real rows.
  -- For non-real row k, partner(k) is the unique conjugate partner.
  have partner_exists : ∀ k, ¬IsRealRow td.M k →
      ∃ k', k' ≠ k ∧ IsConjRow td.M k k' ∧
        (∀ l, l ≠ k → IsConjRow td.M k l → l = k') := by
    intro k hk
    exact (td.hM_real k).resolve_left hk
  -- Choose partners
  choose partner hpartner_ne hpartner_conj hpartner_unique using
    (fun k hk => partner_exists k hk)

  -- Key property: partner is an involution (partner of partner = self)
  -- If k is not real and partner(k) = k', then k' is not real and partner(k') = k.
  have partner_symm : ∀ k (hk : ¬IsRealRow td.M k),
      ¬IsRealRow td.M (partner k hk) ∧
      ∀ (hk' : ¬IsRealRow td.M (partner k hk)),
        partner (partner k hk) hk' = k := by
    intro k hk
    set k' := partner k hk
    have hne := hpartner_ne k hk  -- k' ≠ k
    have hconj := hpartner_conj k hk  -- IsConjRow td.M k k'
    -- k' is not real: if it were real, its row would be self-conjugate,
    -- but it's conjugate to k (a different row), contradiction.
    constructor
    · intro hreal_k'
      -- If k' is real, then IsConjRow M k' k' (self-conjugate)
      -- But IsConjRow M k k' means row k' = conj(row k)
      -- And IsRealRow k' means row k' is real
      -- So row k = conj(row k') = row k' (since k' is real)
      -- But rows k and k' of an invertible matrix must be different for k ≠ k'
      have hconj_sym : IsConjRow td.M k' k := isConjRow_symm hconj
      -- row k = conj(row k') = row k' (since k' is real)
      have hrows : ∀ j, td.M k j = td.M k' j := by
        intro j
        have h1 := hconj_sym j  -- M k j = conj(M k' j)
        have h2 := hreal_k' j   -- (M k' j).im = 0
        rw [h1, starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im.mpr h2]
      -- Two identical rows of an invertible matrix is a contradiction
      have h1 : (td.M * td.M_inv) k k = 1 := by
        rw [td.hM_right_inv, Matrix.one_apply_eq]
      have h2 : (td.M * td.M_inv) k' k = 0 := by
        rw [td.hM_right_inv, Matrix.one_apply_ne hne]
      have heq : (td.M * td.M_inv) k k = (td.M * td.M_inv) k' k := by
        simp only [Matrix.mul_apply]; congr 1; ext l; rw [hrows]
      exact one_ne_zero (h1.symm.trans (heq ▸ h2))
    · intro hk'
      -- partner(k') should be k
      -- IsConjRow M k k' means IsConjRow M k' k (by symmetry)
      have hconj_sym : IsConjRow td.M k' k := isConjRow_symm hconj
      exact (hpartner_unique (partner k hk) hk' k hne.symm hconj_sym).symm

  -- Helper: a real row cannot have a distinct conjugate partner
  have real_no_partner : ∀ k k', k' ≠ k → IsConjRow td.M k k' →
      IsRealRow td.M k → False := by
    intro k k' hkk' hconj_row hreal
    have hrows : ∀ l, td.M k' l = td.M k l := by
      intro l; rw [hconj_row l, starRingEnd_apply, Complex.star_def,
        Complex.conj_eq_iff_im.mpr (hreal l)]
    have h1 : (td.M * td.M_inv) k k = 1 := by rw [td.hM_right_inv, Matrix.one_apply_eq]
    have h2 : (td.M * td.M_inv) k' k = 0 := by
      rw [td.hM_right_inv, Matrix.one_apply_ne hkk']
    have heq : (td.M * td.M_inv) k k = (td.M * td.M_inv) k' k := by
      simp only [Matrix.mul_apply]; congr 1; ext l; rw [hrows]
    exact one_ne_zero (h1.symm.trans (heq ▸ h2))

  -- Step 3: Define corrected families using non-dependent total functions.

  -- Total partner function: returns partner for non-real rows, k for real rows
  let tpartner : Fin n → Fin n := fun k =>
    if hk : IsRealRow td.M k then k else partner k hk

  have tpartner_real : ∀ k, IsRealRow td.M k → tpartner k = k :=
    fun k hk => dite_eq_left hk

  have tpartner_nonreal : ∀ k (hk : ¬IsRealRow td.M k), tpartner k = partner k hk := by
    intro k hk; exact dite_eq_right hk

  have tpartner_not_real : ∀ k, ¬IsRealRow td.M k → ¬IsRealRow td.M (tpartner k) := by
    intro k hk; rw [tpartner_nonreal k hk]; exact (partner_symm k hk).1

  have tpartner_ne : ∀ k, ¬IsRealRow td.M k → tpartner k ≠ k := by
    intro k hk; rw [tpartner_nonreal k hk]; exact hpartner_ne k hk

  have tpartner_conj : ∀ k, ¬IsRealRow td.M k → IsConjRow td.M k (tpartner k) := by
    intro k hk; rw [tpartner_nonreal k hk]; exact hpartner_conj k hk

  have tpartner_invol : ∀ k, ¬IsRealRow td.M k → tpartner (tpartner k) = k := by
    intro k hk
    rw [tpartner_nonreal k hk, tpartner_nonreal _ (partner_symm k hk).1]
    exact (partner_symm k hk).2 (partner_symm k hk).1

  -- is_canon k means k is the canonical member of its class (k ≤ tpartner k)
  let is_canon : Fin n → Prop := fun k => k ≤ tpartner k

  have canon_real : ∀ k, IsRealRow td.M k → is_canon k := by
    intro k hk; show k ≤ tpartner k; rw [tpartner_real k hk]

  -- If k is not canonical, then tpartner k IS canonical
  have canon_partner : ∀ k, ¬is_canon k → is_canon (tpartner k) := by
    intro k hk
    by_cases hr : IsRealRow td.M k
    · exact absurd (canon_real k hr) hk
    · show tpartner k ≤ tpartner (tpartner k)
      rw [tpartner_invol k hr]; exact le_of_lt (not_le.mp hk)

  -- If k is canonical and not real, tpartner k is NOT canonical
  have noncanon_partner : ∀ k, is_canon k → ¬IsRealRow td.M k → ¬is_canon (tpartner k) := by
    intro k hc hk h
    rw [show is_canon (tpartner k) ↔ tpartner k ≤ tpartner (tpartner k) from Iff.rfl] at h
    rw [tpartner_invol k hk] at h
    exact tpartner_ne k hk (le_antisymm h hc)

  -- Define the output families
  let Uhat : Fin n → Matrix (Fin m) (Fin m) ℂ := fun k =>
    if is_canon k then U0 k else matConj (U0 (tpartner k))
  let Shat : Fin n → Matrix (Fin m) (Fin p) ℂ := fun k =>
    if is_canon k then S0 k else S0 (tpartner k)
  let Vhat : Fin n → Matrix (Fin p) (Fin p) ℂ := fun k =>
    if is_canon k then V0 k else matConj (V0 (tpartner k))

  -- Helper for the SVD-diagonal conjugate-self property
  have svd_diag_conj_self : ∀ k (i : Fin m) (j : Fin p),
      starRingEnd ℂ (S0 k i j) = S0 k i j := by
    intro k i j
    by_cases hij : (i : ℕ) = (j : ℕ)
    · rw [starRingEnd_apply, Complex.star_def,
        Complex.conj_eq_iff_im.mpr ((hS0d k).2.1 i j hij).1]
    · rw [(hS0d k).1 i j hij, map_zero]

  refine ⟨Uhat, Shat, Vhat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  -- Property 1: ∀ k, IsUnitary (Uhat k)
  · intro k; show IsUnitary (if is_canon k then U0 k else matConj (U0 (tpartner k)))
    split_ifs
    · exact hU0u k
    · exact isUnitary_matConj (hU0u _)

  -- Property 2: ∀ k, IsUnitary (Vhat k)
  · intro k; show IsUnitary (if is_canon k then V0 k else matConj (V0 (tpartner k)))
    split_ifs
    · exact hV0u k
    · exact isUnitary_matConj (hV0u _)

  -- Property 3: ∀ k, IsSVDDiagC (Shat k)
  · intro k; show IsSVDDiagC (if is_canon k then S0 k else S0 (tpartner k))
    split_ifs
    · exact hS0d k
    · exact hS0d _

  -- Property 4: ∀ k, Ahat k = Uhat k * Shat k * (Vhat k)ᴴ
  · intro k
    show Ahat k = (if is_canon k then U0 k else matConj (U0 (tpartner k))) *
      (if is_canon k then S0 k else S0 (tpartner k)) *
      (if is_canon k then V0 k else matConj (V0 (tpartner k)))ᴴ
    split_ifs with hc
    · exact hSVD0 k
    · -- k is not canonical, so k > tpartner k, meaning k is non-real
      have hk : ¬IsRealRow td.M k := fun hr => hc (canon_real k hr)
      rw [← matConj_conjTranspose, ahat_conj (tpartner k) k (tpartner_ne k hk).symm
        (isConjRow_symm (tpartner_conj k hk))]
      exact svd_conj_decomp (hS0d _) (hSVD0 _)

  -- Properties 5, 6, 7: paired structure
  -- We prove a common helper for the conjugate-pair case
  -- For each property, at a real row k, the value comes from real SVD factors.
  -- For a conjugate pair (k, k'), one uses U0 and the other uses matConj(U0).

  -- Property 5: ∀ i j, HasRealPairedStructure td (fun k => Uhat k i j)
  · intro i j; constructor
    · intro k hreal
      show ((if is_canon k then U0 k else matConj (U0 (tpartner k))) i j).im = 0
      rw [ite_eq_left (canon_real k hreal)]
      exact (hreal0 k hreal).1 i j
    · intro k k' hkk' hconj_row
      show (if is_canon k' then U0 k' else matConj (U0 (tpartner k'))) i j =
           starRingEnd ℂ ((if is_canon k then U0 k else matConj (U0 (tpartner k))) i j)
      have hk : ¬IsRealRow td.M k := fun h => real_no_partner k k' hkk' hconj_row h
      have hk' : ¬IsRealRow td.M k' := by
        intro h; exact real_no_partner k' k hkk'.symm (isConjRow_symm hconj_row) h
      -- k' = tpartner k (the unique partner)
      have hk'_eq : k' = tpartner k := by
        rw [tpartner_nonreal k hk]; exact hpartner_unique k hk k' hkk' hconj_row
      by_cases hc : is_canon k
      · -- k is canonical: Uhat k = U0 k, k' is non-canonical: Uhat k' = matConj (U0 (tpartner k'))
        rw [ite_eq_left hc, ite_eq_right (hk'_eq ▸ noncanon_partner k hc hk)]
        -- tpartner k' = tpartner (tpartner k) = k
        rw [show tpartner k' = k from by rw [hk'_eq, tpartner_invol k hk]]
        rfl
      · -- k is non-canonical: Uhat k = matConj (U0 (tpartner k))
        -- k' is canonical: since k' = tpartner k, and k is not canonical, k' IS canonical
        rw [ite_eq_right hc, ite_eq_left (hk'_eq ▸ canon_partner k hc)]
        rw [hk'_eq]
        simp only [matConj_apply, starRingEnd_apply, star_star]

  -- Property 6: ∀ i j, HasRealPairedStructure td (fun k => Shat k i j)
  · intro i j; constructor
    · intro k hreal
      show ((if is_canon k then S0 k else S0 (tpartner k)) i j).im = 0
      rw [ite_eq_left (canon_real k hreal)]
      by_cases hij : (i : ℕ) = (j : ℕ)
      · exact ((hS0d k).2.1 i j hij).1
      · rw [(hS0d k).1 i j hij]; rfl
    · intro k k' hkk' hconj_row
      show (if is_canon k' then S0 k' else S0 (tpartner k')) i j =
           starRingEnd ℂ ((if is_canon k then S0 k else S0 (tpartner k)) i j)
      have hk : ¬IsRealRow td.M k := fun h => real_no_partner k k' hkk' hconj_row h
      have hk' : ¬IsRealRow td.M k' := by
        intro h; exact real_no_partner k' k hkk'.symm (isConjRow_symm hconj_row) h
      have hk'_eq : k' = tpartner k := by
        rw [tpartner_nonreal k hk]; exact hpartner_unique k hk k' hkk' hconj_row
      by_cases hc : is_canon k
      · rw [ite_eq_left hc, ite_eq_right (hk'_eq ▸ noncanon_partner k hc hk)]
        rw [show tpartner k' = k from by rw [hk'_eq, tpartner_invol k hk]]
        exact (svd_diag_conj_self k i j).symm
      · rw [ite_eq_right hc, ite_eq_left (hk'_eq ▸ canon_partner k hc)]
        rw [hk'_eq]
        exact (svd_diag_conj_self _ i j).symm

  -- Property 7: ∀ i j, HasRealPairedStructure td (fun k => Vhat k i j)
  · intro i j; constructor
    · intro k hreal
      show ((if is_canon k then V0 k else matConj (V0 (tpartner k))) i j).im = 0
      rw [ite_eq_left (canon_real k hreal)]
      exact (hreal0 k hreal).2 i j
    · intro k k' hkk' hconj_row
      show (if is_canon k' then V0 k' else matConj (V0 (tpartner k'))) i j =
           starRingEnd ℂ ((if is_canon k then V0 k else matConj (V0 (tpartner k))) i j)
      have hk : ¬IsRealRow td.M k := fun h => real_no_partner k k' hkk' hconj_row h
      have hk' : ¬IsRealRow td.M k' := by
        intro h; exact real_no_partner k' k hkk'.symm (isConjRow_symm hconj_row) h
      have hk'_eq : k' = tpartner k := by
        rw [tpartner_nonreal k hk]; exact hpartner_unique k hk k' hkk' hconj_row
      by_cases hc : is_canon k
      · rw [ite_eq_left hc, ite_eq_right (hk'_eq ▸ noncanon_partner k hc hk)]
        rw [show tpartner k' = k from by rw [hk'_eq, tpartner_invol k hk]]
        rfl
      · rw [ite_eq_right hc, ite_eq_left (hk'_eq ▸ canon_partner k hc)]
        rw [hk'_eq]
        simp only [matConj_apply, starRingEnd_apply, star_star]

/-! ## Helpers for singular tube ordering -/

/-! ## TSVD structure

A `TSVD` bundles the three factors (U, S, V) of a t-SVD together with all
their properties: ⋆_M-unitarity, f-diagonality, the decomposition identity,
and per-slice SVD properties in the transform domain. -/

/-- The t-SVD of a tubal matrix, bundling U, S, V and all properties.-/
structure TSVD {m p n : ℕ} {td : TubalData n} (A : TubalMatrix m p n td) where
  /-- The left ⋆_M-unitary factor (m × m).-/
  U : TubalMatrix m m n td
  /-- The f-diagonal factor (m × p).-/
  S : TubalMatrix m p n td
  /-- The right ⋆_M-unitary factor (p × p).-/
  V : TubalMatrix p p n td
  /-- U is ⋆_M-unitary.-/
  hU_unitary : IsStarMUnitary U
  /-- V is ⋆_M-unitary.-/
  hV_unitary : IsStarMUnitary V
  /-- S is f-diagonal.-/
  hS_fdiag : IsFDiagonal S
  /-- The decomposition identity A = U ⋆_M S ⋆_M Vᴴ.-/
  hA_eq : A = U * S * Vᴴ
  /-- Each transform-domain slice of U is unitary.-/
  hU_slice : ∀ k, IsUnitary (transform U k)
  /-- Each transform-domain slice of V is unitary.-/
  hV_slice : ∀ k, IsUnitary (transform V k)
  /-- Each transform-domain slice of S is SVD-diagonal.-/
  hS_svdDiag : ∀ k, IsSVDDiagC (transform S k)
  /-- Per-slice decomposition: Â_k = Û_k Ŝ_k V̂_kᴴ.-/
  hSlice : ∀ k, transform A k = transform U k * transform S k * (transform V k)ᴴ
  /-- Singular tubes are nonneg: σ_i ≥_M 0.-/
  hS_nonneg : ∀ i : Fin (min m p),
    0 ≤ S (Fin.castLE (Nat.min_le_left m p) i) (Fin.castLE (Nat.min_le_right m p) i)
  /-- Singular tubes are non-increasing: i₁ ≤ i₂ → σ_{i₂} ≤_M σ_{i₁}.-/
  hS_ordered : ∀ i₁ i₂ : Fin (min m p), i₁ ≤ i₂ →
    S (Fin.castLE (Nat.min_le_left m p) i₂) (Fin.castLE (Nat.min_le_right m p) i₂) ≤
    S (Fin.castLE (Nat.min_le_left m p) i₁) (Fin.castLE (Nat.min_le_right m p) i₁)

end TubalTensor
