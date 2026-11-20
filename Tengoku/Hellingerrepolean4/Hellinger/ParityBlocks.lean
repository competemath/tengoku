import Tengoku.Hellingerrepolean4.Hellinger.ProductState
import Tengoku.Hellingerrepolean4.Hellinger.FourierCounting
import Tengoku.Hellingerrepolean4.Hellinger.SortedEnumeration
import Tengoku.Hellingerrepolean4.Hellinger.EigenvalueOrder
import Tengoku.Hellingerrepolean4.Hellinger.MatrixReindex
import Tengoku.Hellingerrepolean4.Hellinger.PosteriorState

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual even and odd Walsh-frequency blocks, with sorted enumerations.
Their dimensions, multiplicities, ordering and spectral distance are proved
from the concrete product state. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace Hellinger.ParityBlocks
open Fourier ProductState

abbrev EvenIndex (n : ℕ) := {s : Fourier.Cube (n + 1) // Even (degree s)}
abbrev OddIndex (n : ℕ) := {s : Fourier.Cube (n + 1) // Odd (degree s)}

/--
@isnad1 id=eq.0h1v.s7.38237232853a from=translated src=- shape=5b09d1d5 vocab=7e573413
-/
theorem even_card (n : ℕ) : Fintype.card (EvenIndex n) = 2 ^ n := by
  simpa only [Fintype.subtype_card] using card_even_degree n

/--
@isnad1 id=eq.0h1v.s7.4941398eb375 from=translated src=- shape=5b09d1d5 vocab=0c855fed
-/
theorem odd_card (n : ℕ) : Fintype.card (OddIndex n) = 2 ^ n := by
  simpa only [Fintype.subtype_card] using card_odd_degree n

def evenEquiv (n : ℕ) : Fin (2 ^ n) ≃ EvenIndex n :=
  (finCongr (even_card n).symm).trans (SortedEnumeration.sortedEquiv (fun s => degree s.val))

def oddEquiv (n : ℕ) : Fin (2 ^ n) ≃ OddIndex n :=
  (finCongr (odd_card n).symm).trans (SortedEnumeration.sortedEquiv (fun s => degree s.val))

def evenLevel (n : ℕ) (i : Fin (2 ^ n)) : ℕ := degree (evenEquiv n i).val
def oddLevel (n : ℕ) (i : Fin (2 ^ n)) : ℕ := degree (oddEquiv n i).val

/--
@isnad1 id=monotone.0h1v.s6.2fbe221d826f from=translated src=- shape=3c27d09f vocab=6794e10c
-/
theorem evenLevel_monotone (n : ℕ) : Monotone (evenLevel n) := by
  intro i j hij
  apply SortedEnumeration.sortedEquiv_monotone (fun s : EvenIndex n => degree s.val)
  exact hij

/--
@isnad1 id=monotone.0h1v.s6.c76d0d5299bf from=translated src=- shape=3c27d09f vocab=e075c9d3
-/
theorem oddLevel_monotone (n : ℕ) : Monotone (oddLevel n) := by
  intro i j hij
  apply SortedEnumeration.sortedEquiv_monotone (fun s : OddIndex n => degree s.val)
  exact hij

/--
@isnad1 id=le.0h2v.s5.d2f92f4d7352 from=translated src=- shape=36973c39 vocab=54f95af2
-/
theorem evenLevel_le (n : ℕ) (i : Fin (2 ^ n)) : evenLevel n i ≤ n + 1 :=
  degree_le _

/--
@isnad1 id=le.0h2v.s5.3c6edeb97173 from=translated src=- shape=36973c39 vocab=ca6354d7
-/
theorem oddLevel_le (n : ℕ) (i : Fin (2 ^ n)) : oddLevel n i ≤ n + 1 :=
  degree_le _

/--
@isnad1 id=eq.0h3v.s7.8ae2fedc6d28 from=translated src=- shape=af1550ac vocab=3dc5cd28
-/
theorem subtype_degree_count (d k : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ s : {s : Fourier.Cube d // p (degree s)}, if degree s.val = k then (1 : ℝ) else 0) =
      if p k then (d.choose k : ℝ) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun s : Fourier.Cube d => p (degree s)))
    (by simp) (fun s : Fourier.Cube d => if degree s = k then (1 : ℝ) else 0)]
  rw [Finset.sum_filter]
  have hterm (s : Fourier.Cube d) :
      (if p (degree s) then (if degree s = k then (1 : ℝ) else 0) else 0) =
        if p k then (if degree s = k then 1 else 0) else 0 := by
    by_cases h : degree s = k
    · simp [h]
    · simp [h]
  simp_rw [hterm]
  split_ifs with hk
  · simp only [Finset.sum_boole]
    rw [card_degree]
  · simp

/--
@isnad1 id=eq.0h2v.s6.d7c349151008 from=translated src=- shape=f52b3251 vocab=a6589acf
-/
theorem even_multiplicities (n k : ℕ) :
    (∑ i, if evenLevel n i = k then (1 : ℝ) else 0) =
      ParitySpectrum.evenMultiplicity (n + 1) k := by
  unfold evenLevel
  rw [(evenEquiv n).sum_comp (fun s => if degree s.val = k then (1 : ℝ) else 0)]
  exact subtype_degree_count (n + 1) k Even

/--
@isnad1 id=eq.0h2v.s6.28f06fda7fc0 from=translated src=- shape=f52b3251 vocab=6f4612c6
-/
theorem odd_multiplicities (n k : ℕ) :
    (∑ i, if oddLevel n i = k then (1 : ℝ) else 0) =
      ParitySpectrum.oddMultiplicity (n + 1) k := by
  unfold oddLevel
  rw [(oddEquiv n).sum_comp (fun s => if degree s.val = k then (1 : ℝ) else 0)]
  exact subtype_degree_count (n + 1) k Odd

def evenEigenvalue (n : ℕ) (c : ℝ) (i : Fin (2 ^ n)) : ℝ :=
  eigenvalue (n + 1) c (evenEquiv n i).val

def oddEigenvalue (n : ℕ) (c : ℝ) (i : Fin (2 ^ n)) : ℝ :=
  eigenvalue (n + 1) c (oddEquiv n i).val

/--
@isnad1 id=antitone.1h2v.s6.d727aab5a351 from=translated src=- shape=3b5824ac vocab=7a8b664a
-/
theorem evenEigenvalue_antitone (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (evenEigenvalue n c) := by
  intro i j hij
  exact ParitySpectrum.spectralLevel_antitone (n + 1) _ _
    (by linarith [hc.1]) (by linarith [hc.2]) (by linarith [hc.1])
    _ _ (evenLevel_monotone n hij) (evenLevel_le n j)

/--
@isnad1 id=antitone.1h2v.s6.39066806ad84 from=translated src=- shape=3b5824ac vocab=b2440b6c
-/
theorem oddEigenvalue_antitone (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (oddEigenvalue n c) := by
  intro i j hij
  exact ParitySpectrum.spectralLevel_antitone (n + 1) _ _
    (by linarith [hc.1]) (by linarith [hc.2]) (by linarith [hc.1])
    _ _ (oddLevel_monotone n hij) (oddLevel_le n j)

/--
@isnad1 id=eq.1h2v.s7.712e16663829 from=translated src=- shape=ff15e002 vocab=7ad934ec
-/
theorem actual_parity_spectra_l1 (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, |evenEigenvalue n c i - oddEigenvalue n c i|) = c := by
  exact ParitySpectrum.parity_spectra_l1 n c hc.1 hc.2
    (evenLevel n) (oddLevel n) (evenLevel_monotone n) (oddLevel_monotone n)
    (evenLevel_le n) (oddLevel_le n)
    (fun k _ => even_multiplicities n k) (fun k _ => odd_multiplicities n k)

def parityEquiv (n : ℕ) : EvenIndex n ⊕ OddIndex n ≃ Fourier.Cube (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun _ =>
    Nat.not_even_iff_odd.symm))).trans (Equiv.sumCompl (fun s => Even (degree s)))

def blockEquiv (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fourier.Cube (n + 1) :=
  (Equiv.sumCongr (evenEquiv n) (oddEquiv n)).trans (parityEquiv n)

/--
@isnad1 id=eq.0h2v.s9.7cc011cad215 from=translated src=- shape=ff2f2f8e vocab=435b9d1f
-/
@[simp] theorem blockEquiv_inl (n : ℕ) (i : Fin (2 ^ n)) :
    blockEquiv n (Sum.inl i) = (evenEquiv n i).val := rfl

/--
@isnad1 id=eq.0h2v.s9.fdc21b6f9557 from=translated src=- shape=ff2f2f8e vocab=aa08c720
-/
@[simp] theorem blockEquiv_inr (n : ℕ) (i : Fin (2 ^ n)) :
    blockEquiv n (Sum.inr i) = (oddEquiv n i).val := rfl

/--
@isnad1 id=eq.0h2v.s10.663cc4a88c60 from=translated src=- shape=0b074cdc vocab=89b4ae07
-/
theorem state_diagonal_blocks (n : ℕ) (c : ℝ) :
    (Matrix.diagonal (eigenvalue (n + 1) c)).submatrix (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks (Matrix.diagonal (evenEigenvalue n c)) 0 0
        (Matrix.diagonal (oddEigenvalue n c)) := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal, Matrix.fromBlocks, evenEigenvalue, oddEigenvalue]

def parityDiagonal (n : ℕ) : Matrix (Fourier.Cube n) (Fourier.Cube n) ℝ :=
  Matrix.diagonal (fun s => (-1 : ℝ) ^ degree s)

/--
@isnad1 id=eq.0h1v.s10.e761e3fe399f from=translated src=- shape=56c9d5de vocab=3e6ed0ac
-/
theorem parity_diagonal_blocks (n : ℕ) :
    (parityDiagonal (n + 1)).submatrix (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks 1 0 0 (-1) := by
  unfold parityDiagonal
  rw [Matrix.submatrix_diagonal_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.diagonal, Matrix.fromBlocks, (evenEquiv n i).property.neg_one_pow,
      Matrix.one_apply]
  · simp
  · simp
  · simp [Matrix.diagonal, Matrix.fromBlocks, (oddEquiv n i).property.neg_one_pow,
      Matrix.one_apply]
    split_ifs <;> norm_num

def transformedReflection (n : ℕ) (f : Fourier.Cube n → ℝ) :
    Matrix (Fourier.Cube n) (Fourier.Cube n) ℝ :=
  Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (Matrix.diagonal f)

/--
@isnad1 id=eq.1h2v.s7.f9d671d37b0d from=translated src=- shape=3c661350 vocab=e396c3a3
-/
theorem reflection_squared (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) : Matrix.diagonal f * Matrix.diagonal f = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  rcases hf x with hx | hx <;> simp [hx]

/--
@isnad1 id=eq.1h2v.s7.e42eb33bf57b from=translated src=- shape=cb4fedcc vocab=19572645
-/
theorem transformedReflection_squared (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    transformedReflection n f * transformedReflection n f = 1 := by
  rw [transformedReflection, ← map_mul, reflection_squared n f hf, map_one]

/--
@isnad1 id=ishermit.0h2v.s5.00d3f7fc0105 from=translated src=- shape=128be85d vocab=684426b9
-/
theorem transformedReflection_isHermitian (n : ℕ) (f : Fourier.Cube n → ℝ) :
    (transformedReflection n f).IsHermitian := by
  change star (transformedReflection n f) = transformedReflection n f
  rw [transformedReflection, ← map_star]
  congr 1
  exact Matrix.isHermitian_diagonal_iff.mpr (fun _ => IsSelfAdjoint.all _)

/--
@isnad1 id=eq.1h2v.s7.a834e3756380 from=translated src=- shape=78e95c5d vocab=46589e5c
-/
theorem reflection_anticommutes (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hanti : ∀ x, f (antipode n x) = -f x) :
    Matrix.diagonal f * antipodalMatrix n = -(antipodalMatrix n * Matrix.diagonal f) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp only [← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.mulVec_diagonal,
    Pi.neg_apply, antipodalMatrix_apply, hanti, neg_mul, neg_neg]

/--
@isnad1 id=eq.0h1v.s13.aa10e82cc8e8 from=translated src=- shape=c83d0b1c vocab=b77e07d4
-/
theorem transformed_antipodalMatrix (n : ℕ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (antipodalMatrix n) =
      parityDiagonal n := by
  simpa only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose, parityDiagonal] using antipodalMatrix_diagonalization n

/--
@isnad1 id=eq.1h2v.s7.edb458d47f73 from=translated src=- shape=2a5eca9a vocab=bd78d039
-/
theorem transformedReflection_anticommutes (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hanti : ∀ x, f (antipode n x) = -f x) :
    transformedReflection n f * parityDiagonal n =
      -(parityDiagonal n * transformedReflection n f) := by
  rw [transformedReflection, ← transformed_antipodalMatrix, ← map_mul,
    reflection_anticommutes n f hanti, map_neg, map_mul]

/--
@isnad1 id=eq.2h4v.s7.5d80f40cccab from=translated src=- shape=9a61cfd6 vocab=a9cbbacc
-/
theorem transformedReflection_same_parity_zero (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hanti : ∀ x, f (antipode n x) = -f x) (s t : Fourier.Cube n)
    (heq : (-1 : ℝ) ^ degree s = (-1 : ℝ) ^ degree t) :
    transformedReflection n f s t = 0 := by
  have h := congrFun (congrFun (transformedReflection_anticommutes n f hanti) s) t
  simp only [parityDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h
  rw [heq] at h
  have hn : (-1 : ℝ) ^ degree t ≠ 0 := pow_ne_zero _ (by norm_num)
  have hz : transformedReflection n f s t * (-1 : ℝ) ^ degree t = 0 := by nlinarith [h]
  exact (mul_eq_zero.mp hz).resolve_right hn

def offBlock (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  fun i j => transformedReflection (n + 1) f (evenEquiv n i).val (oddEquiv n j).val

/--
@isnad1 id=eq.1h2v.s10.0a4230fca1ba from=translated src=- shape=97a58349 vocab=6ad2260c
-/
theorem reflection_blocks (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    (transformedReflection (n + 1) f).submatrix (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks 0 (offBlock n f) (offBlock n f).transpose 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact transformedReflection_same_parity_zero (n + 1) f hanti _ _ (by
      simp only [blockEquiv_inl, (evenEquiv n i).property.neg_one_pow,
        (evenEquiv n j).property.neg_one_pow])
  · rfl
  · have h := congrFun (congrFun (transformedReflection_isHermitian (n + 1) f) 
      (evenEquiv n j).val) (oddEquiv n i).val
    exact h
  · exact transformedReflection_same_parity_zero (n + 1) f hanti _ _ (by
      simp only [blockEquiv_inr, (oddEquiv n i).property.neg_one_pow,
        (oddEquiv n j).property.neg_one_pow])

/--
@isnad1 id=eq.2h2v.s9.932793b0718b from=translated src=- shape=aad34993 vocab=ad4a2034
-/
theorem offBlock_mul_transpose (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    offBlock n f * (offBlock n f).transpose = 1 := by
  have h := congrArg (fun M => M.submatrix (blockEquiv n) (blockEquiv n))
    (transformedReflection_squared (n + 1) f hf)
  rw [← Matrix.submatrix_mul_equiv _ _ (blockEquiv n) (blockEquiv n) (blockEquiv n),
    reflection_blocks n f hanti,
    Matrix.fromBlocks_multiply, Matrix.submatrix_one_equiv] at h
  have h₁ := congrArg Matrix.toBlocks₁₁ h
  ext i j
  have hij := congrFun (congrFun h₁ i) j
  simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using hij

def blockUnitary (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℝ :=
  ⟨offBlock n f, Matrix.mem_unitaryGroup_iff.mpr (by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using offBlock_mul_transpose n f hf hanti)⟩

/--
@isnad1 id=eq.0h2v.s13.a90d30ae4f78 from=translated src=- shape=1de334c7 vocab=788bea1c
-/
theorem transformed_state (n : ℕ) (c : ℝ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (state n c) =
      Matrix.diagonal (eigenvalue n c) := by
  simpa only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose] using state_diagonalization n c

/--
@isnad1 id=eq.1h3v.s15.e6cd7e4a7320 from=translated src=- shape=12080b53 vocab=923b6ed0
-/
theorem difference_blocks (n : ℕ) (c : ℝ) (f : Fourier.Cube (n + 1) → ℝ)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary (n + 1))
      (state (n + 1) c - Matrix.diagonal f * state (n + 1) c * Matrix.diagonal f)).submatrix
        (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks
        (Matrix.diagonal (evenEigenvalue n c) -
          offBlock n f * Matrix.diagonal (oddEigenvalue n c) * (offBlock n f).transpose) 0 0
        (Matrix.diagonal (oddEigenvalue n c) -
          (offBlock n f).transpose * Matrix.diagonal (evenEigenvalue n c) * offBlock n f) := by
  simp only [map_sub, map_mul, transformed_state]
  change (Matrix.diagonal (eigenvalue (n + 1) c)).submatrix (blockEquiv n) (blockEquiv n) -
    (transformedReflection (n + 1) f * Matrix.diagonal (eigenvalue (n + 1) c) *
      transformedReflection (n + 1) f).submatrix (blockEquiv n) (blockEquiv n) = _
  rw [← Matrix.submatrix_mul_equiv _ _ (blockEquiv n) (blockEquiv n) (blockEquiv n),
    ← Matrix.submatrix_mul_equiv _ _ (blockEquiv n) (blockEquiv n) (blockEquiv n),
    state_diagonal_blocks, reflection_blocks n f hanti]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal]

/--
@isnad1 id=eq.2h3v.s14.38fa30a99b40 from=translated src=- shape=e80ab0b1 vocab=bd842622
-/
theorem actual_block_trace (n : ℕ) (c : ℝ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    TraceNorm.traceNorm (state (n + 1) c -
      Matrix.diagonal f * state (n + 1) c * Matrix.diagonal f) =
      2 * TraceNorm.traceNorm (Matrix.diagonal (evenEigenvalue n c) -
        Unitary.conjStarAlgAut ℝ _ (blockUnitary n f hf hanti)
          (Matrix.diagonal (oddEigenvalue n c))) := by
  rw [← TraceNorm.traceNorm_conjugate (hadamardUnitary (n + 1)),
    ← TraceNorm.traceNorm_submatrix_equiv _ (blockEquiv n), difference_blocks n c f hanti]
  have h := TraceNorm.traceNorm_paired_difference (blockUnitary n f hf hanti)
    (Matrix.diagonal (evenEigenvalue n c)) (Matrix.diagonal (oddEigenvalue n c))
  simpa only [Unitary.conjStarAlgAut_apply, blockUnitary, Unitary.coe_star,
    Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using h

/--
@isnad1 id=le.3h3v.s10.39c10d80ef98 from=translated src=- shape=bdd6fa3e vocab=1146e1ec
-/
theorem antipodal_trace_lower_bound (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (f : Fourier.Cube (n + 1) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    c ≤ TraceNorm.traceNorm (state (n + 1) c -
      Matrix.diagonal f * state (n + 1) c * Matrix.diagonal f) / 2 := by
  rw [actual_block_trace n c f hf hanti]
  have h := TraceNorm.sorted_diagonal_distance_le_traceNorm
    (evenEigenvalue n c) (oddEigenvalue n c)
    (evenEigenvalue_antitone n c hc) (oddEigenvalue_antitone n c hc)
    (blockUnitary n f hf hanti)
  rw [actual_parity_spectra_l1 n c hc] at h
  linarith

/--
@isnad1 id=le.3h3v.s9.398e0fcca28b from=translated src=- shape=d5134ecc vocab=a065e826
-/
theorem antipodal_hellinger (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    root ρ ≤ mean (fun y => root ((cubeBSC (n + 1) ρ hρ).apply f y)) := by
  have hc : root ρ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])⟩
  exact (antipodal_trace_lower_bound n (root ρ) hc
    f hf hanti).trans (PosteriorState.bsc_lifting (n + 1) f hf ρ hρ)

end Hellinger.ParityBlocks
