import Tengoku.PaperCLean.PaperC.Coding.HammingBound
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank and parity of the defect code

This file formalizes the exact linear-algebraic step in Proposition 3.2.
For a binary matrix with `m` columns and `r` rows, rank--nullity gives

`m - r ≤ finrank F₂ (ker A)`.

The paper uses columns obtained by appending a constant coordinate `1` to
the small-prime parity vector of an integer.  The appended coordinate forces
every kernel word to have even Hamming weight.  If the listed small primes
cover every nonzero coordinate of the full parity vectors, the same kernel
equations imply that the product selected by the word is a square.

The coverage hypothesis is essential for the last conclusion: even weight,
or vanishing only on a proper subset of prime coordinates, does not by itself
make a product a square.
-/

namespace PaperC
namespace DefectCodeRank

open Finset

/--
The safe truncated nullity bound for a binary linear map with `m` input
coordinates and `r` output coordinates.
@isnad1 id=le.0h3v.s10.27efd17729ae from=translated src=- shape=2124a004 vocab=5bf234af
-/
theorem columns_sub_rows_le_finrank_ker {m r : ℕ}
    (A : (Fin m → F₂) →ₗ[F₂] (Fin r → F₂)) :
    m - r ≤ Module.finrank F₂ (LinearMap.ker A) := by
  have hrank :
      Module.finrank F₂ (LinearMap.range A) ≤ r := by
    simpa only [Module.finrank_fin_fun] using
      (LinearMap.range A).finrank_le
  have hnullity :
      Module.finrank F₂ (LinearMap.range A) +
          Module.finrank F₂ (LinearMap.ker A) =
        m := by
    simpa only [Module.finrank_fin_fun] using
      A.finrank_range_add_finrank_ker
  omega

/-- Append a final coordinate equal to one to a binary column.-/
def appendOne {r : ℕ} (v : Fin r → F₂) : Fin (r + 1) → F₂ :=
  Fin.lastCases 1 v

/--
@isnad1 id=eq.0h2v.s5.797cfa38ac9b from=translated src=- shape=9320f307 vocab=b7d0c9ba
-/
@[simp]
theorem appendOne_last {r : ℕ} (v : Fin r → F₂) :
    appendOne v (Fin.last r) = 1 := by
  simp [appendOne]

/--
@isnad1 id=eq.0h3v.s4.9c1cfd268d77 from=translated src=- shape=6d29024d vocab=4516fc17
-/
@[simp]
theorem appendOne_castSucc {r : ℕ} (v : Fin r → F₂) (j : Fin r) :
    appendOne v j.castSucc = v j := by
  simp [appendOne]

/--
The linear map whose columns are `(columns i, 1)`.
The output has `r + 1` rows.-/
noncomputable def augmentedColumnMap {m r : ℕ}
    (columns : Fin m → (Fin r → F₂)) :
    (Fin m → F₂) →ₗ[F₂] (Fin (r + 1) → F₂) :=
  Fintype.linearCombination F₂ (fun i ↦ appendOne (columns i))

/-- Rank--nullity for the augmented matrix: its codimension is at most `r + 1`.
@isnad1 id=le.0h3v.s10.88c04e8c56e7 from=translated src=- shape=c13c939c vocab=2b7b064f
-/
theorem columns_sub_augmentedRows_le_finrank_ker {m r : ℕ}
    (columns : Fin m → (Fin r → F₂)) :
    m - (r + 1) ≤
      Module.finrank F₂ (LinearMap.ker (augmentedColumnMap columns)) :=
  columns_sub_rows_le_finrank_ker (augmentedColumnMap columns)

/--
@isnad1 id=eq.0h5v.s9.7b4f26040809 from=translated src=- shape=0d0a39bf vocab=b398649f
-/
theorem augmentedColumnMap_apply_castSucc {m r : ℕ}
    (columns : Fin m → (Fin r → F₂)) (x : Fin m → F₂) (j : Fin r) :
    augmentedColumnMap columns x j.castSucc =
      ∑ i : Fin m, x i * columns i j := by
  simp [augmentedColumnMap, Fintype.linearCombination_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h4v.s9.5ea79d6bb4c4 from=translated src=- shape=4513f134 vocab=58e2687b
-/
theorem augmentedColumnMap_apply_last {m r : ℕ}
    (columns : Fin m → (Fin r → F₂)) (x : Fin m → F₂) :
    augmentedColumnMap columns x (Fin.last r) = ∑ i : Fin m, x i := by
  simp [augmentedColumnMap, Fintype.linearCombination_apply, smul_eq_mul]

/--
Over `F₂`, summing over the support of a word is the same as weighting by
the word's coordinates.
@isnad1 id=eq.0h3v.s6.0de4603c589b from=translated src=- shape=019bdf0a vocab=179d3a97
-/
theorem sum_wordSupport_eq_weighted_sum {m : ℕ}
    (x : Fin m → F₂) (a : Fin m → F₂) :
    ∑ i ∈ HammingBound.wordSupport x, a i =
      ∑ i : Fin m, x i * a i := by
  classical
  rw [HammingBound.wordSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x i = 0
  · simp [hxi]
  · have hxone : x i = 1 :=
      HammingBound.eq_one_of_ne_zero (x i) hxi
    simp [hxi, hxone]

/-- A kernel word of an augmented-column matrix has even Hamming weight.
@isnad1 id=even.1h4v.s9.2af41f4e437e from=translated src=- shape=127ee2b4 vocab=65b9d064
-/
theorem even_hammingNorm_of_mem_ker_augmentedColumnMap {m r : ℕ}
    (columns : Fin m → (Fin r → F₂)) (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker (augmentedColumnMap columns)) :
    Even (hammingNorm x) := by
  have hlast : ∑ i : Fin m, x i = 0 := by
    have hzero := congrFun (LinearMap.mem_ker.mp hx) (Fin.last r)
    simpa [augmentedColumnMap_apply_last] using hzero
  have hweight :
      ((hammingNorm x : ℕ) : F₂) = 0 := by
    rw [← HammingBound.card_wordSupport]
    calc
      ((HammingBound.wordSupport x).card : F₂) =
          ∑ i ∈ HammingBound.wordSupport x, (1 : F₂) := by
            simp
      _ = ∑ i : Fin m, x i * 1 := sum_wordSupport_eq_weighted_sum x _
      _ = 0 := by simpa using hlast
  exact even_iff_two_dvd.mpr
    ((ZMod.natCast_eq_zero_iff (hammingNorm x) 2).mp hweight)

/-- The small-prime parity column of an integer.-/
noncomputable def smallParityColumn {r : ℕ} (smallPrime : Fin r → ℕ) (n : ℕ) :
    Fin r → F₂ :=
  fun j ↦ parityVec n (smallPrime j)

/-- The augmented columns `((v_p(n))_{p in smallPrime}, 1)` from Proposition 3.2.-/
noncomputable def augmentedParityMap {m r : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ) :
    (Fin m → F₂) →ₗ[F₂] (Fin (r + 1) → F₂) :=
  augmentedColumnMap (fun i ↦ smallParityColumn smallPrime (f i))

/-- The nullity bound for the defect-code matrix used in Proposition 3.2.
@isnad1 id=le.0h4v.s10.2d0d567f27c6 from=translated src=- shape=21c5ce39 vocab=cba0971e
-/
theorem defectCode_finrank_ge {m r : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ) :
    m - (r + 1) ≤
      Module.finrank F₂ (LinearMap.ker (augmentedParityMap smallPrime f)) :=
  columns_sub_augmentedRows_le_finrank_ker _

/-- Every word in the defect-code kernel has even Hamming weight.
@isnad1 id=even.1h5v.s9.9c3ed07a08a4 from=translated src=- shape=5c9fa795 vocab=8e003627
-/
theorem defectCode_kernelWord_even {m r : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker (augmentedParityMap smallPrime f)) :
    Even (hammingNorm x) :=
  even_hammingNorm_of_mem_ker_augmentedColumnMap _ x hx

/--
Each listed small-prime coordinate of the parity sum selected by a kernel
word vanishes.
@isnad1 id=eq.1h6v.s9.87ba482dad40 from=translated src=- shape=f03022a3 vocab=33456ede
-/
theorem defectCode_kernel_coordinate {m r : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker (augmentedParityMap smallPrime f))
    (j : Fin r) :
    ∑ i : Fin m, x i * parityVec (f i) (smallPrime j) = 0 := by
  have hzero := congrFun (LinearMap.mem_ker.mp hx) j.castSucc
  simpa [augmentedParityMap, smallParityColumn,
    augmentedColumnMap_apply_castSucc] using hzero

/--
If every nonzero prime-parity coordinate of every selectable integer occurs
in `smallPrime`, then a defect-code kernel word selects a square product.

For the paper this coverage comes from writing an `H`-defective integer as
`s * a^2`, with squarefree `s` supported on primes `p ≤ H`.
@isnad1 id=ex.3h5v.s9.792339e61216 from=translated src=- shape=c7a6d6ef vocab=78ff1113
-/
theorem square_product_of_mem_ker_augmentedParityMap {m r : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (hf : ∀ i, f i ≠ 0)
    (hcover : ∀ i p, parityVec (f i) p ≠ 0 →
      ∃ j : Fin r, smallPrime j = p)
    (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker (augmentedParityMap smallPrime f)) :
    ∃ q : ℕ, ∏ i ∈ HammingBound.wordSupport x, f i = q ^ 2 := by
  classical
  apply (sum_parityVec_eq_zero_iff_prod_eq_sq
    (HammingBound.wordSupport x) f ?_).mp
  · ext p
    by_cases hp : ∃ j : Fin r, smallPrime j = p
    · obtain ⟨j, rfl⟩ := hp
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.zero_apply]
      rw [sum_wordSupport_eq_weighted_sum]
      exact defectCode_kernel_coordinate smallPrime f x hx j
    · have hzero : ∀ i : Fin m, parityVec (f i) p = 0 := by
        intro i
        apply Classical.byContradiction
        intro hne
        exact hp (hcover i p hne)
      simp [hzero]
  · intro i hi
    exact hf i

end DefectCodeRank
end PaperC
