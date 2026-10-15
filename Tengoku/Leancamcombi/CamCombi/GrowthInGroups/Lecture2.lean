module

public import Tengoku.Leancamcombi.CamCombi.Mathlib.Combinatorics.Additive.ApproximateSubgroup
public import Tengoku

public section

open Fin Finset List
open scoped Pointwise

namespace GrowthInGroups.Lecture2
variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : ℝ} {m : ℕ}

/--
@isnad1 id=le.0h4v.s7.7d1006287bf6 from=translated src=- shape=21cb955c vocab=44e78010
-/
lemma lemma_2_2 (U V W : Finset G) : #U * #(V⁻¹ * W) ≤ #(U * V) * #(U * W) :=
  ruzsa_triangle_inequality_invMul_mul_mul ..

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=le.1h3v.s7.0fe355b0e4d7 from=translated src=- shape=4b77cd63 vocab=6a626110
-/
lemma lemma_2_3_2 (hA : #(A ^ 2) ≤ K * #A) : #(A⁻¹ * A) ≤ K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A⁻¹ * A) : ℝ) ≤ #(A * A) * #(A * A) := by norm_cast; exact lemma_2_2 ..
    _ ≤ (K * #A) * (K * #A) := by rw [← sq A]; gcongr
    _ = #A * (K ^ 2 * #A) := by ring

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=le.1h3v.s7.04f8dd4ca6d6 from=translated src=- shape=04bb9936 vocab=6a626110
-/
lemma lemma_2_3_1 (hA : #(A ^ 2) ≤ K * #A) : #(A * A⁻¹) ≤ K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A * A⁻¹) : ℝ) ≤ #(A * A) * #(A * A) := by
      norm_cast; simpa [← mul_inv_rev] using lemma_2_2 A⁻¹ A⁻¹ A⁻¹
    _ ≤ (K * #A) * (K * #A) := by rw [← sq A]; gcongr
    _ = #A * (K ^ 2 * #A) := by ring

/--
@isnad1 id=le.3h5v.s7.2afc232ff296 from=translated src=- shape=8c6ec720 vocab=61713020
-/
lemma lemma_2_4_1 (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (ε : Fin m → ℤ) (hε : ∀ i, |ε i| = 1) :
    #((finRange m).map fun i ↦ A ^ ε i).prod ≤ K ^ (3 * (m - 2)) * #A :=
  small_alternating_pow_of_small_tripling hm hA ε hε

/--
@isnad1 id=le.3h4v.s7.8c973c190883 from=translated src=- shape=5229a881 vocab=bcd04e35
-/
lemma lemma_2_4_2 (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (hAsymm : A⁻¹ = A) :
    #(A ^ m) ≤ K ^ (m - 2) * #A := small_pow_of_small_tripling hm hA hAsymm

def def_2_5 (S : Set G) (K : ℝ) : Prop := IsApproximateSubgroup K S

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isapprox.0h1v.s5.8f7975b871e8 from=translated src=- shape=39f542d9 vocab=7f220926
-/
lemma remark_2_6_1 (k : ℕ) : IsApproximateAddSubgroup 2 (.Icc (-k) k : Set ℤ) where
  zero_mem := by simp
  neg_eq_self := by simp
  two_nsmul_covByVAdd :=
    ⟨{(-k : ℤ), (k : ℤ)}, mod_cast card_le_two, by simp [two_nsmul, Set.Icc_add_Icc, Set.pair_add]⟩

/--
@isnad1 id=isapprox.0h2v.s6.ecede04d62ba from=translated src=- shape=e72770ba vocab=b42ec0bb
-/
lemma remark_2_6_2 {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    IsApproximateAddSubgroup (2 ^ Fintype.card ι)
      (Set.univ.pi fun i ↦ .Icc (-k i) (k i) : Set (ι → ℤ)) := by
  simpa using IsApproximateAddSubgroup.pi fun i ↦ remark_2_6_1 (k i)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isapprox.0h0v.s4.d34f6a04bb44 from=translated src=- shape=ae5ba64e vocab=99e021fb
-/
lemma remark_2_6_3 : IsApproximateAddSubgroup 2 (.Icc (-1) 1 : Set ℝ) where
  zero_mem := by simp
  neg_eq_self := by simp
  two_nsmul_covByVAdd :=
    ⟨{-1, 1}, mod_cast card_le_two, by simp [two_nsmul, Set.Icc_add_Icc, Set.pair_add]⟩

/--
@isnad1 id=isapprox.3h3v.s7.7f5f395e2c5a from=translated src=- shape=4ffdfdbb vocab=31cd4064
-/
lemma lemma_2_7 {A : Finset G} (hA₁ : 1 ∈ A) (hsymm : A⁻¹ = A) (hA : #(A ^ 3) ≤ K * #A) :
    IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) := .of_small_tripling hA₁ hsymm hA

/--
@isnad1 id=ex.2h4v.s7.ead5c9a48efb from=translated src=- shape=8ba8b33e vocab=2ed89ecf
-/
lemma lemma_2_8 {A B : Finset G} (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * (B / B) := ruzsa_covering_mul hB hK

end GrowthInGroups.Lecture2
