import Tengoku.Seed.Algebra.Order.BigOperators.Expect
import Tengoku.Seed.Logic.Equiv.Prod
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary uniform probabilities on finite sample spaces

These lemmas keep the sampling estimates for exchanges finite and explicit.
-/

open scoped BigOperators

namespace EGZ.Expansion

noncomputable def finiteProb {A : Type*} [Fintype A] (P : A → Prop) : ℝ := by
  classical
  exact 𝔼 a, if P a then 1 else 0

/--
@isnad1 id=le.0h2v.s4.322c3855fa38 from=translated src=- shape=369b0e77 vocab=ac9bed5c
-/
theorem finiteProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ finiteProb P := by
  classical
  exact Finset.expect_nonneg (by intro a _; split_ifs <;> norm_num)

/--
@isnad1 id=le.0h4v.s5.78912317a089 from=translated src=- shape=a55bc3cd vocab=ac9bed5c
-/
theorem finiteProb_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : finiteProb P ≤ finiteProb Q := by
  classical
  apply Finset.expect_le_expect
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

/--
@isnad1 id=eq.0h1v.s4.22d828568fbd from=translated src=- shape=030f6fa5 vocab=3c54c02e
-/
@[simp] theorem finiteProb_true {A : Type*} [Fintype A] [Nonempty A] :
    finiteProb (fun _ : A ↦ True) = 1 := by
  simp [finiteProb]

/--
@isnad1 id=eq.0h1v.s4.88faff5085f5 from=translated src=- shape=26847842 vocab=8cb3f712
-/
@[simp] theorem finiteProb_false {A : Type*} [Fintype A] :
    finiteProb (fun _ : A ↦ False) = 0 := by
  simp [finiteProb]

/--
@isnad1 id=le.0h2v.s4.d296082d2248 from=translated src=- shape=f5bb8240 vocab=7e07687f
-/
theorem finiteProb_le_one {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    finiteProb P ≤ 1 := by
  simpa using finiteProb_mono (P := P) (Q := fun _ ↦ True) (by simp)

/--
@isnad1 id=eq.0h2v.s5.e2dbd5e2b85d from=translated src=- shape=205a2bc2 vocab=1a4c05c8
-/
theorem finiteProb_not {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    finiteProb (fun a ↦ ¬P a) = 1 - finiteProb P := by
  classical
  unfold finiteProb
  rw [← Fintype.expect_const (ι := A) (1 : ℝ), ← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro a _
  by_cases h : P a <;> simp [h]

/--
@isnad1 id=le.0h3v.s5.de4876a38a35 from=translated src=- shape=ab5cf03e vocab=cb34759f
-/
theorem finiteProb_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (P : I → A → Prop) :
    finiteProb (fun a ↦ ∃ i, P i a) ≤ ∑ i, finiteProb (P i) := by
  classical
  unfold finiteProb
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro a _
  by_cases h : ∃ i, P i a
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    exact (by simp [hi] : (1 : ℝ) ≤ if P i a then 1 else 0).trans
      (Finset.single_le_sum (f := fun j ↦ if P j a then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ i))
  · simp only [h, ↓reduceIte]
    positivity

/--
@isnad1 id=ex.1h3v.s5.e9cbba063c5d from=translated src=- shape=e619a14c vocab=1c9f6ba5
-/
theorem exists_forall_not_of_sum_finiteProb_lt_one {A I : Type*}
    [Fintype A] [Nonempty A] [Fintype I] (P : I → A → Prop)
    (h : (∑ i, finiteProb (P i)) < 1) : ∃ a, ∀ i, ¬P i a := by
  by_contra! hn
  have hp : finiteProb (fun a ↦ ∃ i, P i a) = 1 := by
    have heq : (fun a ↦ ∃ i, P i a) = (fun _ : A ↦ True) := by
      funext a
      exact propext ⟨fun _ ↦ trivial, fun _ ↦ hn a⟩
    rw [heq, finiteProb_true]
  have := finiteProb_exists_le P
  linarith

/--
@isnad1 id=eq.0h3v.s5.396dd8951bbf from=translated src=- shape=f6dfc273 vocab=62811917
-/
theorem finiteProb_prod {A B : Type*} [Fintype A] [Fintype B]
    (P : A × B → Prop) :
    finiteProb P = 𝔼 a, finiteProb (fun b ↦ P (a, b)) := by
  classical
  simpa only [finiteProb, Finset.univ_product_univ] using
    Finset.expect_product Finset.univ Finset.univ (fun x : A × B ↦ if P x then (1 : ℝ) else 0)

/--
@isnad1 id=eq.0h4v.s9.9c6787bbcee3 from=translated src=- shape=9e3bb424 vocab=4875aec4
-/
theorem expect_pi_split {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] (i : I) (f : (∀ i, A i) → ℝ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b : ∀ j : {j // j ≠ i}, A j,
      f ((Equiv.piSplitAt i A).symm (a, b)) := by
  rw [Fintype.expect_equiv (Equiv.piSplitAt i A) f
    (fun x ↦ f ((Equiv.piSplitAt i A).symm x))
    (by intro x; exact congrArg f ((Equiv.piSplitAt i A).symm_apply_apply x).symm)]
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product Finset.univ Finset.univ
      (fun x ↦ f ((Equiv.piSplitAt i A).symm x))

/--
@isnad1 id=eq.0h4v.s6.675fe63ce85d from=translated src=- shape=a29e7fd2 vocab=5fe5791b
-/
theorem expect_pi_eval {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (i : I) (f : A i → ℝ) : (𝔼 x : ∀ i, A i, f (x i)) = 𝔼 a, f a := by
  classical
  rw [expect_pi_split A i]
  simp [Equiv.piSplitAt]

/--
@isnad1 id=eq.0h4v.s6.f9b3852bba4a from=translated src=- shape=566a86fb vocab=51adb326
-/
theorem finiteProb_pi_eval {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (i : I) (P : A i → Prop) :
    finiteProb (fun x : ∀ i, A i ↦ P (x i)) = finiteProb P := by
  classical
  exact expect_pi_eval A i (fun a ↦ if P a then 1 else 0)

/--
@isnad1 id=eq.0h2v.s5.30d0c97cf221 from=translated src=- shape=c73cd982 vocab=20d8fd8d
-/
theorem finiteProb_eq_card {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] :
    finiteProb P = ((Finset.univ.filter P).card : ℝ) / Fintype.card A := by
  classical
  rw [finiteProb, Fintype.expect_eq_sum_div_card]
  congr 1
  have h : (∑ a : A, if P a then (1 : ℕ) else 0) = (Finset.univ.filter P).card :=
    Finset.sum_boole _ _
  exact_mod_cast h

/--
@isnad1 id=eq.0h2v.s5.67c6c481bae4 from=translated src=- shape=b3fabac1 vocab=7133f64a
-/
@[simp] theorem finiteProb_eq {A : Type*} [Fintype A] (a : A) :
    finiteProb (fun x ↦ x = a) = 1 / (Fintype.card A : ℝ) := by
  classical
  simp [finiteProb]

/-- The two samples at distinct coordinates of a finite product are
independent, including when the coordinate types differ.
@isnad1 id=eq.1h5v.s7.49ea1509d045 from=translated src=- shape=7c97cd84 vocab=5fe5791b
-/
theorem expect_pi_pair {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    {i j : I} (hij : j ≠ i) (f : A i → A j → ℝ) :
    (𝔼 x : ∀ k, A k, f (x i) (x j)) = 𝔼 a, 𝔼 b, f a b := by
  rw [expect_pi_split A i]
  apply Finset.expect_congr rfl
  intro a _
  simpa only [Equiv.piSplitAt_symm_apply, ↓reduceDIte, dite_eq_right hij] using
    expect_pi_eval (fun k : {k // k ≠ i} ↦ A k) ⟨j, hij⟩ (f a)

/--
@isnad1 id=eq.1h5v.s6.57c21fc4302a from=translated src=- shape=9a16f7ba vocab=e103214e
-/
theorem finiteProb_pi_pair {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    {i j : I} (hij : j ≠ i) (P : A i → A j → Prop) :
    finiteProb (fun x : ∀ k, A k ↦ P (x i) (x j)) =
      𝔼 a, finiteProb (P a) := by
  classical
  exact expect_pi_pair A hij (fun a b ↦ if P a b then 1 else 0)

/-- A collision after injectively encoding the two coordinate types has
probability at most the reciprocal size of the second coordinate type.
@isnad1 id=le.2h6v.s6.2b8382840053 from=translated src=- shape=236a23ae vocab=6cf3df11
-/
theorem finiteProb_pi_collision_le {I B : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (v : ∀ i, A i → B) (hv : ∀ i, Function.Injective (v i))
    {i j : I} (hij : j ≠ i) :
    finiteProb (fun x : ∀ k, A k ↦ v i (x i) = v j (x j)) ≤
      1 / (Fintype.card (A j) : ℝ) := by
  rw [finiteProb_pi_pair A hij (fun a b ↦ v i a = v j b)]
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  by_cases he : ∃ b, v i a = v j b
  · obtain ⟨b, hb⟩ := he
    have hp : (fun x ↦ v i a = v j x) = (fun x ↦ x = b) := by
      funext x
      exact propext (by rw [hb, (hv j).eq_iff, eq_comm])
    rw [hp, finiteProb_eq]
  · have hp : (fun x ↦ v i a = v j x) = (fun _ : A j ↦ False) := by
      funext x
      exact propext ⟨fun h ↦ he ⟨x, h⟩, False.elim⟩
    rw [hp, finiteProb_false]
    positivity

/-- A union bound controls all repeated positions in an independent
sample. The deliberately loose square bound avoids ordering the indices.
@isnad1 id=le.3h5v.s7.6d363cf787f9 from=translated src=- shape=dbbc54d7 vocab=8ff647c2
-/
theorem finiteProb_not_injective_le {I B : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (v : ∀ i, A i → B) (hv : ∀ i, Function.Injective (v i))
    {M : ℝ} (hM : 0 < M) (hsize : ∀ i, M ≤ Fintype.card (A i)) :
    finiteProb (fun x : ∀ i, A i ↦ ¬Function.Injective (fun i ↦ v i (x i))) ≤
      (Fintype.card I : ℝ) ^ 2 / M := by
  classical
  let bad : I × I → (∀ i, A i) → Prop := fun ij x ↦
    ij.1 ≠ ij.2 ∧ v ij.1 (x ij.1) = v ij.2 (x ij.2)
  have hpoint (ij : I × I) : finiteProb (bad ij) ≤ 1 / M := by
    by_cases h : ij.1 = ij.2
    · have heq : bad ij = fun _ ↦ False := by
        funext x
        simp [bad, h]
      rw [heq, finiteProb_false]
      positivity
    · calc
        finiteProb (bad ij) ≤ finiteProb (fun x ↦ v ij.1 (x ij.1) = v ij.2 (x ij.2)) :=
          finiteProb_mono (fun _ hx ↦ hx.2)
        _ ≤ 1 / (Fintype.card (A ij.2) : ℝ) :=
          finiteProb_pi_collision_le A v hv (Ne.symm h)
        _ ≤ 1 / M := one_div_le_one_div_of_le hM (hsize ij.2)
  calc
    finiteProb (fun x : ∀ i, A i ↦ ¬Function.Injective (fun i ↦ v i (x i))) ≤
        finiteProb (fun x ↦ ∃ ij, bad ij x) := by
      apply finiteProb_mono
      intro x hx
      by_contra! hn
      apply hx
      intro i j hij
      by_contra hne
      exact hn (i, j) ⟨hne, hij⟩
    _ ≤ ∑ ij, finiteProb (bad ij) := finiteProb_exists_le bad
    _ ≤ ∑ _ij : I × I, 1 / M := Finset.sum_le_sum (fun ij _ ↦ hpoint ij)
    _ = (Fintype.card I : ℝ) ^ 2 / M := by
      simp [Fintype.card_prod, Nat.cast_mul, pow_two, div_eq_mul_inv]

end EGZ.Expansion
