/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Tengoku
/-!
# Common zeros on products of projective planes

Scratch development, independent of `Submission/Spec.lean`.
The multihomogeneity convention is coefficientwise, so the zero polynomial
is homogeneous of every multidegree.  No projective intersection theorem is
assumed as an axiom.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MvPolynomial

namespace KoetheMultiProjective

variable {k : Type*} {N : ℕ}

/-- The polynomial variables, grouped into triples. -/
abbrev Vars (N : ℕ) := Fin N × Fin 3

/-- The degree of an exponent vector in one block. -/
def blockDegree (d : Vars N →₀ ℕ) (b : Fin N) : ℕ :=
  ∑ j : Fin 3, d (b, j)

/--
@isnad1 id=eq.0h2v.s5.67cabb39b7cc from=translated src=- shape=79bf5912 vocab=87ee6592
-/
@[simp] theorem blockDegree_zero (b : Fin N) : blockDegree 0 b = 0 := by
  simp [blockDegree]

/--
@isnad1 id=eq.0h4v.s6.95d0f8fb6571 from=translated src=- shape=b208ed52 vocab=bbc4e8d1
-/
@[simp] theorem blockDegree_add (d e : Vars N →₀ ℕ) (b : Fin N) :
    blockDegree (d + e) b = blockDegree d b + blockDegree e b := by
  simp [blockDegree, Finset.sum_add_distrib]

/-- All block degrees of an exponent vector are equal. -/
def Balanced (d : Vars N →₀ ℕ) : Prop :=
  ∀ b c : Fin N, blockDegree d b = blockDegree d c

instance (d : Vars N →₀ ℕ) : Decidable (Balanced d) :=
  inferInstanceAs (Decidable (∀ b c : Fin N, blockDegree d b = blockDegree d c))

/--
@isnad1 id=balanced.0h1v.s4.1917c15f7ed3 from=translated src=- shape=7e4dfd91 vocab=ab232035
-/
@[simp] theorem balanced_zero : Balanced (0 : Vars N →₀ ℕ) := by
  intro b c
  simp

/--
@isnad1 id=balanced.2h3v.s6.f6ede0fd71a2 from=translated src=- shape=1398a052 vocab=7a632994
-/
theorem Balanced.add {d e : Vars N →₀ ℕ} (hd : Balanced d) (he : Balanced e) :
    Balanced (d + e) := by
  intro b c
  simp only [blockDegree_add, hd b c, he b c]

/--
@isnad1 id=iff.1h3v.s6.50ce3d797ca9 from=translated src=- shape=c689bae3 vocab=7a632994
-/
theorem Balanced.add_iff_right {d e : Vars N →₀ ℕ} (hd : Balanced d) :
    Balanced (d + e) ↔ Balanced e := by
  constructor
  · intro h b c
    have := h b c
    simpa only [blockDegree_add, hd b c, Nat.add_left_cancel_iff] using this
  · exact hd.add

/-- Coefficientwise multihomogeneity with a specified degree in each block. -/
def IsMultiHomogeneous [CommSemiring k] (f : MvPolynomial (Vars N) k)
    (r : Fin N → ℕ) : Prop :=
  ∀ d, f.coeff d ≠ 0 → ∀ b, blockDegree d b = r b

/-- Every nonzero monomial has the same degree `r` in every block. -/
def IsMultiHomogeneousOfDegree [CommSemiring k] (f : MvPolynomial (Vars N) k)
    (r : ℕ) : Prop :=
  IsMultiHomogeneous f (fun _ => r)

/-- Polynomials all of whose monomials have balanced block degrees.
Different monomials may have different common degrees. -/
def HasBalancedSupport [CommSemiring k] (f : MvPolynomial (Vars N) k) : Prop :=
  ∀ d, f.coeff d ≠ 0 → Balanced d

/--
@isnad1 id=hasbalan.1h4v.s4.2d62e0034ef7 from=translated src=- shape=ebd66cb6 vocab=bf3b5185
-/
theorem IsMultiHomogeneousOfDegree.hasBalancedSupport [CommSemiring k]
    {f : MvPolynomial (Vars N) k} {r : ℕ} (hf : IsMultiHomogeneousOfDegree f r) :
    HasBalancedSupport f := by
  intro d hd b c
  exact (hf d hd b).trans (hf d hd c).symm

section MultihomogeneityAPI

variable [CommSemiring k]

/--
@isnad1 id=ismultih.0h3v.s5.05572a62e9f3 from=translated src=- shape=0f68b2b8 vocab=639b4e9b
-/
@[simp] theorem isMultiHomogeneous_zero (r : Fin N → ℕ) :
    IsMultiHomogeneous (0 : MvPolynomial (Vars N) k) r := by
  intro d hd
  simp at hd

/--
@isnad1 id=ismultih.0h3v.s5.96e275d20be0 from=translated src=- shape=a76f68dd vocab=160b030b
-/
@[simp] theorem isMultiHomogeneousOfDegree_zero (r : ℕ) :
    IsMultiHomogeneousOfDegree (0 : MvPolynomial (Vars N) k) r :=
  isMultiHomogeneous_zero _

/--
@isnad1 id=ismultih.1h5v.s7.835f914a566a from=translated src=- shape=cd407d51 vocab=330a5e10
-/
theorem isMultiHomogeneous_monomial {d : Vars N →₀ ℕ} {r : Fin N → ℕ}
    (hd : ∀ b, blockDegree d b = r b) (a : k) :
    IsMultiHomogeneous (monomial d a) r := by
  classical
  intro e he
  by_cases h : d = e
  · subst e
    exact hd
  · simp [coeff_monomial, h] at he

/--
@isnad1 id=ismultih.2h5v.s6.4121a7b91301 from=translated src=- shape=ddd39c35 vocab=e86f0c12
-/
theorem IsMultiHomogeneous.add {p q : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (hq : IsMultiHomogeneous q r) :
    IsMultiHomogeneous (p + q) r := by
  intro d hd
  by_cases h : p.coeff d = 0
  · apply hq d
    simpa [h] using hd
  · exact hp d h

/--
@isnad1 id=ismultih.1h5v.s6.b29eaa11beb3 from=translated src=- shape=a6e5ab60 vocab=fead97c1
-/
theorem IsMultiHomogeneous.smul {p : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (a : k) : IsMultiHomogeneous (a • p) r := by
  intro d hd
  apply hp d
  exact right_ne_zero_of_mul (by simpa only [coeff_smul, smul_eq_mul] using hd)

/--
@isnad1 id=ismultih.2h6v.s6.21ae58eb723a from=translated src=- shape=cdc64006 vocab=f5518636
-/
theorem IsMultiHomogeneous.mul {p q : MvPolynomial (Vars N) k} {r s : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (hq : IsMultiHomogeneous q s) :
    IsMultiHomogeneous (p * q) (r + s) := by
  classical
  intro d hd b
  rw [coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hef, blockDegree_add,
    hp e (left_ne_zero_of_mul h) b, hq f (right_ne_zero_of_mul h) b]
  rfl

/--
@isnad1 id=ismultih.1h5v.s6.58d2f115323c from=translated src=- shape=03065400 vocab=761a79b4
-/
theorem IsMultiHomogeneous.pow {p : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (n : ℕ) :
    IsMultiHomogeneous (p ^ n) (fun b => n * r b) := by
  induction n with
  | zero =>
    have h := isMultiHomogeneous_monomial (fun b : Fin N => blockDegree_zero b) (1 : k)
    rw [monomial_zero', C_1] at h
    simpa only [pow_zero, Nat.zero_mul] using h
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hp using 1
    funext b
    simp [Nat.add_mul]

/--
@isnad1 id=ismultih.2h5v.s6.9776b0d05fc6 from=translated src=- shape=4b59f68f vocab=3ac32afc
-/
theorem IsMultiHomogeneousOfDegree.add {p q : MvPolynomial (Vars N) k} {r : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (hq : IsMultiHomogeneousOfDegree q r) :
    IsMultiHomogeneousOfDegree (p + q) r := IsMultiHomogeneous.add hp hq

/--
@isnad1 id=ismultih.2h6v.s6.6360f7c5e5ba from=translated src=- shape=b9e13703 vocab=e0b08dc7
-/
theorem IsMultiHomogeneousOfDegree.mul {p q : MvPolynomial (Vars N) k} {r s : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (hq : IsMultiHomogeneousOfDegree q s) :
    IsMultiHomogeneousOfDegree (p * q) (r + s) := IsMultiHomogeneous.mul hp hq

/--
@isnad1 id=ismultih.1h5v.s6.86a18e478601 from=translated src=- shape=fac30ee0 vocab=8622c492
-/
theorem IsMultiHomogeneousOfDegree.pow {p : MvPolynomial (Vars N) k} {r : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (n : ℕ) :
    IsMultiHomogeneousOfDegree (p ^ n) (n * r) := IsMultiHomogeneous.pow hp n

end MultihomogeneityAPI

section BalancedAlgebra

variable [CommSemiring k]

/--
@isnad1 id=hasbalan.1h4v.s7.038aacd5483e from=translated src=- shape=d55582b8 vocab=fcc2e7ce
-/
theorem hasBalancedSupport_monomial {d : Vars N →₀ ℕ} (hd : Balanced d) (a : k) :
    HasBalancedSupport (monomial d a) := by
  classical
  intro e he
  by_cases h : d = e
  · simpa [← h] using hd
  · simp [coeff_monomial, h] at he

/--
@isnad1 id=hasbalan.2h4v.s6.d98a34de2c53 from=translated src=- shape=aec89646 vocab=888c60b1
-/
theorem hasBalancedSupport_add {p q : MvPolynomial (Vars N) k}
    (hp : HasBalancedSupport p) (hq : HasBalancedSupport q) :
    HasBalancedSupport (p + q) := by
  intro d hd
  by_cases h : p.coeff d = 0
  · apply hq d
    simpa [h] using hd
  · exact hp d h

/--
@isnad1 id=hasbalan.2h4v.s6.9e228773c509 from=translated src=- shape=aec89646 vocab=ef2ca745
-/
theorem hasBalancedSupport_mul {p q : MvPolynomial (Vars N) k}
    (hp : HasBalancedSupport p) (hq : HasBalancedSupport q) :
    HasBalancedSupport (p * q) := by
  classical
  intro d hd
  rw [coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have he : p.coeff e ≠ 0 := left_ne_zero_of_mul h
  have hf : q.coeff f ≠ 0 := right_ne_zero_of_mul h
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hef]
  exact (hp e he).add (hq f hf)

/-- The diagonal (balanced-degree) monomial subalgebra. -/
def balancedAlgebra (k : Type*) [CommSemiring k] (N : ℕ) :
    Subalgebra k (MvPolynomial (Vars N) k) where
  carrier := {p | HasBalancedSupport p}
  zero_mem' := by intro d hd; simp at hd
  one_mem' := hasBalancedSupport_monomial balanced_zero 1
  add_mem' := hasBalancedSupport_add
  mul_mem' := hasBalancedSupport_mul
  algebraMap_mem' a := hasBalancedSupport_monomial balanced_zero a

/--
@isnad1 id=iff.0h3v.s7.7372cd7e586c from=translated src=- shape=cecc550b vocab=d9e82399
-/
@[simp] theorem mem_balancedAlgebra {p : MvPolynomial (Vars N) k} :
    p ∈ balancedAlgebra k N ↔ HasBalancedSupport p := Iff.rfl

/-- Exponent vector of a degree-one Segre coordinate. -/
def segreExponent (j : Fin N → Fin 3) : Vars N →₀ ℕ :=
  ∑ b : Fin N, Finsupp.single (b, j b) 1

/--
@isnad1 id=eq.0h4v.s6.fb9e72667cf1 from=translated src=- shape=dad7cf6d vocab=0419c18b
-/
@[simp] theorem segreExponent_apply (j : Fin N → Fin 3) (b : Fin N) (c : Fin 3) :
    segreExponent j (b, c) = if j b = c then 1 else 0 := by
  classical
  simp only [segreExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single b]
  · simp [Finsupp.single_apply, Prod.mk.injEq]
  · intro a _ ha
    simp [Prod.mk.injEq, ha]
  · simp

/--
@isnad1 id=eq.0h3v.s4.bc7097415c1b from=translated src=- shape=61dac71e vocab=2e14dd20
-/
@[simp] theorem blockDegree_segreExponent (j : Fin N → Fin 3) (b : Fin N) :
    blockDegree (segreExponent j) b = 1 := by
  classical
  simp [blockDegree]

/--
@isnad1 id=balanced.0h2v.s4.4b13a6cef9bf from=translated src=- shape=6b37c451 vocab=55d280f8
-/
theorem balanced_segreExponent (j : Fin N → Fin 3) : Balanced (segreExponent j) := by
  intro b c
  simp

/-- A degree-one Segre coordinate, as a polynomial in the original triples. -/
def segreMonomial (j : Fin N → Fin 3) : MvPolynomial (Vars N) k :=
  ∏ b : Fin N, X (b, j b)

/--
@isnad1 id=eq.0h3v.s7.a822b8766b32 from=translated src=- shape=001057c3 vocab=1b433012
-/
theorem segreMonomial_eq_monomial (j : Fin N → Fin 3) :
    segreMonomial (k := k) j = monomial (segreExponent j) 1 := by
  classical
  simp [segreMonomial, segreExponent, monomial_sum_one, X]

/--
@isnad1 id=ismultih.0h3v.s4.76d7ea535b56 from=translated src=- shape=2ac016e2 vocab=af503fa5
-/
theorem isMultiHomogeneousOfDegree_segreMonomial (j : Fin N → Fin 3) :
    IsMultiHomogeneousOfDegree (segreMonomial (k := k) j) 1 := by
  rw [segreMonomial_eq_monomial]
  exact isMultiHomogeneous_monomial (blockDegree_segreExponent j) 1

/--
@isnad1 id=mem.0h3v.s7.6fdd7fe87ba6 from=translated src=- shape=1691eb8a vocab=84b0e7c2
-/
theorem segreMonomial_mem (j : Fin N → Fin 3) :
    segreMonomial (k := k) j ∈ balancedAlgebra k N := by
  rw [segreMonomial_eq_monomial]
  exact hasBalancedSupport_monomial (balanced_segreExponent j) 1

/--
@isnad1 id=eq.1h2v.s5.1b363432fc11 from=translated src=- shape=08cd4243 vocab=87ee6592
-/
theorem exponent_eq_zero_of_blockDegree_zero {d : Vars N →₀ ℕ}
    (hd : ∀ b, blockDegree d b = 0) : d = 0 := by
  classical
  ext ⟨b, j⟩
  have h : d (b, j) ≤ blockDegree d b :=
    Finset.single_le_sum (f := fun j : Fin 3 => d (b, j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa [hd b] using h

/--
@isnad1 id=ex.1h3v.s6.ad4f092298a7 from=translated src=- shape=28949d1b vocab=f7935bc4
-/
theorem exists_segreExponent_le {d : Vars N →₀ ℕ} {r : ℕ}
    (hd : ∀ b, blockDegree d b = r + 1) :
    ∃ j : Fin N → Fin 3, segreExponent j ≤ d := by
  classical
  have hpos : ∀ b, ∃ j : Fin 3, 0 < d (b, j) := by
    intro b
    by_contra! h
    have hzero : blockDegree d b = 0 := by
      simp [blockDegree, Nat.eq_zero_of_le_zero (h _)]
    have := hd b
    omega
  choose j hj using hpos
  refine ⟨j, ?_⟩
  intro ⟨b, c⟩
  simp only [segreExponent_apply]
  split_ifs with h
  · subst c
    exact hj b
  · exact Nat.zero_le _

/-- A balanced monomial factors into degree-one Segre monomials.
This is the finite-generation step, proved by induction on the common degree.
@isnad1 id=mem.1h5v.s8.c145ba6865c3 from=translated src=- shape=55d5d41f vocab=cabca4b7
-/
theorem monomial_mem_adjoin_segre {d : Vars N →₀ ℕ} {r : ℕ}
    (hd : ∀ b, blockDegree d b = r) (a : k) :
    monomial d a ∈ Algebra.adjoin k (Set.range (segreMonomial (k := k) (N := N))) := by
  classical
  induction r generalizing d with
  | zero =>
    have : d = 0 := exponent_eq_zero_of_blockDegree_zero hd
    subst d
    exact Subalgebra.algebraMap_mem _ a
  | succ r ih =>
    obtain ⟨j, hj⟩ := exists_segreExponent_le hd
    have hde : segreExponent j + (d - segreExponent j) = d := add_tsub_cancel_of_le hj
    have hrem : ∀ b, blockDegree (d - segreExponent j) b = r := by
      intro b
      have h := congrArg (fun e => blockDegree e b) hde
      simp only [blockDegree_add, blockDegree_segreExponent, hd b] at h
      omega
    have hm : monomial d a = segreMonomial j * monomial (d - segreExponent j) a := by
      rw [segreMonomial_eq_monomial, monomial_mul_monomial, one_mul, hde]
    rw [hm]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨j, rfl⟩) (ih hrem)

/-- The balanced subalgebra is generated by the finitely many Segre coordinates.
@isnad1 id=eq.0h2v.s7.01b8c22ca2ea from=translated src=- shape=adf330bc vocab=4568e8b5
-/
theorem adjoin_segre_eq_balancedAlgebra [NeZero N] :
    Algebra.adjoin k (Set.range (segreMonomial (k := k) (N := N))) = balancedAlgebra k N := by
  classical
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact segreMonomial_mem j
  · intro p hp
    rw [p.as_sum]
    apply Subalgebra.sum_mem
    intro d hd
    apply monomial_mem_adjoin_segre (r := blockDegree d 0)
    intro b
    exact hp d (mem_support_iff.mp hd) b 0

end BalancedAlgebra

section Retraction

variable [CommSemiring k]

/-- Keep just the monomials whose block degrees are all equal. -/
def balancedPart : MvPolynomial (Vars N) k →ₗ[k] MvPolynomial (Vars N) k where
  toFun p := (AddMonoidAlgebra.coeffLinearEquiv k).symm
    (Finsupp.filter Balanced (AddMonoidAlgebra.coeffLinearEquiv k p))
  map_add' _ _ := by simp [Finsupp.filter_add]
  map_smul' _ _ := by simp [Finsupp.filter_smul]

/--
@isnad1 id=eq.0h4v.s8.a4a006934dad from=translated src=- shape=39139b80 vocab=aa2fc65d
-/
@[simp] theorem coeff_balancedPart (p : MvPolynomial (Vars N) k) (d : Vars N →₀ ℕ) :
    (balancedPart p).coeff d = if Balanced d then p.coeff d else 0 := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=mem.0h3v.s8.95d452520719 from=translated src=- shape=86b2a1ed vocab=b9e707ec
-/
theorem balancedPart_mem (p : MvPolynomial (Vars N) k) :
    balancedPart p ∈ balancedAlgebra k N := by
  classical
  intro d hd
  by_contra h
  simp [h] at hd

/--
@isnad1 id=eq.1h3v.s8.686f736d576b from=translated src=- shape=f5cb54c3 vocab=b9e707ec
-/
@[simp] theorem balancedPart_of_mem {p : MvPolynomial (Vars N) k}
    (hp : p ∈ balancedAlgebra k N) : balancedPart p = p := by
  classical
  ext d
  rw [coeff_balancedPart]
  by_cases h : Balanced d
  · simp [h]
  · have hc : p.coeff d = 0 := by
      by_contra hc
      exact h (hp d hc)
    simp [h, hc]

/--
@isnad1 id=eq.0h4v.s9.421cc2312327 from=translated src=- shape=0e2d88b1 vocab=278c1ff3
-/
@[simp] theorem balancedPart_monomial (d : Vars N →₀ ℕ) (a : k) :
    balancedPart (monomial d a) = if Balanced d then monomial d a else 0 := by
  classical
  ext e
  rw [coeff_balancedPart]
  rcases eq_or_ne d e with rfl | hde
  · split_ifs <;> simp [coeff_monomial]
  · simp [coeff_monomial, hde,
      apply_ite (fun p : MvPolynomial (Vars N) k => p.coeff e)]

/--
@isnad1 id=eq.1h5v.s9.c9613cb4fa69 from=translated src=- shape=fd8c44f3 vocab=385c29df
-/
theorem balancedPart_monomial_mul {d : Vars N →₀ ℕ} (hd : Balanced d)
    (a : k) (q : MvPolynomial (Vars N) k) :
    balancedPart (monomial d a * q) = monomial d a * balancedPart q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial e b =>
    rw [monomial_mul_monomial, balancedPart_monomial, balancedPart_monomial]
    simp only [hd.add_iff_right]
    split_ifs <;> simp [monomial_mul_monomial]
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]

/-- The balanced-monomial projection is linear over the whole balanced subalgebra,
not merely over the coefficient field.
@isnad1 id=eq.1h4v.s9.cd0306f5ce76 from=translated src=- shape=25248064 vocab=f45ec59b
-/
theorem balancedPart_mul {p : MvPolynomial (Vars N) k}
    (hp : p ∈ balancedAlgebra k N) (q : MvPolynomial (Vars N) k) :
    balancedPart (p * q) = p * balancedPart q := by
  classical
  calc
    balancedPart (p * q) =
        balancedPart ((∑ d ∈ p.support, monomial d (p.coeff d)) * q) := by
      congr 2
      exact p.as_sum
    _ = ∑ d ∈ p.support, balancedPart (monomial d (p.coeff d) * q) := by
      simp only [Finset.sum_mul, map_sum]
    _ = ∑ d ∈ p.support, monomial d (p.coeff d) * balancedPart q := by
      apply Finset.sum_congr rfl
      intro d hd
      exact balancedPart_monomial_mul (hp d (mem_support_iff.mp hd)) _ _
    _ = p * balancedPart q := by rw [← Finset.sum_mul, ← p.as_sum]

/-- The same projection with codomain restricted to the balanced algebra. -/
def balancedRetract : MvPolynomial (Vars N) k →ₗ[k] balancedAlgebra k N :=
  balancedPart.codRestrict (balancedAlgebra k N).toSubmodule balancedPart_mem

/--
@isnad1 id=eq.0h3v.s10.970651188425 from=translated src=- shape=9d634f14 vocab=0f2fe857
-/
@[simp] theorem coe_balancedRetract (p : MvPolynomial (Vars N) k) :
    (balancedRetract p : MvPolynomial (Vars N) k) = balancedPart p := rfl

/--
@isnad1 id=eq.0h3v.s10.a7f12b16f688 from=translated src=- shape=060059c9 vocab=f7f058b7
-/
@[simp] theorem balancedRetract_coe (p : balancedAlgebra k N) :
    balancedRetract (p : MvPolynomial (Vars N) k) = p := by
  apply Subtype.ext
  exact balancedPart_of_mem p.property

/--
@isnad1 id=eq.0h4v.s11.76b804393947 from=translated src=- shape=248d1fc5 vocab=d271fa6a
-/
@[simp] theorem balancedRetract_mul (p : balancedAlgebra k N)
    (q : MvPolynomial (Vars N) k) :
    balancedRetract ((p : MvPolynomial (Vars N) k) * q) = p * balancedRetract q := by
  apply Subtype.ext
  exact balancedPart_mul p.property q

/-- Extending an ideal generated by balanced polynomials to the ambient polynomial
ring and contracting it back introduces no new balanced elements.
@isnad1 id=iff.0h5v.s11.9ad45780fc12 from=translated src=- shape=f9da1ee8 vocab=c0a1bf61
-/
theorem mem_span_range_coe_iff {ι : Type*} [Finite ι]
    (f : ι → balancedAlgebra k N) (p : balancedAlgebra k N) :
    (p : MvPolynomial (Vars N) k) ∈
        Ideal.span (Set.range (fun i => (f i : MvPolynomial (Vars N) k))) ↔
      p ∈ Ideal.span (Set.range f) := by
  classical
  cases nonempty_fintype ι
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
    have h := congrArg balancedRetract ha
    have hsum : (∑ i, balancedRetract (a i) * f i) = p := by
      simpa only [smul_eq_mul, map_sum, mul_comm, balancedRetract_mul,
        balancedRetract_coe] using h
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := i))
  · intro hp
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
    have h := congrArg (balancedAlgebra k N).val ha
    simp only [smul_eq_mul, map_sum, map_mul] at h
    change ∑ i, (a i : MvPolynomial (Vars N) k) * (f i : MvPolynomial (Vars N) k) =
      (p : MvPolynomial (Vars N) k) at h
    rw [← h]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := i))

/--
@isnad1 id=iff.0h5v.s11.e50078110931 from=translated src=- shape=1cec7045 vocab=b63b90d6
-/
theorem mem_radical_span_range_coe_iff {ι : Type*} [Finite ι]
    (f : ι → balancedAlgebra k N) (p : balancedAlgebra k N) :
    (p : MvPolynomial (Vars N) k) ∈
        (Ideal.span (Set.range (fun i => (f i : MvPolynomial (Vars N) k)))).radical ↔
      p ∈ (Ideal.span (Set.range f)).radical := by
  simp only [Ideal.mem_radical_iff, ← Subalgebra.coe_pow, mem_span_range_coe_iff]

end Retraction

section Height

variable [Field k]

/-- A Segre coordinate as an element of the balanced subalgebra. -/
def segre (j : Fin N → Fin 3) : balancedAlgebra k N :=
  ⟨segreMonomial j, segreMonomial_mem j⟩

/--
@isnad1 id=eq.0h3v.s8.f3b65971382c from=translated src=- shape=da3dd80a vocab=dfcd081b
-/
@[simp] theorem coe_segre (j : Fin N → Fin 3) :
    (segre (k := k) j : MvPolynomial (Vars N) k) = segreMonomial j := rfl

/--
@isnad1 id=ne.0h3v.s6.973f56a8c281 from=translated src=- shape=26eb6bb4 vocab=8903c4d8
-/
theorem segreMonomial_ne_zero (j : Fin N → Fin 3) :
    segreMonomial (k := k) j ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => X_ne_zero _)

/--
@isnad1 id=eq.0h3v.s7.f6d304ab523c from=translated src=- shape=974be473 vocab=35995305
-/
@[simp] theorem constantCoeff_segreMonomial [NeZero N] (j : Fin N → Fin 3) :
    constantCoeff (segreMonomial (k := k) j) = 0 := by
  classical
  simp [segreMonomial, NeZero.ne N]

/-- Set a specified finite set of ambient variables to zero. -/
def killVars (s : Finset (Vars N)) :
    MvPolynomial (Vars N) k →ₐ[k] MvPolynomial (Vars N) k := by
  classical
  exact aeval (fun v => if v ∈ s then 0 else X v)

/--
@isnad1 id=eq.0h4v.s8.7e0cfdbd6cac from=translated src=- shape=07f83a1b vocab=fbab71ac
-/
@[simp] theorem killVars_X (s : Finset (Vars N)) (v : Vars N) :
    killVars (k := k) s (X v) = if v ∈ s then 0 else X v := by
  classical
  simp [killVars]

/--
@isnad1 id=eq.1h4v.s8.293f02867606 from=translated src=- shape=f00574dc vocab=e09e2603
-/
theorem killVars_comp_of_subset {s t : Finset (Vars N)} (hst : s ⊆ t) :
    (killVars (k := k) t).comp (killVars s) = killVars t := by
  classical
  ext v
  by_cases h : v ∈ s
  · simp [h, hst h]
  · simp [h]

/--
@isnad1 id=eq.0h3v.s8.90ecacb2f52c from=translated src=- shape=1b0f70f6 vocab=02695f0a
-/
theorem zero_aeval_comp_killVars (s : Finset (Vars N)) :
    (aeval (R := k) (fun _ : Vars N => (0 : k))).comp (killVars (k := k) s) =
      aeval (R := k) (fun _ : Vars N => (0 : k)) := by
  classical
  ext v
  by_cases h : v ∈ s <;> simp [h]

/-- Contract a prime variable ideal to the balanced subalgebra. -/
def killedIdeal (s : Finset (Vars N)) : Ideal (balancedAlgebra k N) :=
  RingHom.ker (((killVars s).comp (balancedAlgebra k N).val).toRingHom)

/--
@isnad1 id=iff.0h4v.s11.763216ca81b8 from=translated src=- shape=d2000ae8 vocab=3131dfc4
-/
@[simp] theorem mem_killedIdeal (s : Finset (Vars N)) (p : balancedAlgebra k N) :
    p ∈ killedIdeal s ↔ killVars s (p : MvPolynomial (Vars N) k) = 0 := Iff.rfl

/--
@isnad1 id=isprime.0h3v.s8.3bf7cbe669a9 from=translated src=- shape=fd9cb521 vocab=d7631c9d
-/
instance killedIdeal_isPrime (s : Finset (Vars N)) :
    (killedIdeal (k := k) s).IsPrime := RingHom.ker_isPrime _

/-- The vertex of the affine Segre cone: the augmentation ideal. -/
def vertexIdeal (k : Type*) [Field k] (N : ℕ) : Ideal (balancedAlgebra k N) :=
  RingHom.ker (((aeval (fun _ : Vars N => (0 : k))).comp
    (balancedAlgebra k N).val).toRingHom)

/--
@isnad1 id=iff.0h3v.s11.166b62f78791 from=translated src=- shape=2bdf6707 vocab=78f55fbb
-/
@[simp] theorem mem_vertexIdeal (p : balancedAlgebra k N) :
    p ∈ vertexIdeal k N ↔ constantCoeff (p : MvPolynomial (Vars N) k) = 0 := by
  change aeval (fun _ : Vars N => (0 : k)) (p : MvPolynomial (Vars N) k) = 0 ↔ _
  simp

/--
@isnad1 id=isprime.0h2v.s8.0ed267439ad7 from=translated src=- shape=7bc7565c vocab=728ce897
-/
instance vertexIdeal_isPrime : (vertexIdeal k N).IsPrime := RingHom.ker_isPrime _

/--
@isnad1 id=le.1h4v.s11.e957087ce8b3 from=translated src=- shape=4a3557f3 vocab=4f4f2777
-/
theorem killedIdeal_mono {s t : Finset (Vars N)} (hst : s ⊆ t) :
    killedIdeal (k := k) s ≤ killedIdeal t := by
  intro p hp
  rw [mem_killedIdeal] at hp ⊢
  have h := congrArg (fun φ : MvPolynomial (Vars N) k →ₐ[k] MvPolynomial (Vars N) k =>
    φ (p : MvPolynomial (Vars N) k)) (killVars_comp_of_subset hst)
  simpa [hp] using h.symm

/--
@isnad1 id=le.0h3v.s11.06051c25b874 from=translated src=- shape=f04b659b vocab=c4e3f5cd
-/
theorem killedIdeal_le_vertexIdeal (s : Finset (Vars N)) :
    killedIdeal (k := k) s ≤ vertexIdeal k N := by
  intro p hp
  rw [mem_killedIdeal] at hp
  rw [mem_vertexIdeal]
  have h := congrArg (fun φ : MvPolynomial (Vars N) k →ₐ[k] k =>
    φ (p : MvPolynomial (Vars N) k)) (zero_aeval_comp_killVars s)
  simpa [hp] using h.symm

/--
@isnad1 id=eq.1h4v.s8.3123d763258c from=translated src=- shape=882180f3 vocab=f75615fb
-/
theorem killVars_segreMonomial_of_disjoint (s : Finset (Vars N)) (j : Fin N → Fin 3)
    (hj : ∀ b, (b, j b) ∉ s) :
    killVars (k := k) s (segreMonomial j) = segreMonomial j := by
  classical
  simp [segreMonomial, hj]

/--
@isnad1 id=eq.1h5v.s8.2a84410329dc from=translated src=- shape=b9c688eb vocab=f75615fb
-/
theorem killVars_segreMonomial_of_mem (s : Finset (Vars N)) (j : Fin N → Fin 3)
    (b : Fin N) (hb : (b, j b) ∈ s) :
    killVars (k := k) s (segreMonomial j) = 0 := by
  classical
  simp only [segreMonomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])

/-- Choose the newly killed variable in its block and the protected coordinate `2`
in every other block. -/
def separatingChoice (v : Vars N) (b : Fin N) : Fin 3 :=
  if b = v.1 then v.2 else 2

/--
@isnad1 id=not.2h4v.s6.71fd9759c5ea from=translated src=- shape=1ddcd5cd vocab=57ea4a3a
-/
theorem separatingChoice_avoids {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) {v : Vars N} (hv : v ∉ s) :
    ∀ b, (b, separatingChoice v b) ∉ s := by
  intro b
  by_cases h : b = v.1
  · subst b
    simpa [separatingChoice] using hv
  · simpa [separatingChoice, h] using hprotect b

/-- Each additional killed coordinate strictly increases the contracted prime ideal.
@isnad1 id=lt.2h4v.s11.b21ff2776c5d from=translated src=- shape=475b1185 vocab=86aee8b9
-/
theorem killedIdeal_lt_insert {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) {v : Vars N} (hv : v ∉ s) :
    killedIdeal (k := k) s < killedIdeal (insert v s) := by
  classical
  refine lt_of_le_of_ne (killedIdeal_mono (Finset.subset_insert _ _)) ?_
  intro heq
  have hmem : segre (k := k) (separatingChoice v) ∈ killedIdeal (insert v s) := by
    rw [mem_killedIdeal, coe_segre]
    apply killVars_segreMonomial_of_mem _ _ v.1
    simp [separatingChoice]
  rw [← heq, mem_killedIdeal, coe_segre,
    killVars_segreMonomial_of_disjoint s _ (separatingChoice_avoids hprotect hv)] at hmem
  exact segreMonomial_ne_zero _ hmem

/-- The final strict step kills the remaining positive-degree balanced monomials.
@isnad1 id=lt.1h3v.s11.1b26decbb3f8 from=translated src=- shape=633fe758 vocab=8045cbcf
-/
theorem killedIdeal_lt_vertexIdeal [NeZero N] {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) :
    killedIdeal (k := k) s < vertexIdeal k N := by
  refine lt_of_le_of_ne (killedIdeal_le_vertexIdeal s) ?_
  intro heq
  have hmem : segre (k := k) (fun _ : Fin N => 2) ∈ vertexIdeal k N := by
    simp
  rw [← heq, mem_killedIdeal, coe_segre,
    killVars_segreMonomial_of_disjoint s _ hprotect] at hmem
  exact segreMonomial_ne_zero _ hmem

/-- The height of a contracted variable ideal is at least the number of killed
coordinates, as long as one coordinate in every block remains protected.
@isnad1 id=le.1h3v.s8.3fdd06408ad9 from=translated src=- shape=9e3c6120 vocab=512c8be7
-/
theorem card_le_height_killedIdeal (s : Finset (Vars N))
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) :
    (s.card : ℕ∞) ≤ (killedIdeal (k := k) s).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    have hs : ∀ b, (b, (2 : Fin 3)) ∉ s := by
      intro b hb
      exact hprotect b (Finset.mem_insert_of_mem hb)
    have hlt : (killedIdeal (k := k) s).height + 1 ≤ (killedIdeal (k := k) (insert v s)).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime (killedIdeal_lt_insert (k := k) hs hv)
    calc
      ((insert v s).card : ℕ∞) = (s.card : ℕ∞) + 1 := by simp [hv]
      _ ≤ (killedIdeal (k := k) s).height + 1 := add_le_add (ih hs) le_rfl
      _ ≤ (killedIdeal (k := k) (insert v s)).height := hlt

/-- The Segre cone vertex has height at least `2*N + 1`.
The proof constructs all `2*N + 1` strict prime-ideal steps explicitly.
@isnad1 id=le.0h2v.s8.8b323260bdc8 from=translated src=- shape=f5730035 vocab=c0c98f95
-/
theorem vertexIdeal_height_lower_bound [NeZero N] :
    (2 * N + 1 : ℕ∞) ≤ (vertexIdeal k N).height := by
  classical
  let s : Finset (Vars N) := Finset.univ ×ˢ ({0, 1} : Finset (Fin 3))
  have hs : ∀ b, (b, (2 : Fin 3)) ∉ s := by
    intro b
    simp [s]
  have hcard : s.card = 2 * N := by
    simp [s, Finset.card_product, Nat.mul_comm]
  have hlt : (killedIdeal (k := k) s).height + 1 ≤ (vertexIdeal k N).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (killedIdeal_lt_vertexIdeal (k := k) hs)
  calc
    (2 * N + 1 : ℕ∞) = (s.card : ℕ∞) + 1 := by simp [hcard]
    _ ≤ (killedIdeal (k := k) s).height + 1 :=
      add_le_add (card_le_height_killedIdeal s hs) le_rfl
    _ ≤ (vertexIdeal k N).height := hlt

end Height

section CommonZeros

variable [Field k]

/--
@isnad1 id=eq.2h4v.s7.66622cb8be22 from=translated src=- shape=58ab5571 vocab=9414d25c
-/
theorem IsMultiHomogeneousOfDegree.constantCoeff_eq_zero [NeZero N]
    {f : MvPolynomial (Vars N) k} {r : ℕ}
    (hf : IsMultiHomogeneousOfDegree f r) (hr : 0 < r) : constantCoeff f = 0 := by
  change f.coeff 0 = 0
  by_contra h
  have hdeg := hf 0 h (0 : Fin N)
  simp only [blockDegree_zero] at hdeg
  omega

/-- On an assignment with one zero block, any balanced polynomial evaluates
to its constant coefficient.
@isnad1 id=eq.2h5v.s9.b4bbd3990cd4 from=translated src=- shape=86249cd6 vocab=6045d964
-/
theorem eval_eq_constantCoeff_of_block_zero [NeZero N]
    {p : MvPolynomial (Vars N) k} (hp : p ∈ balancedAlgebra k N)
    {x : Vars N → k} {b : Fin N} (hx : ∀ j, x (b, j) = 0) :
    eval x p = constantCoeff p := by
  classical
  rw [← adjoin_segre_eq_balancedAlgebra] at hp
  refine Algebra.adjoin_induction (p := fun p _ => eval x p = constantCoeff p)
    ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨j, rfl⟩
    rw [constantCoeff_segreMonomial]
    simp only [segreMonomial, map_prod, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (hx (j b))
  · intro a
    simp
  · intro p q _ _ hp hq
    simp only [map_add, hp, hq]
  · intro p q _ _ hp hq
    simp only [map_mul, hp, hq]

variable [IsAlgClosed k] [NeZero N]

/-- If balanced polynomials with zero constant term have no common zero with all
blocks nonzero, their ideal in the balanced subalgebra has radical the vertex.
This is the affine Nullstellensatz plus the explicitly proved retraction.
@isnad1 id=eq.2h4v.s12.08214d07e63b from=translated src=- shape=66010c28 vocab=2b519667
-/
theorem radical_span_eq_vertex_of_no_common_zero {ι : Type*} [Finite ι]
    (f : ι → balancedAlgebra k N) (hf : ∀ i, f i ∈ vertexIdeal k N)
    (hno : ¬ ∃ x : Vars N → k, (∀ b, ∃ j, x (b, j) ≠ 0) ∧
      ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0) :
    (Ideal.span (Set.range f)).radical = vertexIdeal k N := by
  classical
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (vertexIdeal_isPrime (k := k) (N := N))).mpr
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hf i
  · intro p hp
    apply (mem_radical_span_range_coe_iff f p).mp
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro x hx
    have hfx : ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0 := by
      intro i
      exact hx _ (Ideal.mem_span_range_self (x := i))
    have hbad : ∃ b, ∀ j, x (b, j) = 0 := by
      by_contra! hgood
      exact hno ⟨x, hgood, hfx⟩
    obtain ⟨b, hb⟩ := hbad
    change eval x (p : MvPolynomial (Vars N) k) = 0
    rw [eval_eq_constantCoeff_of_block_zero p.property hb]
    exact (mem_vertexIdeal p).mp hp

end CommonZeros

end KoetheMultiProjective

end
