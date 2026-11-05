module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HilbertBurch
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Quotient
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Numerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Degreewise Hilbert–Burch exactness for genuinely homogeneous entries.
Integer shifts include the vanishing pieces in negative degrees. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] {n c m : ℕ}

/-- Homogeneous forms with an integer degree; the space is zero in negative degrees.-/
def signedForms (K : Type*) [Field K] (n : ℕ) (t : ℤ) : Submodule K (Poly K n) :=
  if 0 ≤ t then Forms K n t.toNat else ⊥

/-- Homogeneous projection with the same negative-degree convention.-/
def signedComponent (t : ℤ) : Poly K n →ₗ[K] Poly K n :=
  if 0 ≤ t then homogeneousComponent t.toNat else 0

/--
@isnad1 id=finite.0h3v.s7.052334f558cc from=translated src=- shape=bad79076 vocab=63b4d411
-/
instance signedFormsFinite (t : ℤ) : Module.Finite K (signedForms K n t) := by
  by_cases ht : 0 ≤ t
  · rw [signedForms, ite_eq_left ht]
    infer_instance
  · rw [signedForms, ite_eq_right ht]
    infer_instance

/--
@isnad1 id=eq.0h3v.s5.f45ff5c49c11 from=translated src=- shape=e96e4b17 vocab=e865ad09
-/
@[simp] theorem signedForms_nat (t : ℕ) : signedForms K n t = Forms K n t := by
  simp [signedForms]

/--
@isnad1 id=eq.0h3v.s6.97515cc5ba34 from=translated src=- shape=b670fb21 vocab=520fbcde
-/
@[simp] theorem signedComponent_nat (t : ℕ) :
    (signedComponent (K := K) (n := n) t) = homogeneousComponent t := by
  simp [signedComponent]

/--
@isnad1 id=mem.0h4v.s8.aca4706a2d86 from=translated src=- shape=5c167e63 vocab=848f8ee6
-/
theorem signedComponent_mem (t : ℤ) (f : Poly K n) :
    signedComponent t f ∈ signedForms K n t := by
  by_cases ht : 0 ≤ t
  · simpa [signedComponent, signedForms, ht] using homogeneousComponent_mem t.toNat f
  · simp [signedComponent, signedForms, ht]

/--
@isnad1 id=eq.0h4v.s9.6d3939a8af17 from=translated src=- shape=3dbf6d10 vocab=9482410d
-/
theorem signedComponent_self (t : ℤ) (f : signedForms K n t) :
    signedComponent t f.val = f.val := by
  by_cases ht : 0 ≤ t
  · have hf : f.val.IsHomogeneous t.toNat := by simpa [signedForms, ht] using f.property
    simpa [signedComponent, ht] using homogeneousComponent_eq_self hf
  · have hf : f.val = 0 := by simpa [signedForms, ht] using f.property
    simp [signedComponent, ht, hf]

/--
@isnad1 id=iff.0h4v.s8.30e74bff6f08 from=translated src=- shape=7d07cb0b vocab=848f8ee6
-/
theorem mem_signedForms_iff_component_self (t : ℤ) (f : Poly K n) :
    f ∈ signedForms K n t ↔ signedComponent t f = f := by
  constructor
  · intro h
    exact signedComponent_self t ⟨f, h⟩
  · intro h
    exact h ▸ signedComponent_mem t f

/-- Homogeneous-component extraction commutes with a homogeneous factor even
when the coefficient degree is negative.
@isnad1 id=eq.1h6v.s8.ca3c85b26696 from=translated src=- shape=b7b211e1 vocab=9f33333b
-/
theorem signedComponent_mul_form (t : ℤ) {δ : ℕ} (f p : Poly K n)
    (hf : f.IsHomogeneous δ) :
    signedComponent (t + δ) (f * p) = f * signedComponent t p := by
  by_cases ht : 0 ≤ t
  · have hsum : 0 ≤ t + (δ : ℤ) := by omega
    have hnat : (t + (δ : ℤ)).toNat = δ + t.toNat := by omega
    simp only [signedComponent, ht, hsum, ite_true, hnat]
    exact homogeneousComponent_mul_form t.toNat f p hf
  · have htneg : t < 0 := by omega
    by_cases hsum : 0 ≤ t + (δ : ℤ)
    · have hsmall : (t + (δ : ℤ)).toNat < δ := by omega
      simp only [signedComponent, ht, hsum, ite_true, ite_false, LinearMap.zero_apply, mul_zero]
      exact homogeneousComponent_mul_eq_zero_of_lt _ hsmall f p hf
    · simp [signedComponent, ht, hsum]

/-- Signed cofactor minors have the complementary row degree.
@isnad1 id=ishomoge.1h6v.s7.92b3f3755c1b from=translated src=- shape=fe5ed96c vocab=1a7e839b
-/
theorem signedMaximalMinor_homogeneous_total
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (i : Fin (c + 1)) :
    (signedMaximalMinor B i).IsHomogeneous ((∑ j, δ j) - δ i) := by
  have hsum : ∑ j, δ j = δ i + ∑ j : Fin c, δ (i.succAbove j) :=
    Fin.sum_univ_succAbove δ i
  have hminor := maximalMinor_homogeneous B δ hB i
  rw [hsum, Nat.add_sub_cancel_left]
  have hconst : ((-1 : Poly K n) ^ i.val).IsHomogeneous 0 := by
    simpa using (isHomogeneous_C (σ := Fin n) (-1 : K)).pow i.val
  simpa [signedMaximalMinor] using hconst.mul hminor

/-- The graded free middle term corresponding to row degrees `δ`.-/
abbrev rowForms (K : Type*) [Field K] (n : ℕ) {m : ℕ} (δ : Fin m → ℕ) (e : ℤ) :=
  ∀ i : Fin m, signedForms K n (e + δ i)

/-- Coefficientwise inclusion in the ungraded polynomial module.-/
def rowFormsVal {δ : Fin m → ℕ} {e : ℤ} :
    rowForms K n δ e →ₗ[K] (Fin m → Poly K n) where
  toFun v i := (v i).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extract the appropriate homogeneous coefficient in each row.-/
def rowFormsComponent (δ : Fin m → ℕ) (e : ℤ) :
    (Fin m → Poly K n) →ₗ[K] rowForms K n δ e where
  toFun v i := ⟨signedComponent (e + δ i) (v i), signedComponent_mem _ _⟩
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

/--
@isnad1 id=eq.0h7v.s10.246d7a2dd0a4 from=translated src=- shape=8fc4cb24 vocab=433ed497
-/
@[simp] theorem rowFormsComponent_val (δ : Fin m → ℕ) (e : ℤ)
    (v : Fin m → Poly K n) (i : Fin m) :
    (rowFormsComponent δ e v i).val = signedComponent (e + δ i) (v i) := rfl

/--
@isnad1 id=eq.0h6v.s11.8ba384b871d2 from=translated src=- shape=dde16d9c vocab=9cfc3c67
-/
@[simp] theorem rowFormsComponent_self (δ : Fin m → ℕ) (e : ℤ)
    (v : rowForms K n δ e) : rowFormsComponent δ e (rowFormsVal v) = v := by
  funext i
  apply Subtype.ext
  exact signedComponent_self _ (v i)

/-- Homogeneous projection of the matrix equation is its equation on the
projected coefficients.
@isnad1 id=eq.1h8v.s9.acae49d6b2ca from=translated src=- shape=6540b0f1 vocab=56de218c
-/
theorem signedComponent_mulVec
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (e : ℤ) (w : Fin c → Poly K n) (i : Fin (c + 1)) :
    signedComponent (e + δ i) (B.mulVec w i) =
      B.mulVec (fun j => signedComponent e (w j)) i := by
  simp only [Matrix.mulVec, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact signedComponent_mul_form e (B i j) (w j) (hB i j)

/-- The homogeneous matrix map between its shifted free pieces.-/
def gradedMatrixMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i)) (e : ℤ) :
    (Fin c → signedForms K n e) →ₗ[K] rowForms K n δ e where
  toFun w i := ⟨B.mulVec (fun j => (w j).val) i, by
    apply (mem_signedForms_iff_component_self _ _).mpr
    rw [signedComponent_mulVec B δ hB]
    simp only [signedComponent_self]⟩
  map_add' w u := by ext i; simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' r w := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_eq_mul]

/--
@isnad1 id=eq.1h8v.s11.0a723b1f798a from=translated src=- shape=6f60f8fa vocab=920846b8
-/
@[simp] theorem gradedMatrixMap_val
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (e : ℤ) (w : Fin c → signedForms K n e) (i : Fin (c + 1)) :
    (gradedMatrixMap B δ hB e w i).val = B.mulVec (fun j => (w j).val) i := rfl

/-- Projecting an ungraded cofactor combination extracts exactly its shifted
homogeneous coefficients.
@isnad1 id=eq.1h7v.s12.1025ce3ebb68 from=translated src=- shape=fed4d038 vocab=cdcfb5c1
-/
theorem signedComponent_cofactorMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (e : ℤ) (v : Fin (c + 1) → Poly K n) :
    signedComponent (e + ∑ i, δ i) (cofactorMap B v) =
      cofactorMap B (rowFormsVal (rowFormsComponent δ e v)) := by
  simp only [cofactorMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hle : δ i ≤ ∑ j, δ j := Finset.single_le_sum (fun j _ => Nat.zero_le (δ j)) (Finset.mem_univ i)
  have heq : e + (∑ j, δ j : ℕ) = (e + δ i) + ((∑ j, δ j : ℕ) - δ i : ℕ) := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [heq]
  exact signedComponent_mul_form (e + δ i) (signedMaximalMinor B i) (v i)
    (signedMaximalMinor_homogeneous_total B δ hB i)

/-- The homogeneous cofactor map between the actual shifted polynomial pieces.-/
def gradedCofactorMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i)) (e : ℤ) :
    rowForms K n δ e →ₗ[K] signedForms K n (e + ∑ i, δ i) where
  toFun v := ⟨cofactorMap B (rowFormsVal v), by
    apply (mem_signedForms_iff_component_self _ _).mpr
    rw [signedComponent_cofactorMap B δ hB, rowFormsComponent_self]⟩
  map_add' v w := by
    apply Subtype.ext
    simp only [rowFormsVal, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Submodule.coe_add]
    exact map_add (cofactorMap B) _ _
  map_smul' r v := by
    apply Subtype.ext
    simp [cofactorMap_apply, rowFormsVal]

/--
@isnad1 id=eq.1h7v.s12.f87c9ff0f831 from=translated src=- shape=de9ad074 vocab=67ce64ee
-/
@[simp] theorem gradedCofactorMap_val
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (e : ℤ) (v : rowForms K n δ e) :
    (gradedCofactorMap B δ hB e v).val = cofactorMap B (rowFormsVal v) := rfl

/-- Genuine Hilbert–Burch exactness restricts to every homogeneous degree,
including negative coefficient degrees.
@isnad1 id=eq.2h6v.s11.c2e353c02035 from=translated src=- shape=23cc397e vocab=a79a724c
-/
theorem graded_ker_cofactor_eq_range
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (gradedCofactorMap B δ hB e).ker = (gradedMatrixMap B δ hB e).range := by
  apply le_antisymm
  · intro v hv
    have hpoly : rowFormsVal v ∈ (cofactorMap B).ker := by
      have h := congrArg Subtype.val hv
      exact h
    rw [ker_cofactorMap_eq_range B hprimitive] at hpoly
    obtain ⟨w, hw⟩ := hpoly
    change B.mulVec w = rowFormsVal v at hw
    let u : Fin c → signedForms K n e :=
      fun j => ⟨signedComponent e (w j), signedComponent_mem _ _⟩
    refine ⟨u, ?_⟩
    funext i
    apply Subtype.ext
    change B.mulVec (fun j => signedComponent e (w j)) i = (v i).val
    rw [← signedComponent_mulVec B δ hB, hw]
    exact signedComponent_self _ (v i)
  · rintro v ⟨w, rfl⟩
    apply Subtype.ext
    exact cofactorMap_mulVec B (fun j => (w j).val)

/-- The first graded map is injective, as a consequence of the genuine
ungraded maximal-minor theorem.
@isnad1 id=injectiv.2h6v.s11.a551d31f1ca4 from=translated src=- shape=a005a53d vocab=54cdbab0
-/
theorem gradedMatrixMap_injective
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    Function.Injective (gradedMatrixMap B δ hB e) := by
  intro w u h
  have hpoly : B.mulVec (fun j => (w j).val) = B.mulVec (fun j => (u j).val) := by
    exact congrArg rowFormsVal h
  have hcoeff := mulVec_injective_of_primitive B hprimitive hpoly
  funext j
  apply Subtype.ext
  exact congrFun hcoeff j

/-- The actual ideal generated by the cofactor minors.-/
def maximalMinorIdeal
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) : Ideal (Poly K n) :=
  Ideal.span (Set.range (signedMaximalMinor B))

/-- The homogeneous piece of the genuine maximal-minor ideal.-/
def gradedMinorIdealPiece
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (e : ℤ) :
    Submodule K (signedForms K n (e + ∑ i, δ i)) :=
  (maximalMinorIdeal B).restrictScalars K |>.comap (signedForms K n (e + ∑ i, δ i)).subtype

/-- Every homogeneous equation in the maximal-minor ideal has homogeneous
cofactor coefficients of the required complementary degrees.
@isnad1 id=eq.1h6v.s10.33e6b7c12be5 from=translated src=- shape=dd512294 vocab=784b8640
-/
theorem gradedCofactorMap_range_eq_idealPiece
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i)) (e : ℤ) :
    (gradedCofactorMap B δ hB e).range = gradedMinorIdealPiece B δ e := by
  apply le_antisymm
  · rintro f ⟨v, rfl⟩
    change cofactorMap B (rowFormsVal v) ∈ maximalMinorIdeal B
    change cofactorMap B (rowFormsVal v) ∈
      Submodule.span (Poly K n) (Set.range (signedMaximalMinor B))
    rw [← cofactorMap_range_eq_span]
    exact ⟨rowFormsVal v, rfl⟩
  · intro f hf
    have hfpoly : f.val ∈ (cofactorMap B).range := by
      rw [cofactorMap_range_eq_span]
      exact hf
    obtain ⟨v, hv⟩ := hfpoly
    refine ⟨rowFormsComponent δ e v, ?_⟩
    apply Subtype.ext
    change cofactorMap B (rowFormsVal (rowFormsComponent δ e v)) = f.val
    rw [← signedComponent_cofactorMap B δ hB, hv]
    exact signedComponent_self _ f

/-- The dimension of each signed ternary form space is the paper's `N₂`.
@isnad1 id=eq.0h2v.s8.c54638a8fbf3 from=translated src=- shape=b31cce57 vocab=83df35d4
-/
theorem finrank_signedPlaneForms (t : ℤ) :
    (finrank K (signedForms K 3 t) : ℤ) = N₂ t := by
  by_cases ht : 0 ≤ t
  · rw [signedForms, ite_eq_left ht]
    simp [N₂, ht, finrank_plane_forms, N]
  · rw [signedForms, ite_eq_right ht]
    simp [N₂, ht]

/-- The dimension of the graded free middle term is the sum of its row dimensions.
@isnad1 id=eq.0h4v.s9.92e80b0c8fd1 from=translated src=- shape=37a9a4e3 vocab=1130d0d7
-/
theorem finrank_rowPlaneForms (δ : Fin m → ℕ) (e : ℤ) :
    (finrank K (rowForms K 3 δ e) : ℤ) = ∑ i, N₂ (e + δ i) := by
  rw [Module.finrank_pi_fintype, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact finrank_signedPlaneForms (e + δ i)

/-- The Hilbert–Burch image dimension in every degree follows by finite
rank-nullity from the actual exact sequence.
@isnad1 id=eq.2h5v.s11.d7123180d209 from=translated src=- shape=3fcf2098 vocab=9df907f7
-/
theorem gradedMinorIdealPiece_finrank
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (finrank K (gradedMinorIdealPiece B δ e) : ℤ) =
      (∑ i, N₂ (e + δ i)) - (c : ℤ) * N₂ e := by
  have hdim := (gradedCofactorMap B δ hB e).finrank_range_add_finrank_ker
  rw [graded_ker_cofactor_eq_range B δ hB hprimitive,
    LinearMap.finrank_range_of_inj (gradedMatrixMap_injective B δ hB hprimitive e),
    gradedCofactorMap_range_eq_idealPiece B δ hB] at hdim
  have hsrc : (finrank K (Fin c → signedForms K 3 e) : ℤ) = (c : ℤ) * N₂ e := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_signedPlaneForms]
  have hcast := congrArg (fun j : ℕ => (j : ℤ)) hdim
  rw [Nat.cast_add, hsrc, finrank_rowPlaneForms] at hcast
  omega

/-- The genuine homogeneous quotient by the maximal-minor ideal has the
Hilbert–Burch numerator coefficients, in every integer degree.
@isnad1 id=eq.2h5v.s11.79e2d24e03d8 from=translated src=- shape=3947c2a7 vocab=3db79673
-/
theorem gradedMinorQuotient_finrank
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (finrank K ((signedForms K 3 (e + ∑ i, δ i)) ⧸ gradedMinorIdealPiece B δ e) : ℤ) =
      N₂ (e + ∑ i, δ i) - (∑ i, N₂ (e + δ i)) + (c : ℤ) * N₂ e := by
  have h := (gradedMinorIdealPiece B δ e).finrank_quotient_add_finrank
  have hcast := congrArg (fun j : ℕ => (j : ℤ)) h
  rw [Nat.cast_add, finrank_signedPlaneForms,
    gradedMinorIdealPiece_finrank B δ hB hprimitive] at hcast
  omega

/-- Map from the homogeneous forms into the genuine polynomial-ring quotient
by the maximal-minor ideal.-/
def minorFormToRingQuotient
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (t : ℤ) :
    signedForms K n t →ₗ[K] Poly K n ⧸ maximalMinorIdeal B :=
  (Ideal.Quotient.mkₐ K (maximalMinorIdeal B)).toLinearMap.comp
    (signedForms K n t).subtype

/-- The actual homogeneous Hilbert function of the maximal-minor ideal.-/
def minorHilbertFunction
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (t : ℤ) : ℕ :=
  finrank K (minorFormToRingQuotient B t).range

/--
@isnad1 id=eq.0h6v.s10.f6abf7f6416b from=translated src=- shape=bf52860c vocab=a573c590
-/
theorem minorFormToRingQuotient_ker
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (δ : Fin (c + 1) → ℕ) (e : ℤ) :
    (minorFormToRingQuotient B (e + ∑ i, δ i)).ker = gradedMinorIdealPiece B δ e := by
  ext f
  change Ideal.Quotient.mk (maximalMinorIdeal B) f.val = 0 ↔ f.val ∈ maximalMinorIdeal B
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Hilbert–Burch computes the homogeneous image in the actual quotient ring,
not merely a formal alternating dimension expression.
@isnad1 id=eq.2h5v.s8.391f2aceb9c2 from=translated src=- shape=d7fc7b70 vocab=54b03099
-/
theorem minorHilbertFunction_formula
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (minorHilbertFunction B (e + ∑ i, δ i) : ℤ) =
      N₂ (e + ∑ i, δ i) - (∑ i, N₂ (e + δ i)) + (c : ℤ) * N₂ e := by
  have h := (minorFormToRingQuotient B (e + ∑ i, δ i)).quotKerEquivRange.finrank_eq
  rw [minorFormToRingQuotient_ker] at h
  dsimp only [minorHilbertFunction]
  rw [← h]
  exact gradedMinorQuotient_finrank B δ hB hprimitive e

/-- The equivalent formula indexed by the target degree instead of the
coefficient degree.
@isnad1 id=eq.2h5v.s8.2d6138216d9a from=translated src=- shape=33ce1659 vocab=54b03099
-/
theorem minorHilbertFunction_at_degree
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (δ : Fin (c + 1) → ℕ) (hB : ∀ i j, (B i j).IsHomogeneous (δ i))
    (hprimitive : PrimitiveMaximalMinors B) (t : ℤ) :
    (minorHilbertFunction B t : ℤ) = N₂ t -
      (∑ i, N₂ (t - (∑ j, δ j) + δ i)) + (c : ℤ) * N₂ (t - ∑ i, δ i) := by
  have h := minorHilbertFunction_formula B δ hB hprimitive (t - ∑ i, δ i)
  simpa only [sub_add_cancel] using h

end ChoppedPlane
