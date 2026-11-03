import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.SplitBasicQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conventional basicness and split quotient coordinates

For a finite-dimensional algebra, basicness may be expressed by saying that
the semisimple quotient is reduced: equivalently, every Wedderburn matrix
block has size one.  Over an algebraically closed field this is equivalent to
commutativity of the semisimple quotient, and hence to the intrinsic
split-basic quotient condition used by the coordinate development.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.BasicnessWrapper

universe u

/-- Standard ring-theoretic basicness for a finite-dimensional algebra:
every matrix block in its semisimple quotient has size one.-/
def IsBasicAlgebra (K B : Type u)
    [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B] : Prop :=
  IsReduced (B ⧸ Ring.jacobson B)

private theorem fin_subsingleton_of_pi_matrix_reduced
    (K : Type u) [Field K]
    {n : ℕ} {d : Fin n → ℕ}
    [IsReduced (∀ i, Matrix (Fin (d i)) (Fin (d i)) K)]
    (i : Fin n) : Subsingleton (Fin (d i)) := by
  constructor
  intro a b
  by_contra hab
  let z : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K :=
    Pi.single i (Matrix.single a b 1)
  have hzpow : z ^ 2 = 0 := by
    ext j p q
    by_cases hji : j = i
    · subst j
      simp only [z, Pi.single_eq_same, Pi.pow_apply, Pi.zero_apply, pow_two]
      simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hax : a = x
      · subst x
        have hba : b ≠ a := Ne.symm hab
        simp [hba]
      · simp [hax]
    · simp [z, hji]
  have hz : z = 0 := IsReduced.eq_zero z ⟨2, hzpow⟩
  have hone : (1 : K) = 0 := by
    have := congrArg (fun w ↦ w i a b) hz
    simp [z, Matrix.single] at this
  exact one_ne_zero hone

variable (K B : Type u)
  [Field K] [IsAlgClosed K] [Ring B] [Algebra K B]
  [FiniteDimensional K B]

omit [IsAlgClosed K] in
/-- A commutative semisimple quotient is reduced, so it is basic.  This
implication does not use algebraic closedness.
@isnad1 id=isbasica.1h2v.s8.fd164dc1e864 from=translated src=- shape=9a8468fe vocab=c8abde3f
-/
theorem isBasicAlgebra_of_quotient_mul_comm
    (hcomm : ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x) :
    IsBasicAlgebra K B := by
  let Q := B ⧸ Ring.jacobson B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : CommRing Q :=
    { (inferInstance : Ring Q) with
      mul_comm := hcomm }
  letI : IsSemisimpleRing Q := inferInstance
  exact (inferInstance : IsReduced Q)

/-- Over an algebraically closed field, conventional basicness makes the
semisimple quotient commutative.
@isnad1 id=eq.1h4v.s8.43fb2424ea93 from=translated src=- shape=a2017fab vocab=4ae85386
-/
theorem quotient_mul_comm_of_isBasicAlgebra
    (h : IsBasicAlgebra K B) :
    ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x := by
  let Q := B ⧸ Ring.jacobson B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : FiniteDimensional K Q := inferInstance
  letI : IsReduced Q := h
  letI : IsSemisimpleRing Q := inferInstance
  obtain ⟨n, d, _hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K Q
  letI : IsReduced (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :=
    isReduced_of_injective e.symm e.symm.injective
  have hsub (i : Fin n) : Subsingleton (Fin (d i)) :=
    fin_subsingleton_of_pi_matrix_reduced K i
  intro x y
  apply e.injective
  rw [map_mul, map_mul]
  ext i a b
  haveI : Subsingleton (Fin (d i)) := hsub i
  change
    (∑ j, e x i a j * e y i j b) =
      ∑ j, e y i a j * e x i j b
  apply Finset.sum_congr rfl
  intro j _
  rw [Subsingleton.elim a j, Subsingleton.elim b j, mul_comm]

/-- Over an algebraically closed field, conventional basicness is exactly
commutativity of the semisimple quotient.
@isnad1 id=iff.0h2v.s8.d4889aff9083 from=translated src=- shape=098378b5 vocab=4ae85386
-/
theorem isBasicAlgebra_iff_quotient_mul_comm :
    IsBasicAlgebra K B ↔
      ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x :=
  ⟨quotient_mul_comm_of_isBasicAlgebra K B,
    isBasicAlgebra_of_quotient_mul_comm K B⟩

/-- Conventional basicness over an algebraically closed field supplies the
intrinsic split-basic condition already used downstream.
@isnad1 id=issplitb.1h2v.s5.88d7a55e2387 from=translated src=- shape=bc51ee13 vocab=7848d59b
-/
theorem isSplitBasicQuotient_of_isBasicAlgebra
    (h : IsBasicAlgebra K B) :
    QuotientSubmoduleEquidistribution.SplitBasicQuotient.IsSplitBasicQuotient K B :=
  QuotientSubmoduleEquidistribution.SplitBasicQuotient.isSplitBasicQuotient_of_quotient_mul_comm
    K B (quotient_mul_comm_of_isBasicAlgebra K B h)

/-- In the finite-dimensional algebraically closed setting, conventional
basicness and the downstream intrinsic split-basic quotient predicate are
equivalent.
@isnad1 id=iff.0h2v.s5.1ce89fcdb4f2 from=translated src=- shape=1bb14ae2 vocab=7848d59b
-/
theorem isBasicAlgebra_iff_isSplitBasicQuotient :
    IsBasicAlgebra K B ↔
      QuotientSubmoduleEquidistribution.SplitBasicQuotient.IsSplitBasicQuotient K B := by
  constructor
  · exact isSplitBasicQuotient_of_isBasicAlgebra K B
  · rintro ⟨hcomm, _⟩
    exact isBasicAlgebra_of_quotient_mul_comm K B hcomm

/-- Conventional basicness over an algebraically closed field supplies an
explicit finite coordinate presentation of the semisimple quotient.
@isnad1 id=ex.1h2v.s6.6147e212439c from=translated src=- shape=b2641f3d vocab=b02a6a1c
-/
theorem exists_quotientCoordinateData_of_isBasicAlgebra
    (h : IsBasicAlgebra K B) :
    ∃ n : ℕ,
      Nonempty
        (QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData
          (K := K) (B := B) (I := Fin n)) :=
  QuotientSubmoduleEquidistribution.SplitBasicQuotient.exists_quotientCoordinateData_of_isSplitBasicQuotient
    (isSplitBasicQuotient_of_isBasicAlgebra K B h)

end QuotientSubmoduleEquidistribution.BasicnessWrapper
