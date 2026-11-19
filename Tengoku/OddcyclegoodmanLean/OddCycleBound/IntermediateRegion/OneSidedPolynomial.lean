import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Expansion
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.GraphonKrylovBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion

noncomputable def oneSidedUCoeff (p : Real) (s : Nat → Real) (n : Nat) : Real :=
  if 2 ≤ n then
    ∑ j ∈ Finset.range (n - 1), p ^ (n - 2 - j) * (-1 : Real) ^ j * s j
  else 0

noncomputable def oneSidedLogCoeff (p : Real) (s : Nat → Real) (m : Nat) : Real :=
  ∑ k ∈ Finset.range m,
    momentConv (oneSidedUCoeff p s) (k + 1) m / (k + 1 : Nat)

noncomputable def oneSidedShiftPolynomial
    (p : Real) (s : Nat → Real) (m : Nat) : Real :=
  m * oneSidedLogCoeff p s m

/--
@isnad1 id=eq.0h2v.s4.6880a81814c8 from=translated src=- shape=093dbb48 vocab=db17f6b3
-/
@[simp] theorem oneSidedUCoeff_zero (p : Real) (s : Nat → Real) :
    oneSidedUCoeff p s 0 = 0 := by simp [oneSidedUCoeff]

/--
@isnad1 id=le.1h3v.s5.f6be3d0ed750 from=translated src=- shape=db85be62 vocab=2b871e63
-/
theorem momentConv_nonneg {s : Nat → Real} (hs : ∀ j, 0 ≤ s j) :
    ∀ r j, 0 ≤ momentConv s r j
  | 0, j => by cases j <;> simp [momentConv]
  | r + 1, j => by
      rw [momentConv_succ]
      exact Finset.sum_nonneg fun i hi =>
        mul_nonneg (hs i) (momentConv_nonneg hs r (j - i))

/--
@isnad1 id=eq.0h2v.s4.c52905629662 from=translated src=- shape=ce367421 vocab=601cb9b3
-/
@[simp] theorem momentConv_one (s : Nat → Real) (j : Nat) :
    momentConv s 1 j = s j := by
  rw [momentConv_succ]
  simp only [momentConv]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have hblt : b < j := by
      have hble : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
      exact lt_of_le_of_ne hble hbj
    have hne : j - b ≠ 0 := fun hzero =>
      (Nat.not_le_of_gt hblt) (Nat.sub_eq_zero_iff_le.mp hzero)
    simp [hne]
  · simp

/--
@isnad1 id=le.1h3v.s5.9c41c2d2f0c4 from=translated src=- shape=c7640574 vocab=e0d1c968
-/
theorem oneSidedLogCoeff_nonneg
    {p : Real} {s : Nat → Real}
    (hu : ∀ n, 0 ≤ oneSidedUCoeff p s n) (m : Nat) :
    0 ≤ oneSidedLogCoeff p s m := by
  unfold oneSidedLogCoeff
  exact Finset.sum_nonneg fun k hk =>
    div_nonneg (momentConv_nonneg hu (k + 1) m) (Nat.cast_nonneg _)

/--
@isnad1 id=le.1h3v.s5.089490a5b93b from=translated src=- shape=c7640574 vocab=9bd5e206
-/
theorem oneSidedShiftPolynomial_nonneg
    {p : Real} {s : Nat → Real}
    (hu : ∀ n, 0 ≤ oneSidedUCoeff p s n) (m : Nat) :
    0 ≤ oneSidedShiftPolynomial p s m := by
  exact mul_nonneg (Nat.cast_nonneg m) (oneSidedLogCoeff_nonneg hu m)

noncomputable def oneSidedGeom (p : Real) (n : Nat) (lambda : Real) : Real :=
  ∑ j ∈ Finset.range (n - 1), p ^ (n - 2 - j) * lambda ^ j

/--
@isnad1 id=eq.2h3v.s6.c7bb1ec1385b from=translated src=- shape=e502015b vocab=7f6e8c25
-/
theorem oneSidedGeom_mul_sub
    {p lambda : Real} {n : Nat} (hn : 2 ≤ n) (hlp : lambda ≤ p) :
    oneSidedGeom p n lambda * (p - lambda) =
      p ^ (n - 1) - lambda ^ (n - 1) := by
  have hnsub : n - 2 = (n - 1) - 1 := by omega
  have hsum :
      oneSidedGeom p n lambda =
        ∑ j ∈ Finset.range (n - 1),
          p ^ j * lambda ^ ((n - 1) - 1 - j) := by
    unfold oneSidedGeom
    rw [hnsub]
    calc
      (∑ j ∈ Finset.range (n - 1),
          p ^ ((n - 1) - 1 - j) * lambda ^ j) =
          ∑ j ∈ Finset.range (n - 1),
            lambda ^ j * p ^ ((n - 1) - 1 - j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = ∑ j ∈ Finset.range (n - 1),
          p ^ j * lambda ^ ((n - 1) - 1 - j) := by
            exact (geom_sum₂_comm lambda p (n - 1))
  rw [hsum]
  exact geom_sum₂_mul_of_ge hlp (n - 1)

/--
@isnad1 id=le.4h3v.s5.51518380ffa7 from=translated src=- shape=a88773f5 vocab=c1c3ba8b
-/
theorem oneSidedGeom_nonneg
    {p lambda : Real} {n : Nat} (hn : 2 ≤ n)
    (hp0 : 0 ≤ p) (hlower : -p ≤ lambda) (hupper : lambda ≤ p) :
    0 ≤ oneSidedGeom p n lambda := by
  have habs : |lambda| ≤ p := abs_le.mpr ⟨hlower, hupper⟩
  have hpowAbs : |lambda| ^ (n - 1) ≤ p ^ (n - 1) :=
    pow_le_pow_left₀ (abs_nonneg lambda) habs _
  have hlpow : lambda ^ (n - 1) ≤ p ^ (n - 1) := by
    calc
      lambda ^ (n - 1) ≤ |lambda ^ (n - 1)| := le_abs_self _
      _ = |lambda| ^ (n - 1) := abs_pow _ _
      _ ≤ p ^ (n - 1) := hpowAbs
  have hprod : 0 ≤ oneSidedGeom p n lambda * (p - lambda) := by
    rw [oneSidedGeom_mul_sub hn hupper]
    linarith
  have hsub : 0 ≤ p - lambda := sub_nonneg.mpr hupper
  by_cases heq : lambda = p
  · subst lambda
    unfold oneSidedGeom
    exact Finset.sum_nonneg fun j hj => mul_nonneg (pow_nonneg hp0 _)
      (pow_nonneg hp0 _)
  · have hsubpos : 0 < p - lambda := sub_pos.mpr (lt_of_le_of_ne hupper heq)
    exact nonneg_of_mul_nonneg_left hprod hsubpos

section Atomic

variable {ι : Type*} [Fintype ι]

private theorem negOnePow_mul_negOnePow (j : Nat) :
    (-1 : Real) ^ j * (-1 : Real) ^ j = 1 := by
  rw [← pow_add, (Even.add_self j).neg_one_pow]

/--
@isnad1 id=eq.1h5v.s6.e183a4ab65e5 from=translated src=- shape=843d3afc vocab=c6eff12d
-/
theorem oneSidedUCoeff_atomic
    (p : Real) (w lambda : ι → Real) {n : Nat} (hn : 2 ≤ n) :
    oneSidedUCoeff p
        (fun j => (-1 : Real) ^ j * atomicMoment w lambda j) n =
      ∑ i, w i * oneSidedGeom p n (lambda i) := by
  classical
  unfold oneSidedUCoeff
  rw [ite_eq_left hn]
  simp_rw [atomicMoment]
  calc
    (∑ j ∈ Finset.range (n - 1),
        p ^ (n - 2 - j) * (-1 : Real) ^ j *
          ((-1 : Real) ^ j * ∑ i, w i * lambda i ^ j)) =
        ∑ j ∈ Finset.range (n - 1),
          ∑ i, w i * (p ^ (n - 2 - j) * lambda i ^ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            calc
              p ^ (n - 2 - j) * (-1 : Real) ^ j *
                    ((-1 : Real) ^ j * ∑ i, w i * lambda i ^ j) =
                  p ^ (n - 2 - j) * ∑ i, w i * lambda i ^ j := by
                    have hsign := negOnePow_mul_negOnePow j
                    calc
                      _ = p ^ (n - 2 - j) *
                          (((-1 : Real) ^ j * (-1 : Real) ^ j) *
                            ∑ i, w i * lambda i ^ j) := by ring
                      _ = _ := by rw [hsign, one_mul]
              _ = ∑ i, w i * (p ^ (n - 2 - j) * lambda i ^ j) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
    _ = ∑ i, ∑ j ∈ Finset.range (n - 1),
          w i * (p ^ (n - 2 - j) * lambda i ^ j) := by
            rw [Finset.sum_comm]
    _ = ∑ i, w i * oneSidedGeom p n (lambda i) := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold oneSidedGeom
          rw [Finset.mul_sum]

end Atomic

section Graphon

open MeasureTheory

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

noncomputable def complementCompressionMoment
    (_hW : IsGraphon W mu) (j : Nat) : Real :=
  (-1 : Real) ^ j * specMoment W mu j

noncomputable def graphonOneSidedShift
    (hW : IsGraphon W mu) (m : Nat) : Real :=
  oneSidedShiftPolynomial (edgeDensity W mu)
    (complementCompressionMoment hW) m

/--
@isnad1 id=eq.2h4v.s15.f6c63dd2f0aa from=translated src=- shape=72249f2c vocab=20f61f4f
-/
theorem graphon_oneSidedUCoeff_eq_atomic
    (hW : IsGraphon W mu) {n : Nat} (hn : 2 ≤ n) :
    oneSidedUCoeff (edgeDensity W mu) (complementCompressionMoment hW) n =
      ∑ i, graphonAtomWeight hW (n - 1) i *
        oneSidedGeom (edgeDensity W mu) n
          (graphonAtomEigenvalue hW (n - 1) i) := by
  classical
  let w := graphonAtomWeight hW (n - 1)
  let lambda := graphonAtomEigenvalue hW (n - 1)
  calc
    oneSidedUCoeff (edgeDensity W mu) (complementCompressionMoment hW) n =
        oneSidedUCoeff (edgeDensity W mu)
          (fun j => (-1 : Real) ^ j * atomicMoment w lambda j) n := by
            unfold oneSidedUCoeff
            rw [ite_eq_left hn, ite_eq_left hn]
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : j < n - 1 := Finset.mem_range.mp hj
            dsimp [w, lambda]
            rw [complementCompressionMoment,
              specMoment_eq_graphonAtomicMoment (d := n - 1) (j := j) hW hjlt.le]
    _ = ∑ i, w i * oneSidedGeom (edgeDensity W mu) n (lambda i) :=
      oneSidedUCoeff_atomic _ _ _ hn
    _ = _ := rfl

/--
@isnad1 id=le.2h4v.s6.0deda2f32b7e from=translated src=- shape=a1db15d0 vocab=b6e55247
-/
theorem graphon_oneSidedUCoeff_nonneg
    (hW : IsGraphon W mu) (hp : 1 / 2 < edgeDensity W mu) (n : Nat) :
    0 ≤ oneSidedUCoeff (edgeDensity W mu)
      (complementCompressionMoment hW) n := by
  by_cases hn : 2 ≤ n
  · rw [graphon_oneSidedUCoeff_eq_atomic hW hn]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (graphonAtomWeight_nonneg hW (n - 1) i)
        (oneSidedGeom_nonneg hn (by linarith)
          (by
            have hmem := graphonAtomEigenvalue_mem_halfInterval hW (n - 1) i
            linarith [hmem.1])
          (by
            have hmem := graphonAtomEigenvalue_mem_halfInterval hW (n - 1) i
            linarith [hmem.2]))
  · simp [oneSidedUCoeff, hn]

/--
@isnad1 id=le.2h4v.s6.77b8ed6ab230 from=translated src=- shape=85b924ce vocab=bf75cdb1
-/
theorem graphonOneSidedShift_nonneg
    (hW : IsGraphon W mu) (hp : 1 / 2 < edgeDensity W mu) (m : Nat) :
    0 ≤ graphonOneSidedShift hW m := by
  exact oneSidedShiftPolynomial_nonneg
    (graphon_oneSidedUCoeff_nonneg hW hp) m

end Graphon

end OddCycleBound.IntermediateRegion
