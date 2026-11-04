import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceEvenAutomorphism
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairTargets
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceTwoReflectionTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms BV_evenV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_two_even_pairs_dephasing` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Triality.SourceVectorPairDephase

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceEvenReflections SourceVectorPairReflection SourceEvenAutomorphism

universe u
variable {K : Type u} [Field K] [CharZero K]

/--
@isnad1 id=eq.2h5v.s6.9b8a2c576333 from=translated src=- shape=6512f357 vocab=2b933c85
-/
theorem BV_evenV (A B x y : VCoord K) (hA : nV A ≠ 0) (hB : nV B ≠ 0) :
    BV (evenV A B x) (evenV A B y) = BV x y := by
  simp only [evenV]
  rw [SourceVectorPairReflection.BV_reflectV A _ _ hA,
    SourceVectorPairReflection.BV_reflectV B _ _ hB]

/--
@isnad1 id=eq.0h5v.s6.582547c9e3f1 from=translated src=- shape=8f6bc521 vocab=db10274e
-/
theorem evenV_add (A B x y : VCoord K) :
    evenV A B (x + y) = evenV A B x + evenV A B y := by
  simp only [evenV, SourceVectorPairReflection.reflectV_add]

/--
@isnad1 id=eq.0h5v.s8.8a61d3e350f2 from=translated src=- shape=028862c3 vocab=cd00a758
-/
theorem evenV_smul (A B x : VCoord K) (q : K) :
    evenV A B (q • x) = q • evenV A B x := by
  simp only [evenV, SourceVectorPairReflection.reflectV_smul]

/-- Two explicit even stages. Each pair `(A_j,B_j)` is applied as reflection
in `B_j` followed by reflection in `A_j`. The orientation root is supplied.
@isnad1 id=ex.3h4v.s8.d77b87142b18 from=translated src=- shape=d4fd0c50 vocab=71bcafa5
-/
theorem exists_two_even_pairs_dephasing
    (v1 v2 : VCoord K) (s : K)
    (ha : nV v1 ≠ 0)
    (hGram : 4 * nV v1 * nV v2 - (BV v1 v2) ^ 2 ≠ 0)
    (hs : s ^ 2 = (BV v1 v2) ^ 2 - 4 * nV v1 * nV v2) :
    ∃ A1 B1 A2 B2 : VCoord K,
      nV A1 ≠ 0 ∧ nV B1 ≠ 0 ∧ nV A2 ≠ 0 ∧ nV B2 ≠ 0 ∧
      evenV A2 B2 (evenV A1 B1 v1) = targetFirst (nV v1) ∧
      evenV A2 B2 (evenV A1 B1 v2) =
        targetSecond (nV v1) (BV v1 v2) s := by
  let a := nV v1
  let h := BV v1 v2
  let m := nV v2
  let t := targetFirst a
  let z := targetSecond a h s
  let e : VCoord K := parityVector
  have he : nV e ≠ 0 := by simp [e]
  have ht : nV t = nV v1 := by simp [t, a, targetFirst_norm]
  have het : BV e t = 0 := by simp [e, t, targetFirst]
  obtain ⟨A1, B1, hA1, hB1, h1⟩ :=
    evenV_eq_of_centers e v1 t he ht.symm ha het
  let w := evenV A1 B1 v2
  have hwNorm : nV w = m := by
    simp [w, m, nV_evenV A1 B1 v2 hA1 hB1]
  have htw : BV t w = h := by
    rw [← h1]
    change BV (evenV A1 B1 v1) (evenV A1 B1 v2) = h
    rw [BV_evenV A1 B1 v1 v2 hA1 hB1]
  let u := orthogonalRemainder t w
  let q := targetRemainder a h s
  have hta : nV t ≠ 0 := by simpa [t, a, targetFirst_norm] using ha
  have htu : BV t u = 0 := BV_orthogonalRemainder t w hta
  have htq : BV t q = 0 := by
    have hq : q = orthogonalRemainder t z := by
      change targetRemainder a h s = orthogonalRemainder t z
      rw [targetRemainder, orthogonalRemainder]
      congr 1
      simp [projectionCoeff, t, z, target_pairing a h s ha, targetFirst_norm]
    rw [hq]
    exact BV_orthogonalRemainder t z hta
  have hu : nV u = (4 * a * m - h ^ 2) / (4 * a) := by
    have H := nV_orthogonalRemainder_identity t w hta
    rw [ht, hwNorm, htw] at H
    apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).2
    linear_combination H
  have hq : nV q = (4 * a * m - h ^ 2) / (4 * a) := by
    rw [targetRemainder_norm a h s ha, hs]
    ring
  have hu0 : nV u ≠ 0 := by
    rw [hu]
    exact div_ne_zero (by simpa [a, h, m] using hGram)
      (mul_ne_zero (by norm_num) ha)
  have heq : BV e q = 0 := by
    change BV parityVector (targetRemainder a h s) = 0
    rw [targetRemainder_eq a h s ha]
    exact BV_parityVector_plane _ _
  have hte : BV t e = 0 := by rw [BV_symmetric]; exact het
  obtain ⟨A2, B2, hA2, hB2, _, _, h2, h2fix⟩ :=
    evenV_eq_fixing e t u q he (hu.trans hq.symm) hu0 heq hte htu htq
  refine ⟨A1, B1, A2, B2, hA1, hB1, hA2, hB2, ?_, ?_⟩
  · rw [h1, h2fix]
  · change evenV A2 B2 w = z
    have hwdecomp : w = u + projectionCoeff t w • t := by
      simp [u, orthogonalRemainder]
    rw [hwdecomp, evenV_add, h2, evenV_smul, h2fix]
    have hc : projectionCoeff t w = h / (2 * a) := by
      simp [projectionCoeff, htw, t, a, targetFirst_norm]
    rw [hc]
    change targetRemainder a h s + (h / (2 * a)) • targetFirst a =
      targetSecond a h s
    rw [targetRemainder]
    exact sub_add_cancel _ _

end AlbertLean.Triality.SourceVectorPairDephase
