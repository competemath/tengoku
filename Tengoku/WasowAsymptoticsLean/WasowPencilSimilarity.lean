import Tengoku.WasowAsymptoticsLean.WasowPencilDescent
import Tengoku.WasowAsymptoticsLean.WasowSingleEigenBlocks
import Tengoku.Seed.Algebra.Polynomial.RingDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms minorGCD_map_associated` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms natDegree_translate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms minorGCD_translate_degree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degreeMass_translate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pencil_sub_scalar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degreeMass_sub_scalar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pencil_similarity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degreeMass_similarity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms single_eigen_pencil_mass_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms single_eigen_pencil_mass_strict` (it only prints; the queue checks the axioms of every declaration). -/

/-! Constant similarity and scalar translation preserve the actual polynomial
pencil degree invariant. These are algebraic invariances, not descent hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilSimilarity
open WasowPencilReduction WasowReductionDescent WasowPencilDescent

variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=associat.0h4v.s7.31fc55ec1d6b from=translated src=- shape=994e8ae8 vocab=328bf0ee
-/
theorem minorGCD_map_associated (T : Matrix ι ι ℂ[X]) (e : ℂ[X] ≃+* ℂ[X]) (k : ℕ) :
    Associated (e (minorGCD T k)) (minorGCD (T.map e) k) := by
  have hmap (A : Matrix ι ι ℂ[X]) (f : ℂ[X] ≃+* ℂ[X]) (r c : Fin k → ι) :
      ((A.map f).submatrix r c).det = f ((A.submatrix r c).det) := by
    exact (RingHom.map_det f.toRingHom _).symm
  apply associated_of_dvd_dvd
  · rw [dvd_minorGCD_iff]
    intro r c
    rw [hmap T e r c]
    obtain ⟨q, hq⟩ := minorGCD_dvd_minor T k r c
    refine ⟨e q, ?_⟩
    rw [← map_mul, hq]
  · have hd : e.symm (minorGCD (T.map e) k) ∣ minorGCD T k := by
      rw [dvd_minorGCD_iff]
      intro r c
      obtain ⟨q, hq⟩ := minorGCD_dvd_minor (T.map e) k r c
      rw [hmap T e r c] at hq
      refine ⟨e.symm q, ?_⟩
      simpa using congrArg e.symm hq
    obtain ⟨q, hq⟩ := hd
    refine ⟨e q, ?_⟩
    simpa using congrArg e hq

/--
@isnad1 id=eq.0h2v.s7.497dbc07ba97 from=translated src=- shape=62e16968 vocab=9ad6ab01
-/
theorem natDegree_translate (p : ℂ[X]) (α : ℂ) :
    (Polynomial.algEquivAevalXAddC α p).natDegree = p.natDegree := by
  simp [Polynomial.algEquivAevalXAddC_apply, ← Polynomial.comp_eq_aeval,
    Polynomial.natDegree_comp]

/--
@isnad1 id=eq.0h4v.s7.7e9c13873f58 from=translated src=- shape=5e69a3d5 vocab=3a2a1194
-/
theorem minorGCD_translate_degree (T : Matrix ι ι ℂ[X]) (α : ℂ) (k : ℕ) :
    (minorGCD (T.map (Polynomial.algEquivAevalXAddC α)) k).natDegree =
      (minorGCD T k).natDegree := by
  have hh := Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated
      (minorGCD_map_associated T (Polynomial.algEquivAevalXAddC α).toRingEquiv k))
  exact hh.symm.trans (natDegree_translate _ α)

/--
@isnad1 id=eq.0h3v.s7.1893a4f58652 from=translated src=- shape=fcbc871e vocab=f3e4afbc
-/
theorem degreeMass_translate (T : Matrix ι ι ℂ[X]) (α : ℂ) :
    WasowPencilDescent.degreeMass (T.map (Polynomial.algEquivAevalXAddC α)) =
      WasowPencilDescent.degreeMass T := by
  unfold WasowPencilDescent.degreeMass
  simp_rw [minorGCD_translate_degree]

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {h : σ → ℕ}

omit [Fintype σ] in
/--
@isnad1 id=eq.0h4v.s8.7b027fb99d43 from=translated src=- shape=ee87b935 vocab=d011206d
-/
theorem pencil_sub_scalar (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ) :
    pencil (C - α • 1) = (pencil C).map (Polynomial.algEquivAevalXAddC α) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;>
    simp [pencil, hij, Polynomial.algEquivAevalXAddC_apply,
      smul_eq_mul, map_sub]
    ; ring

/--
@isnad1 id=eq.0h4v.s8.a91d581abb6f from=translated src=- shape=0ea9b9d9 vocab=d839e04b
-/
theorem degreeMass_sub_scalar (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ) :
    WasowPencilDescent.degreeMass (pencil (C - α • 1)) =
      WasowPencilDescent.degreeMass (pencil C) := by
  rw [pencil_sub_scalar, degreeMass_translate]

/--
@isnad1 id=eq.1h5v.s9.85cc01c62844 from=translated src=- shape=d8e31505 vocab=2eb59ab7
-/
theorem pencil_similarity (C L R : Matrix (OldIndex h) (OldIndex h) ℂ)
    (hLR : L * R = 1) :
    pencil (L * C * R) = L.map Polynomial.C * pencil C * R.map Polynomial.C := by
  unfold pencil
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [← Matrix.map_mul (L := L) (M := R), hLR]
  simp

/--
@isnad1 id=eq.2h5v.s9.f18044f32f62 from=translated src=- shape=9826df97 vocab=8310df0f
-/
theorem degreeMass_similarity (C L R : Matrix (OldIndex h) (OldIndex h) ℂ)
    (hLR : L * R = 1) (hRL : R * L = 1) :
    WasowPencilDescent.degreeMass (pencil (L * C * R)) =
      WasowPencilDescent.degreeMass (pencil C) := by
  rw [pencil_similarity C L R hLR]
  have hm : R.map Polynomial.C * L.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hRL]
    simp
  unfold WasowPencilDescent.degreeMass
  simp_rw [WasowMinorEquivalence.minorGCD_equivalent
    (L.map Polynomial.C) (R.map Polynomial.C) (pencil C)
    (R.map Polynomial.C) (L.map Polynomial.C) hm hm]

/-- The full single-eigenvalue normalization has weak descent for the original
constant matrix, including the scalar translation of its pencil.
@isnad1 id=le.3h4v.s8.ffb40803e7da from=translated src=- shape=c4a06f2b vocab=5e108ce1
-/
theorem single_eigen_pencil_mass_le {s : ℕ} {h : Fin s → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ)
    (hrows : LastRowForm h C) (hlower : WasowSingleEigenBlocks.LowerBlocks C)
    (hN : IsNilpotent (C - α • 1)) :
    WasowPencilDescent.degreeMass (pencil C) ≤
      WasowPencilDescent.degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) := by
  obtain ⟨L, R, T, hLR, hRL, hT, hdiag, hoff, hlow, _⟩ :=
    WasowSingleEigenBlocks.exists_shift_diagonal_similarity C α hrows hlower hN
  have he : WasowPencilDescent.degreeMass (pencil T) =
      WasowPencilDescent.degreeMass (pencil C) := by
    rw [hT, degreeMass_similarity _ _ _ hLR hRL, degreeMass_sub_scalar]
  rw [← he]
  apply pencil_degreeMass_le (WasowSingleEigenBlocks.lastRowForm_of_blocks T hdiag hoff)
  · intro a b hab i j
    exact hlow (show OrderDual.toDual b < OrderDual.toDual a from hab)
  · intro a i j
    exact congrArg (fun A => A i j) (hdiag a)

/-- A nonzero actual off-diagonal block makes the original pencil invariant
strictly smaller after a single-eigenvalue normalized shearing step.
@isnad1 id=lt.5h4v.s9.594a71e8b58a from=translated src=- shape=255add49 vocab=b6917d00
-/
theorem single_eigen_pencil_mass_strict {s : ℕ} {h : Fin s → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ) (hh : Monotone h)
    (hrows : LastRowForm h C) (hlower : WasowSingleEigenBlocks.LowerBlocks C)
    (hN : IsNilpotent (C - α • 1))
    (hn : ∃ a b, a ≠ b ∧ WasowMultiShiftReduction.block C a b ≠ 0) :
    WasowPencilDescent.degreeMass (pencil C) <
      WasowPencilDescent.degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) := by
  obtain ⟨L, R, T, hLR, hRL, hT, hdiag, hoff, hlow, hniff⟩ :=
    WasowSingleEigenBlocks.exists_shift_diagonal_similarity C α hrows hlower hN
  have he : WasowPencilDescent.degreeMass (pencil T) =
      WasowPencilDescent.degreeMass (pencil C) := by
    rw [hT, degreeMass_similarity _ _ _ hLR hRL, degreeMass_sub_scalar]
  rw [← he]
  apply pencil_degreeMass_strict_drop hh
    (WasowSingleEigenBlocks.lastRowForm_of_blocks T hdiag hoff)
  · intro a b hab i j
    exact hlow (show OrderDual.toDual b < OrderDual.toDual a from hab)
  · intro a i j
    exact congrArg (fun A => A i j) (hdiag a)
  · obtain ⟨a, b, hab, hn⟩ := hn
    have htn := (hniff a b hab).mpr hn
    have he : ∃ i j, WasowMultiShiftReduction.block T a b i j ≠ 0 := by
      by_contra! hz
      apply htn
      apply Matrix.ext
      exact hz
    obtain ⟨i, j, hij⟩ := he
    have hi : i = Fin.last (h a) := by
      apply Fin.ext
      change i.val = h a
      by_contra hi
      have hil : i.val < h a := by omega
      exact hij (hoff a b hab i j hil)
    subst i
    exact ⟨a, b, hab, j, hij⟩

end WasowPencilSimilarity
