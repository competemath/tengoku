import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Module
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSelfAdjointCarrier
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionProjectorBlockBridge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticActualProjectorExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms omega_alternating` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms omega_left_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms omega_right_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixAction_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixAction_add` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms carrier_action_selfAdjoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms carrier_projector_action_idempotent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms carrier_frame_action_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms carrier_action_ne_zero_of_trace_one` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.SymplecticTransvection
open AlbertLean.Generic.SymplecticProjectorFrame

universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev Vec6 (K : Type u) := Ix6 → K

def omegaFun (x y : Vec6 K) : K :=
  ∑ i : Fin 3, (x (Sum.inl i) * y (Sum.inr i) -
    x (Sum.inr i) * y (Sum.inl i))

/-- The literal column-vector form `xᵀJy` for
`J=[[0,I],[-I,0]]`.-/
def omega : BilinForm (K := K) (V := Vec6 K) where
  toFun x :=
    { toFun := omegaFun x
      map_add' := by
        intro y z
        simp [omegaFun, Fin.sum_univ_succ]
        ring
      map_smul' := by
        intro t y
        simp [omegaFun, smul_eq_mul, Fin.sum_univ_succ]
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp [omegaFun, Fin.sum_univ_succ]
    ring
  map_smul' := by
    intro t x
    apply LinearMap.ext
    intro y
    simp [omegaFun, smul_eq_mul, Fin.sum_univ_succ]
    ring

/--
@isnad1 id=eq.0h2v.s9.b50f156a3deb from=translated src=- shape=cb72c833 vocab=d40fdc0a
-/
theorem omega_alternating (x : Vec6 K) : (omega (K := K)) x x = 0 := by
  change omegaFun x x = 0
  simp [omegaFun, Fin.sum_univ_succ]
  ring

def basisVector (i : Ix6) : Vec6 K := Pi.single i 1

/--
@isnad1 id=eq.0h2v.s9.e0683601946c from=translated src=- shape=29bcc378 vocab=17a68672
-/
theorem omega_basis_pair (i : Fin 3) :
    (omega (K := K)) (basisVector (Sum.inl i))
      (basisVector (Sum.inr i)) = 1 := by
  classical
  change omegaFun (basisVector (Sum.inl i)) (basisVector (Sum.inr i)) = 1
  fin_cases i <;> simp [omegaFun, basisVector, Fin.sum_univ_succ]

/--
@isnad1 id=isleftno.0h1v.s6.2708c73c53e5 from=translated src=- shape=5b894d8a vocab=dc7a1879
-/
theorem omega_left_nondegenerate : IsLeftNondegenerate (omega (K := K)) := by
  classical
  intro x hx
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hex
  rcases i with i | i
  · refine ⟨basisVector (Sum.inr i), ?_⟩
    change omegaFun (basisVector (Sum.inr i)) x ≠ 0
    fin_cases i <;>
      simpa [omegaFun, basisVector, Fin.sum_univ_succ] using neg_ne_zero.mpr hi
  · refine ⟨basisVector (Sum.inl i), ?_⟩
    change omegaFun (basisVector (Sum.inl i)) x ≠ 0
    fin_cases i <;> simpa [omegaFun, basisVector, Fin.sum_univ_succ] using hi

/--
@isnad1 id=isrightn.0h1v.s6.281e26b7599a from=translated src=- shape=5b894d8a vocab=966fd2a3
-/
theorem omega_right_nondegenerate : IsRightNondegenerate (omega (K := K)) := by
  classical
  intro x hx
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hex
  rcases i with i | i
  · refine ⟨basisVector (Sum.inr i), ?_⟩
    change omegaFun x (basisVector (Sum.inr i)) ≠ 0
    fin_cases i <;> simpa [omegaFun, basisVector, Fin.sum_univ_succ] using hi
  · refine ⟨basisVector (Sum.inl i), ?_⟩
    change omegaFun x (basisVector (Sum.inl i)) ≠ 0
    fin_cases i <;>
      simpa [omegaFun, basisVector, Fin.sum_univ_succ] using neg_ne_zero.mpr hi

/-- Left multiplication on literal grouped columns.-/
def matrixAction (P : Mat6 K) : Vec6 K →ₗ[K] Vec6 K where
  toFun x i := ∑ j, P i j * x j
  map_add' := by
    intro x y
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro t x
    funext i
    simp [smul_eq_mul, Fintype.sum_sum_type, Fin.sum_univ_succ]
    ring

/--
@isnad1 id=eq.0h4v.s8.c9b608c46908 from=translated src=- shape=bb2d394a vocab=0bac50ee
-/
@[simp] theorem matrixAction_apply (P : Mat6 K) (x : Vec6 K) (i : Ix6) :
    matrixAction P x i = ∑ j, P i j * x j := rfl

/--
@isnad1 id=eq.0h3v.s8.62baee6574a7 from=translated src=- shape=a2e483d5 vocab=3c87b04e
-/
theorem matrixAction_mul (P Q : Mat6 K) :
    matrixAction (P * Q) = (matrixAction P).comp (matrixAction Q) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [matrixAction_apply, LinearMap.comp_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/--
@isnad1 id=eq.0h3v.s9.e36fcf143b85 from=translated src=- shape=46d0c4e8 vocab=97b53b79
-/
theorem matrixAction_add (P Q : Mat6 K) :
    matrixAction (P + Q) = matrixAction P + matrixAction Q := by
  apply LinearMap.ext
  intro x
  funext i
  simp [matrixAction, Finset.sum_add_distrib, add_mul]

/--
@isnad1 id=eq.0h1v.s8.8a62390bdec9 from=translated src=- shape=1155a53a vocab=ab8934f8
-/
theorem matrixAction_one : matrixAction (1 : Mat6 K) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  classical
  simp [matrixAction, Matrix.one_apply]

/--
@isnad1 id=eq.0h1v.s9.e5b468f1b2f0 from=translated src=- shape=1971353d vocab=77c4d74c
-/
theorem matrixAction_zero : matrixAction (0 : Mat6 K) = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  simp [matrixAction]

/--
@isnad1 id=injectiv.0h1v.s7.1bc6c1c14a6c from=translated src=- shape=0068229d vocab=3459daa2
-/
theorem matrixAction_injective : Function.Injective (matrixAction (K := K)) := by
  intro P Q h
  ext i j
  have hcol := LinearMap.congr_fun h (basisVector j)
  have hij := congrFun hcol i
  rcases j with j | j <;> fin_cases j <;>
    simpa [matrixAction, basisVector, Fintype.sum_sum_type,
      Fin.sum_univ_succ] using hij

/-- The matrix equation `PᵀJ=JP` is exactly self-adjointness of left
multiplication for the literal form.
@isnad1 id=isselfad.0h2v.s8.b56a3f2d4527 from=translated src=- shape=6f6a8b9d vocab=29933eae
-/
theorem carrier_action_selfAdjoint (P : Carrier K) :
    SymplecticProjectorFrame.IsSelfAdjoint (omega (K := K))
      (matrixAction (K := K) (P : Mat6 K)) := by
  obtain ⟨a, u, v, hP⟩ := exists_grouped P
  intro x y
  rw [hP]
  simp [omega, omegaFun, matrixAction, grouped, Fintype.sum_sum_type,
    Fin.sum_univ_succ, ScalarFibre.hat]
  ring

/--
@isnad1 id=isidempo.1h2v.s10.caca4e1975af from=translated src=- shape=96c0edac vocab=b89d667a
-/
theorem carrier_projector_action_idempotent (P : Carrier K)
    (hP : (P : Mat6 K) * P = P) :
    SymplecticProjectorFrame.IsIdempotent
      (matrixAction (K := K) (P : Mat6 K)) := by
  change (matrixAction (K := K) (P : Mat6 K)).comp
    (matrixAction (K := K) (P : Mat6 K)) = matrixAction (K := K) (P : Mat6 K)
  rw [← matrixAction_mul]
  exact congrArg (matrixAction (K := K)) hP

/--
@isnad1 id=eq.1h2v.s11.f129eac31ce6 from=translated src=- shape=dfef0076 vocab=d81c0914
-/
theorem carrier_frame_action_sum
    (P : Fin 3 → Carrier K)
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    matrixAction (K := K) (P 0 : Mat6 K) +
        matrixAction (K := K) (P 1 : Mat6 K) +
        matrixAction (K := K) (P 2 : Mat6 K) =
      LinearMap.id := by
  have h := congrArg (matrixAction (K := K)) hsum
  rw [matrixAction_add, matrixAction_add, matrixAction_one] at h
  exact h

/-- Half-trace one supplies the actual nonzero-map premise used by projector
extraction.
@isnad1 id=ne.1h2v.s10.3f1e8f0eaafd from=translated src=- shape=173078fe vocab=50fea280
-/
theorem carrier_action_ne_zero_of_trace_one (P : Carrier K)
    (htrace : jordanTrace (K := K) (P : Mat6 K) = 1) :
    matrixAction (K := K) (P : Mat6 K) ≠ 0 := by
  intro hzero
  have hPzero : (P : Mat6 K) = 0 := by
    apply matrixAction_injective
    rw [hzero, matrixAction_zero]
  rw [hPzero] at htrace
  simp [jordanTrace, Matrix.trace] at htrace

end AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
