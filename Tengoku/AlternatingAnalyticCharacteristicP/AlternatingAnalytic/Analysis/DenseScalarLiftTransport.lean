import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseScalarRestriction
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.LiftCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of bounded lifts along a dense scalar inclusion

Let `K` be dense in `L`. A bounded lift of `Q` over `K` transports to a bounded lift
over `L` with the same norm, through the scalar-restriction isometries of
`DenseScalarRestriction`. With the bounded-lift criterion, failure of analyticity
over `L` implies failure over `K`. This is the lift part of Lemma D.11.
-/

noncomputable section

namespace AlternatingAnalytic

open LiftCriterion

section IsometricConjugation

variable {L A A' B B' : Type*} [NontriviallyNormedField L]
  [NormedAddCommGroup A] [NormedSpace L A]
  [NormedAddCommGroup A'] [NormedSpace L A']
  [NormedAddCommGroup B] [NormedSpace L B]
  [NormedAddCommGroup B'] [NormedSpace L B']

/-- Conjugation by linear isometric equivalences, as an isometry of spaces of
continuous linear maps.-/
def continuousLinearMapCongrIsometry (eA : A ≃ₗᵢ[L] A') (eB : B ≃ₗᵢ[L] B') :
    (A →L[L] B) ≃ₗᵢ[L] (A' →L[L] B') where
  toLinearEquiv := (eA.toContinuousLinearEquiv.arrowCongr eB.toContinuousLinearEquiv).toLinearEquiv
  norm_map' f := by
    let T := eA.toContinuousLinearEquiv.arrowCongr eB.toContinuousLinearEquiv f
    change ‖T‖ = ‖f‖
    apply le_antisymm
    · apply T.opNorm_le_bound (norm_nonneg f)
      intro x
      change ‖eB (f (eA.symm x))‖ ≤ ‖f‖ * ‖x‖
      simpa using f.le_opNorm (eA.symm x)
    · apply f.opNorm_le_bound (norm_nonneg T)
      intro x
      have h := T.le_opNorm (eA x)
      change ‖eB (f (eA.symm (eA x)))‖ ≤ ‖T‖ * ‖eA x‖ at h
      simpa using h

/--
@isnad1 id=eq.0h9v.s11.9940fd4947bf from=translated src=- shape=cccf77c2 vocab=87a64e38
-/
@[simp]
theorem continuousLinearMapCongrIsometry_apply
    (eA : A ≃ₗᵢ[L] A') (eB : B ≃ₗᵢ[L] B') (f : A →L[L] B) (x : A') :
    continuousLinearMapCongrIsometry eA eB f x = eB (f (eA.symm x)) := rfl

end IsometricConjugation

section MultilinearTransportNorm

variable {K L A A' B B' : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L]
  [NormedAddCommGroup A] [NormedSpace K A] [NormedSpace L A] [IsScalarTower K L A]
  [NormedAddCommGroup A'] [NormedSpace L A']
  [NormedAddCommGroup B] [NormedSpace K B] [NormedSpace L B] [IsScalarTower K L B]
  [NormedAddCommGroup B'] [NormedSpace L B']

/-- Scalar extension and isometric changes of domain and codomain preserve the norm
of a continuous multilinear map.
@isnad1 id=eq.1h10v.s10.bce5cb32db0a from=translated src=- shape=e63a59d7 vocab=9ad08acb
-/
theorem norm_denseScalarMultilinear_congr (hd : DenseRange (algebraMap K L)) {n : ℕ}
    (eA : A ≃ₗᵢ[L] A') (eB : B ≃ₗᵢ[L] B') (P : A [×n]→L[K] B) :
    ‖eB.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap
      ((denseScalarMultilinearExtension hd P).compContinuousLinearMap
        (fun _ => eA.symm.toLinearIsometry.toContinuousLinearMap))‖ = ‖P‖ := by
  rw [LinearIsometry.norm_compContinuousMultilinearMap]
  exact ((denseScalarMultilinearExtension hd P).norm_compContinuous_linearIsometryEquiv
    (fun _ => eA.symm)).trans (norm_denseScalarMultilinearExtension hd P)

end MultilinearTransportNorm

/-- The operator norm on the lift space, stated directly to avoid an instance
ambiguity through the alternating-map norm.-/
local instance liftSpaceNorm {R A B C : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup A] [NormedSpace R A]
    [NormedAddCommGroup B] [NormedSpace R B]
    [NormedAddCommGroup C] [NormedSpace R C] {k n : ℕ} :
    Norm (ContinuousMultilinearMap R (fun _ : Fin n => A →L[R] B)
      ((B [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := R) (E := fun _ : Fin n => A →L[R] B)
    (G := (B [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))

section DenseScalars

variable {K L E E' F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace L E] [IsScalarTower K L E]
  [NormedAddCommGroup E'] [NormedSpace K E'] [NormedSpace L E'] [IsScalarTower K L E']
  [NormedAddCommGroup F] [NormedSpace K F] [NormedSpace L F] [IsScalarTower K L F]

/-- Isometric identification of the target spaces of `Q` over `K` and over `L`.-/
def denseScalarQTargetEquiv (hd : DenseRange (algebraMap K L)) (k : ℕ) :
    ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) ≃ₗᵢ[L]
      ((E' [⋀^Fin k]→L[L] F) →L[L] (E [⋀^Fin k]→L[L] F)) :=
  (denseScalarLinearEquiv hd).trans
    (continuousLinearMapCongrIsometry (denseScalarAlternatingEquiv hd)
      (denseScalarAlternatingEquiv hd))

/--
@isnad1 id=eq.1h9v.s14.4287413d251d from=translated src=- shape=cd0bdcf4 vocab=e59e6ffe
-/
@[simp]
theorem denseScalarQTargetEquiv_apply (hd : DenseRange (algebraMap K L)) (k : ℕ)
    (T : (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))
    (m : E' [⋀^Fin k]→L[L] F) (x : Fin k → E) :
    denseScalarQTargetEquiv (E := E) (E' := E') (F := F) hd k T m x = T (m.restrictScalars K) x := rfl

/-- The identification carries `Q` over `K` to `Q` over `L`.
@isnad1 id=eq.1h7v.s13.8236f161ff8f from=translated src=- shape=5ed996ed vocab=afeebac9
-/
theorem denseScalarQTargetEquiv_Q (hd : DenseRange (algebraMap K L)) (k : ℕ)
    (f : E →L[K] E') :
    denseScalarQTargetEquiv (E := E) (E' := E') (F := F) hd k (Q K (Fin k) E E' F f) =
      Q L (Fin k) E E' F (denseScalarLinearEquiv hd f) := by
  ext m x
  rfl

/-- Transport of a continuous `n`-linear map between the source and target spaces
of `Q` from `K` to `L`.-/
def denseScalarLiftTransport (hd : DenseRange (algebraMap K L)) {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) :
    ContinuousMultilinearMap L (fun _ : Fin n => E →L[L] E')
      ((E' [⋀^Fin k]→L[L] F) →L[L] (E [⋀^Fin k]→L[L] F)) :=
  (denseScalarQTargetEquiv (E := E) (E' := E') (F := F) hd k).toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap
    ((denseScalarMultilinearExtension (E := E →L[K] E')
      (F := (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) hd P).compContinuousLinearMap
      (fun _ => (denseScalarLinearEquiv (E := E) (F := E') hd).symm.toLinearIsometry.toContinuousLinearMap))

/--
@isnad1 id=eq.1h11v.s14.78b08c279781 from=translated src=- shape=52b5a277 vocab=cb2ae82d
-/
@[simp]
theorem denseScalarLiftTransport_apply (hd : DenseRange (algebraMap K L)) {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))
    (f : Fin n → E →L[L] E') (m : E' [⋀^Fin k]→L[L] F) (x : Fin k → E) :
    denseScalarLiftTransport hd P f m x =
      P (fun j => (f j).restrictScalars K) (m.restrictScalars K) x := rfl

set_option maxHeartbeats 800000 in
/-- Transport preserves the operator norm.
@isnad1 id=eq.1h8v.s13.705855befff6 from=translated src=- shape=c6f7b940 vocab=90a95da7
-/
theorem norm_denseScalarLiftTransport (hd : DenseRange (algebraMap K L)) {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) :
    ‖denseScalarLiftTransport hd P‖ = ‖P‖ := by
  let A := denseScalarLinearEquiv (E := E) (F := E') hd
  let B := denseScalarQTargetEquiv (E := E) (E' := E') (F := F) hd k
  have hA (f : E →L[K] E') : (A f).restrictScalars K = f := by
    ext x
    rfl
  change sInf {c : ℝ | 0 ≤ c ∧ ∀ fs : Fin n → E →L[L] E',
      ‖denseScalarLiftTransport hd P fs‖ ≤ c * ∏ i, ‖fs i‖} =
    sInf {c : ℝ | 0 ≤ c ∧ ∀ fs : Fin n → E →L[K] E',
      ‖P fs‖ ≤ c * ∏ i, ‖fs i‖}
  congr 1
  ext c
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun fs => ?_⟩
    have hh := h (fun i => A (fs i))
    change ‖B (P (fun i => (A (fs i)).restrictScalars K))‖ ≤
      c * ∏ i, ‖A (fs i)‖ at hh
    simpa only [B.norm_map, A.norm_map, hA] using hh
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun fs => ?_⟩
    have hh := h (fun i => (fs i).restrictScalars K)
    change ‖B (P (fun i => (fs i).restrictScalars K))‖ ≤ c * ∏ i, ‖fs i‖
    rw [B.norm_map]
    simpa only [ContinuousLinearMap.norm_restrictScalars] using hh

/-- The transport of a lift of `Q` over `K` is a lift of `Q` over `L`.
@isnad1 id=eq.2h9v.s14.a0793504bb6a from=translated src=- shape=05e66c09 vocab=0e526f0a
-/
theorem denseScalarLiftTransport_diagonal (hd : DenseRange (algebraMap K L)) {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))
    (hP : ∀ f, P (fun _ => f) = Q K (Fin k) E E' F f) (f : E →L[L] E') :
    denseScalarLiftTransport hd P (fun _ => f) = Q L (Fin k) E E' F f := by
  ext m x
  rw [denseScalarLiftTransport_apply, hP]
  rfl

/-- A bounded lift over `K` gives one over `L`, on the same spaces and in the same degree.
@isnad1 id=hasbound.2h6v.s9.e4eccd8a6156 from=translated src=- shape=7f8f2561 vocab=a666fa5f
-/
theorem hasBoundedLift_fin_of_denseScalars (hd : DenseRange (algebraMap K L)) (k : ℕ)
    (h : HasBoundedLift K (Fin k) E E' F) : HasBoundedLift L (Fin k) E E' F := by
  obtain ⟨P, hP⟩ := h
  exact ⟨denseScalarLiftTransport hd P, denseScalarLiftTransport_diagonal hd P hP⟩

end DenseScalars

section Completion

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace (UniformSpace.Completion K) E]
  [IsScalarTower K (UniformSpace.Completion K) E]
  [NormedAddCommGroup E'] [NormedSpace K E'] [NormedSpace (UniformSpace.Completion K) E']
  [IsScalarTower K (UniformSpace.Completion K) E']
  [NormedAddCommGroup F] [NormedSpace K F] [NormedSpace (UniformSpace.Completion K) F]
  [IsScalarTower K (UniformSpace.Completion K) F]

/-- Transport of lifts to the completion of `K`.-/
def completionScalarLiftTransport {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) :
    ContinuousMultilinearMap (UniformSpace.Completion K)
      (fun _ : Fin n => E →L[UniformSpace.Completion K] E')
      ((E' [⋀^Fin k]→L[UniformSpace.Completion K] F) →L[UniformSpace.Completion K]
        (E [⋀^Fin k]→L[UniformSpace.Completion K] F)) :=
  denseScalarLiftTransport (denseRange_algebraMap_completion K) P

/--
@isnad1 id=eq.0h7v.s13.e8d74f7d15df from=translated src=- shape=0e453426 vocab=4b3af485
-/
theorem norm_completionScalarLiftTransport {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) :
    ‖completionScalarLiftTransport P‖ = ‖P‖ :=
  norm_denseScalarLiftTransport (denseRange_algebraMap_completion K) P

/--
@isnad1 id=eq.1h8v.s15.0945fe6a9dd7 from=translated src=- shape=3d5be99d vocab=134c4fd1
-/
theorem completionScalarLiftTransport_diagonal {k n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))
    (hP : ∀ f, P (fun _ => f) = Q K (Fin k) E E' F f)
    (f : E →L[UniformSpace.Completion K] E') :
    completionScalarLiftTransport P (fun _ => f) =
      Q (UniformSpace.Completion K) (Fin k) E E' F f :=
  denseScalarLiftTransport_diagonal (denseRange_algebraMap_completion K) P hP f

end Completion

end AlternatingAnalytic
