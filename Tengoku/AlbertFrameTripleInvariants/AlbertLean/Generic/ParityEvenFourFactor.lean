import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParityChartFiniteMover
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParityEvenMiddleFactor
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParityEvenConjugation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FiniteQuadraticRoots
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamilyFixedBranch
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorCoefficientMap
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairDephaseAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms fixedParityAut_linear_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms four_fixedParity_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_oneRoot_four_fixedParity` (it only prints; the queue checks the axioms of every declaration). -/

/-! Every legal source even action becomes four literal members of the fixed
parity rational family after one explicit quadratic field extension. -/
noncomputable section
namespace AlbertLean.Triality.ParityEvenFourFactor

open ExteriorSix CoordinateTensor StructuredCubic
open SourceEvenReflections SourceEvenAutomorphism SourceVectorPairDephase
open RationalEvenFamily RationalEvenFamilyFixedBranch
open RationalEvenFamilyInverse ParityChartMovingCenter ParityChartFiniteMover
open ParityEvenMiddleFactor ParityEvenConjugation
open AlbertLean.Generic.FiniteQuadraticRoots
open AlbertLean.Generic.SourceVectorCoefficientMap

universe u
variable {K : Type u} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/-- Reflection in the fixed parity vector preserves the `r` coordinate.-/
@[simp] theorem reflectV_parityVector_r (D : VCoord K) :
    (reflectV parityVector D).r = D.r := by
  simp [reflectV, parityVector]

/-- The fixed parity vector is defined over the prime field.-/
@[simp] theorem mapV_parityVector {L : Type*} [Field L] [CharZero L]
    (f : K →+* L) : mapV f parityVector = parityVector := by
  apply VCoord.ext
  · simp [mapV, parityVector]
  · simp [mapV, parityVector]
  · funext i
    fin_cases i <;> simp [mapV, parityVector, wBasis]

/-- The numeral-power curve commutes with extension of coefficients.-/
theorem map_curveOmega {L : Type*} [Field L] [CharZero L]
    (f : K →+* L) (t : K) :
    (fun i => f (curveOmega t i)) = curveOmega (f t) := by
  funext i
  fin_cases i <;> simp [curveOmega]

/-- The moving center is the same point after extension of coefficients.-/
@[simp] theorem mapV_movingCenter {L : Type*} [Field L] [CharZero L]
    (f : K →+* L) (t : K) :
    mapV f (movingCenter t) = movingCenter (f t) := by
  apply VCoord.ext
  · simp [mapV, movingCenter, center]
  · simp [mapV, movingCenter, center, pf_coordinate, curveOmega]
  · exact map_curveOmega f t

/-- A literal member of the existing eight-parameter fixed-parity family.-/
def fixedParityAut (D : VCoord K) (s : K)
    (hr : D.r ≠ 0) (hs : s ≠ 0) :=
  recoveryAutToSourceAut
    (familyAut parityVector (by simp) D.r D.omega s hr hs)

theorem fixedParityAut_linear_eq (D : VCoord K) (s : K)
    (hr : D.r ≠ 0) (hs : s ≠ 0) (hsq : s ^ 2 = nV D) :
    (fixedParityAut D s hr hs).linear =
      (sourceEvenAut parityVector D s (by simp)
        (by rw [← hsq]; exact pow_ne_zero 2 hs)
        (by simpa using hsq) hs).linear := by
  change (familyAut parityVector (by simp) D.r D.omega s hr hs).linear = _
  exact familyAut_linear_eq_fixed_center parityVector D s (by simp)
    (by rw [← hsq]; exact pow_ne_zero 2 hs) hr (by simpa using hsq) hs

set_option maxHeartbeats 1000000 in
/-- Same-field core: a unit-norm parity mover, a single root of `nV A`, and
the preserved signed product root give the four literal family factors.-/
theorem four_fixedParity_apply
    (A B c : VCoord K) (rho alpha beta : K)
    (hc : nV c = 1)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hr : rho ^ 2 = nV A * nV B) (hr0 : rho ≠ 0)
    (ha : alpha ^ 2 = nV A) (ha0 : alpha ≠ 0)
    (hb : beta ^ 2 = nV B) (hb0 : beta ≠ 0)
    (hab : alpha * beta = rho)
    (hcr : c.r ≠ 0)
    (hAr : (evenV parityVector c A).r ≠ 0)
    (hBr : (evenV parityVector c B).r ≠ 0)
    (x : JCoord K) :
    let A' := evenV parityVector c A
    let B' := evenV parityVector c B
    let D0 := reflectV parityVector c
    let D1 := reflectV parityVector A'
    let F0 := fixedParityAut D0 (-1) (by simpa [D0] using hcr) (by norm_num)
    let F1 := fixedParityAut D1 (-alpha) (by simpa [D1] using hAr)
      (neg_ne_zero.mpr ha0)
    let F2 := fixedParityAut B' beta hBr hb0
    let F3 := fixedParityAut c 1 hcr (by norm_num)
    (sourceEvenAut A B rho hA hB hr hr0).linear x =
      F0.linear (F1.linear (F2.linear (F3.linear x))) := by
  intro A' B' D0 D1 F0 F1 F2 F3
  have he : nV (parityVector : VCoord K) = 1 := nV_parityVector
  have he0 : nV (parityVector : VCoord K) ≠ 0 := by simp
  have hc0 : nV c ≠ 0 := by rw [hc]; exact one_ne_zero
  have hA'n : nV A' ≠ 0 := by simpa [A', nV_evenV _ _ _ he0 hc0] using hA
  have hB'n : nV B' ≠ 0 := by simpa [B', nV_evenV _ _ _ he0 hc0] using hB
  have ha' : alpha ^ 2 = nV A' := by simpa [A', nV_evenV _ _ _ he0 hc0] using ha
  have hb' : beta ^ 2 = nV B' := by simpa [B', nV_evenV _ _ _ he0 hc0] using hb
  have hD0r : D0.r ≠ 0 := by simpa [D0] using hcr
  have hD1r : D1.r ≠ 0 := by simpa [D1] using hAr
  have hconj := sourceEvenAut_conjugate_apply parityVector c A B rho he hc
    hA hB hr hr0 x
  dsimp only at hconj
  rw [← hconj]
  have hmid := sourceEvenAut_middle_apply parityVector A' B' alpha beta rho he
    hA'n hB'n ha' hb' hab ha0 hb0 hr0
      ((sourceEvenAut parityVector c 1 (by simp) hc0
        (by simpa [hc]) (by norm_num)).linear x)
  dsimp only at hmid
  rw [← hmid]
  have hF0 (y : JCoord K) :
      F0.linear y =
        (sourceEvenAut parityVector D0 (-1) (by simp)
          (by simpa [D0, nV_reflectV _ _ he0] using hc0)
          (by simp [D0, nV_reflectV _ _ he0, hc]) (by norm_num)).linear y :=
    congrArg (fun L => L y) (fixedParityAut_linear_eq D0 (-1) hD0r
      (by norm_num) (by simp [D0, nV_reflectV _ _ he0, hc]))
  have hF1 (y : JCoord K) :
      F1.linear y =
        (sourceEvenAut parityVector D1 (-alpha) (by simp)
          (by simpa [D1, nV_reflectV _ _ he0] using hA'n)
          (by simpa [D1, nV_reflectV _ _ he0] using ha')
          (neg_ne_zero.mpr ha0)).linear y :=
    congrArg (fun L => L y) (fixedParityAut_linear_eq D1 (-alpha) hD1r
      (neg_ne_zero.mpr ha0) (by simpa [D1, nV_reflectV _ _ he0] using ha'))
  have hF2 (y : JCoord K) :
      F2.linear y =
        (sourceEvenAut parityVector B' beta (by simp) hB'n
          (by simpa using hb') hb0).linear y :=
    congrArg (fun L => L y) (fixedParityAut_linear_eq B' beta hBr hb0 hb')
  have hF3 (y : JCoord K) :
      F3.linear y =
        (sourceEvenAut parityVector c 1 (by simp) hc0
          (by simpa [hc]) (by norm_num)).linear y :=
    congrArg (fun L => L y) (fixedParityAut_linear_eq c 1 hcr
      (by norm_num) (by simpa [hc]))
  rw [← hF0, ← hF1, ← hF2, ← hF3]

structure FourFixedParityFactorization
    (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hr : rho ^ 2 = nV A * nV B) (hr0 : rho ≠ 0) where
  r : Fin 4 → K
  w : Fin 4 → ExteriorSix.W K
  s : Fin 4 → K
  r_ne : ∀ i, r i ≠ 0
  s_ne : ∀ i, s i ≠ 0
  factor : Fin 4 → AlbertLean.Generic.ResidualAction.SourceAut (K := K)
  factor_eq : ∀ i, factor i =
    recoveryAutToSourceAut
      (familyAut parityVector (by simp) (r i) (w i) (s i) (r_ne i) (s_ne i))
  action : ∀ x : JCoord K,
    (sourceEvenAut A B rho hA hB hr hr0).linear x =
      (factor 0).linear ((factor 1).linear
        ((factor 2).linear ((factor 3).linear x)))

/- Keep projections opaque while packaging the certified family word.
The only representation equality below explicitly unfolds this wrapper. -/
attribute [local irreducible] fixedParityAut

/-- Package the same-field four-factor identity before specializing to the
concrete carrier of a one-root extension.-/
theorem four_fixedParity_factorization
    (A B c : VCoord K) (rho alpha beta : K)
    (hc : nV c = 1)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hr : rho ^ 2 = nV A * nV B) (hr0 : rho ≠ 0)
    (ha : alpha ^ 2 = nV A) (ha0 : alpha ≠ 0)
    (hb : beta ^ 2 = nV B) (hb0 : beta ≠ 0)
    (hab : alpha * beta = rho)
    (hcr : c.r ≠ 0)
    (hAr : (evenV parityVector c A).r ≠ 0)
    (hBr : (evenV parityVector c B).r ≠ 0) :
    Nonempty (FourFixedParityFactorization A B rho hA hB hr hr0) := by
  let A' := evenV parityVector c A
  let B' := evenV parityVector c B
  let D : Fin 4 → VCoord K := ![
    reflectV parityVector c, reflectV parityVector A', B', c]
  let s : Fin 4 → K := ![-1, -alpha, beta, 1]
  have hDr : ∀ i, (D i).r ≠ 0 := by
    intro i
    fin_cases i <;> simp [D, A', B', hcr, hAr, hBr]
  have hs : ∀ i, s i ≠ 0 := by
    intro i
    fin_cases i <;> simp [s, ha0, hb0]
  let F := fun i => fixedParityAut (D i) (s i) (hDr i) (hs i)
  refine ⟨{
    r := fun i => (D i).r
    w := fun i => (D i).omega
    s := s
    r_ne := hDr
    s_ne := hs
    factor := F
    factor_eq := by
      intro i
      dsimp only [F]
      unfold fixedParityAut
      rfl

    action := ?_ }⟩
  intro x
  have hD0 : (reflectV parityVector c).r ≠ 0 := by simpa using hcr
  have hD1 : (reflectV parityVector A').r ≠ 0 := by simpa [A'] using hAr
  have hm1 : (-1 : K) ≠ 0 := by norm_num
  have hma : -alpha ≠ 0 := neg_ne_zero.mpr ha0
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  let G0 := fixedParityAut (reflectV parityVector c) (-1) hD0 hm1
  let G1 := fixedParityAut (reflectV parityVector A') (-alpha) hD1 hma
  let G2 := fixedParityAut B' beta (by simpa [B'] using hBr) hb0
  let G3 := fixedParityAut c 1 hcr h1
  have hfour :
      (sourceEvenAut A B rho hA hB hr hr0).linear x =
        G0.linear (G1.linear (G2.linear (G3.linear x))) := by
    simpa only [G0, G1, G2, G3, A', B'] using
      four_fixedParity_apply A B c rho alpha beta hc hA hB hr hr0
        ha ha0 hb hb0 hab hcr hAr hBr x
  have hF0 : F 0 = G0 := by dsimp [F, D, s, G0]
  have hF1 : F 1 = G1 := by dsimp [F, D, s, G1, A']
  have hF2 : F 2 = G2 := by dsimp [F, D, s, G2, B']
  have hF3 : F 3 = G3 := by dsimp [F, D, s, G3]
  calc
    _ = G0.linear (G1.linear (G2.linear (G3.linear x))) := hfour
    _ = (F 0).linear (G1.linear (G2.linear (G3.linear x))) := by rw [hF0]
    _ = (F 0).linear ((F 1).linear (G2.linear (G3.linear x))) := by rw [hF1]
    _ = (F 0).linear ((F 1).linear ((F 2).linear (G3.linear x))) := by rw [hF2]
    _ = (F 0).linear ((F 1).linear ((F 2).linear ((F 3).linear x))) := by rw [hF3]

/-- Primary A2 endpoint. It returns four genuine fixed-parity family members
over the explicit one-root field, with no choice term in the result surface.-/
theorem exists_oneRoot_four_fixedParity
    (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hr : rho ^ 2 = nV A * nV B) (hr0 : rho ≠ 0) :
    ∃ R : OneRootField K (nV A),
      ∃ _ : CharZero R.Carrier,
      Nonempty (FourFixedParityFactorization (mapV R.embedding A) (mapV R.embedding B)
        (R.embedding rho) (by simpa using R.embedding.injective.ne_iff.mpr hA)
        (by simpa using R.embedding.injective.ne_iff.mpr hB)
        (by simpa using congrArg R.embedding hr)
        (by simpa only [map_zero] using R.embedding.injective.ne_iff.mpr hr0)) := by
  obtain ⟨t, hAt, hBt⟩ := exists_fin15_move_centers A B hA hB
  obtain ⟨R⟩ := oneRootField_nonempty K (nV A)
  letI : CharZero R.Carrier := charZero_of_embedding R.embedding
  let Ae := mapV R.embedding A
  let Be := mapV R.embedding B
  let c := movingCenter (R.embedding (t.val : K))
  let A' := evenV parityVector c Ae
  let B' := evenV parityVector c Be
  let alpha := R.root
  let beta := R.embedding rho / alpha
  have ha : alpha ^ 2 = nV Ae := by simpa [Ae] using R.root_sq
  have ha0 : alpha ≠ 0 := by
    intro hz
    apply R.embedding.injective.ne_iff.mpr hA
    rw [← R.root_sq, show R.root = alpha from rfl, hz]
    norm_num
  have hab : alpha * beta = R.embedding rho := by
    dsimp [beta]
    field_simp [ha0]
  have hb : beta ^ 2 = nV Be := by
    dsimp [beta]
    rw [div_pow, show alpha ^ 2 = R.embedding (nV A) from R.root_sq,
      ← map_pow, hr, map_mul]
    rw [show nV Be = R.embedding (nV B) by simp [Be]]
    have hEA : R.embedding (nV A) ≠ 0 := by
      simpa only [map_zero] using R.embedding.injective.ne_iff.mpr hA
    calc
      R.embedding (nV A) * R.embedding (nV B) / R.embedding (nV A) =
          R.embedding (nV B) * R.embedding (nV A) / R.embedding (nV A) := by
            rw [mul_comm]
      _ = R.embedding (nV B) := mul_div_cancel_right₀ _ hEA
  have hb0 : beta ≠ 0 := by
    apply div_ne_zero
    · simpa only [map_zero] using R.embedding.injective.ne_iff.mpr hr0
    · exact ha0
  have hmc : mapV R.embedding (movingCenter (t.val : K)) = c := by
    rw [mapV_movingCenter]
  have hAr : A'.r ≠ 0 := by
    have hmap :
        mapV R.embedding (evenV parityVector (movingCenter (t.val : K)) A) = A' := by
      rw [mapV_evenV, mapV_parityVector, hmc]
    rw [← hmap]
    change R.embedding ((evenV parityVector (movingCenter (t.val : K)) A).r) ≠ 0
    simpa only [map_zero] using R.embedding.injective.ne_iff.mpr hAt
  have hBr : B'.r ≠ 0 := by
    have hmap :
        mapV R.embedding (evenV parityVector (movingCenter (t.val : K)) B) = B' := by
      rw [mapV_evenV, mapV_parityVector, hmc]
    rw [← hmap]
    change R.embedding ((evenV parityVector (movingCenter (t.val : K)) B).r) ≠ 0
    simpa only [map_zero] using R.embedding.injective.ne_iff.mpr hBt
  have hAe : nV Ae ≠ 0 := by simpa [Ae] using R.embedding.injective.ne_iff.mpr hA
  have hBe : nV Be ≠ 0 := by simpa [Be] using R.embedding.injective.ne_iff.mpr hB
  have hre : (R.embedding rho) ^ 2 = nV Ae * nV Be := by
    simpa [Ae, Be] using congrArg R.embedding hr
  have hre0 : R.embedding rho ≠ 0 := by
    simpa only [map_zero] using R.embedding.injective.ne_iff.mpr hr0
  have hcR : c.r ≠ 0 := by simp [c]
  refine ⟨R, inferInstance, ?_⟩
  exact four_fixedParity_factorization Ae Be c (R.embedding rho) alpha beta
    (movingCenter_norm _) hAe hBe hre hre0 ha ha0 hb hb0 hab hcR hAr hBr

end AlbertLean.Triality.ParityEvenFourFactor
