import Tengoku.Nlalib.NLAlib.Matrix.Functions.PositiveConeEigenvector
import Tengoku.Nlalib.NLAlib.Matrix.Functions.PositiveConeNeumann

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Equivalent Frobenius stability tests for symmetric PSD-cone maps -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero PSD matrix pairs strictly positively with every PD matrix.
@isnad1 id=lt.3h3v.s6.0a7d8938692f from=translated src=- shape=2d844da6 vocab=c0069c38
-/
theorem frobInner_pos_of_posSemidef_posDef {P Y : Matrix n n ℂ}
    (hP : P.PosSemidef) (hP0 : P≠0) (hY : Y.PosDef) : 0 < frobInner P Y := by
  have hn := frobInner_nonneg_of_posSemidef hP hY.posSemidef
  apply lt_of_le_of_ne hn
  intro hz
  have hz' : (P*Y).trace=0 := by
    apply Complex.ext
    · have he : frobInner P Y = 0 := hz.symm
      rw [frobInner_eq_trace,hP.isHermitian.eq] at he
      exact he
    · exact (Complex.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hP hY.posSemidef)).2.symm
  have hPY := (trace_mul_eq_zero_iff_of_posSemidef hP hY.posSemidef).mp hz'
  apply hP0
  calc
    P = P*(Y*Y⁻¹) := by rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)]; simp
    _ = 0 := by rw [← Matrix.mul_assoc,hPY,Matrix.zero_mul]

/-- Norm below one makes `I-L` strictly positive for the Hilbert pairing.
@isnad1 id=lt.2h3v.s8.ed1d2d94be30 from=translated src=- shape=7b37c2ad vocab=7dcf1f6d
-/
theorem inner_sub_map_pos_of_norm_lt_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E→L[ℝ]E) (hL : ‖L‖<1) {x : E} (hx : x≠0) :
    0 < inner ℝ x (x-L x) := by
  have hb : inner ℝ x (L x) ≤ ‖L‖*‖x‖^2 := by
    calc
      _ ≤ ‖x‖*‖L x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖*(‖L‖*‖x‖) := mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  have hp : 0<‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  nlinarith

/-- For symmetric PSD-cone maps the strict Hilbert test is precisely the
Frobenius operator norm bound. Source (F22); cone positivity alone is used.
@isnad1 id=iff.2h2v.s9.bc5f94c865da from=translated src=- shape=1e5dc128 vocab=4e3413a5
-/
theorem inner_sub_map_pos_iff_norm_lt_one [Nonempty n]
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n) (hsym : L.IsSymmetric)
    (hcone : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L x)).PosSemidef) :
    (∀ x≠0, 0 < inner ℝ x (x-L x)) ↔ ‖L‖<1 := by
  constructor
  · intro h
    obtain ⟨x,hx,_,heig⟩ := exists_posSemidef_norm_eigenvector L hsym hcone
    have hp := h x hx
    rw [heig,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq] at hp
    have hn : 0<‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    nlinarith
  · exact fun h x hx => inner_sub_map_pos_of_norm_lt_one L h hx

/-- A strict PSD supersolution forces the norm below one.
@isnad1 id=lt.4h3v.s9.82cdf69d0999 from=translated src=- shape=45bd93f7 vocab=9ed16bce
-/
theorem norm_lt_one_of_posDef_supersolution [Nonempty n]
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n) (hsym : L.IsSymmetric)
    (hcone : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L x)).PosSemidef)
    {Y : HermitianFrobenius ℂ n} (hY : (hermitianFrobeniusMatrix ℂ n Y).PosDef)
    (hgap : (hermitianFrobeniusMatrix ℂ n (Y-L Y)).PosDef) : ‖L‖<1 := by
  obtain ⟨x,hx,hP,heig⟩ := exists_posSemidef_norm_eigenvector L hsym hcone
  have hx0 : hermitianFrobeniusMatrix ℂ n x ≠ 0 := by
    intro h
    apply hx
    apply (hermitianFrobeniusEquiv ℂ n).injective
    exact Subtype.ext h
  have hp := frobInner_pos_of_posSemidef_posDef hP hx0 hgap
  have hq := frobInner_pos_of_posSemidef_posDef hP hx0 hY
  change 0 < inner ℝ x (Y-L Y) at hp
  change 0 < inner ℝ x Y at hq
  have hs := hsym x Y
  change inner ℝ (L x) Y = inner ℝ x (L Y) at hs
  rw [heig,inner_smul_left] at hs
  rw [inner_sub_right,← hs] at hp
  simp only [starRingEnd_apply,star_trivial] at hp
  nlinarith

/-- The strict Hilbert test, Frobenius norm test and existence of a strict
positive supersolution are equivalent.
@isnad1 id=and.2h2v.s10.fb8bfea36bb8 from=translated src=- shape=ad486c37 vocab=8bdb099b
-/
theorem positiveCone_stability_iff [Nonempty n]
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n) (hsym : L.IsSymmetric)
    (hcone : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L x)).PosSemidef) :
    ((∀ x≠0,0 < inner ℝ x (x-L x)) ↔ ‖L‖<1) ∧
    (‖L‖<1 ↔ ∃Y, (hermitianFrobeniusMatrix ℂ n Y).PosDef ∧
      (hermitianFrobeniusMatrix ℂ n (Y-L Y)).PosDef) := by
  refine ⟨inner_sub_map_pos_iff_norm_lt_one L hsym hcone,?_⟩
  constructor
  · intro h
    obtain ⟨Y,hY,hg,_⟩ := exists_posDef_supersolution_of_norm_lt_one L hcone h
    exact ⟨Y,hY,hg⟩
  · rintro ⟨Y,hY,hg⟩
    exact norm_lt_one_of_posDef_supersolution L hsym hcone hY hg

end NLAlib
