import Tengoku.SquarefreeFugledeLean.FugledeAudit.FourierUnitary
import Tengoku.SquarefreeFugledeLean.FugledeAudit.CoordinateLevels

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

open Module

variable {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]

/--
@isnad1 id=eq.0h2v.s7.4b3833a7be22 from=translated src=- shape=088ea2ed vocab=282d1639
-/
theorem standard_character_unit (x : ZMod q) :
    star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
  rw [std_character_star, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

noncomputable def phaseMap (label : ι → ZMod q) : End ℂ (EuclideanSpace ℂ ι) where
  toFun v := WithLp.toLp 2 (fun a => ZMod.stdAddChar (label a) * v a)
  map_add' x y := by ext a; simp [mul_add]
  map_smul' c x := by ext a; simp [mul_left_comm]

omit [Fintype ι] in
/--
@isnad1 id=eq.0h5v.s8.82beca93a68d from=translated src=- shape=2d4778a7 vocab=44f5c716
-/
theorem phase_map_apply (label : ι → ZMod q) (v : EuclideanSpace ℂ ι) (a : ι) :
    phaseMap label v a = ZMod.stdAddChar (label a) * v a := rfl

omit [Fintype ι] in
/--
@isnad1 id=eq.0h4v.s9.a6d211ae842c from=translated src=- shape=be9f63e8 vocab=f260a469
-/
theorem phase_map_inverse (label : ι → ZMod q) (v : EuclideanSpace ℂ ι) :
    phaseMap (-label) (phaseMap label v) = v := by
  ext a
  simp only [phase_map_apply, Pi.neg_apply, ← std_character_star, ← mul_assoc,
    standard_character_unit, one_mul]

/--
@isnad1 id=eq.0h5v.s9.136fbb14b206 from=translated src=- shape=9dd17f53 vocab=fea481ed
-/
theorem phase_map_inner (label : ι → ZMod q) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (phaseMap label x) (phaseMap label y) = inner ℂ x y := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  change inner ℂ (ZMod.stdAddChar (label a) • x a) (ZMod.stdAddChar (label a) • y a) = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  change (star (ZMod.stdAddChar (label a)) * ZMod.stdAddChar (label a)) * inner ℂ (x a) (y a) = _
  rw [standard_character_unit, one_mul]

noncomputable def phaseUnitary (label : ι → ZMod q) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  let e : EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
    { phaseMap label with
      invFun := phaseMap (-label)
      left_inv := phase_map_inverse label
      right_inv := fun v => by simpa using phase_map_inverse (-label) v }
  e.isometryOfInner (phase_map_inner label)

omit [Fintype ι] in
/--
@isnad1 id=eq.0h6v.s9.f9a451df4e83 from=translated src=- shape=99df0e6a vocab=6395a675
-/
theorem phase_power_apply (label : ι → ZMod q) (n : ℕ) (v : EuclideanSpace ℂ ι) (a : ι) :
    (phaseMap label ^ n) v a = ZMod.stdAddChar (label a) ^ n * v a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', End.mul_apply, phase_map_apply, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

omit [Fintype ι] in
/--
@isnad1 id=eq.0h3v.s9.977d18c2df4e from=translated src=- shape=6b5683f9 vocab=6d9d2c48
-/
theorem phase_power_order (label : ι → ZMod q) : phaseMap label ^ q = 1 := by
  ext v a
  rw [phase_power_apply, ← AddChar.map_nsmul_eq_pow]
  simp

/--
@isnad1 id=isprimit.0h1v.s6.26ca2b7dde27 from=translated src=- shape=d2de6518 vocab=d3b1e8ea
-/
theorem standard_character_primitive_root : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod q)) q := by
  refine ⟨by simp [← AddChar.map_nsmul_eq_pow], ?_⟩
  intro n hn
  have he : ZMod.stdAddChar (n : ZMod q) = ZMod.stdAddChar (0 : ZMod q) := by
    simpa [← AddChar.map_nsmul_eq_pow] using hn
  exact (ZMod.natCast_eq_zero_iff n q).mp (ZMod.injective_stdAddChar he)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def conjugatedPhase (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) : E ≃ₗᵢ[ℂ] E :=
  (F.symm.trans (phaseUnitary label)).trans F

/--
@isnad1 id=eq.0h6v.s10.3feb363671d6 from=translated src=- shape=8006b0c8 vocab=ee24ca75
-/
theorem conjugated_phase_apply (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) (v : E) :
    conjugatedPhase F label v = F (phaseMap label (F.symm v)) := rfl

/--
@isnad1 id=eq.0h7v.s11.aeaa5c28b338 from=translated src=- shape=199050e8 vocab=e17be21c
-/
theorem conjugated_phase_power_apply (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) (n : ℕ) (v : E) :
    ((conjugatedPhase F label).toLinearMap ^ n) v = F ((phaseMap label ^ n) (F.symm v)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', End.mul_apply, ih]
    change conjugatedPhase F label (F ((phaseMap label ^ n) (F.symm v))) = _
    rw [conjugated_phase_apply, F.symm_apply_apply, pow_succ', End.mul_apply]

/--
@isnad1 id=eq.0h5v.s9.fbfca7d2a600 from=translated src=- shape=86095150 vocab=5fb58210
-/
theorem conjugated_phase_order (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) : (conjugatedPhase F label).toLinearMap ^ q = 1 := by
  apply LinearMap.ext
  intro v
  rw [conjugated_phase_power_apply, phase_power_order]
  simp

end FugledeAudit
