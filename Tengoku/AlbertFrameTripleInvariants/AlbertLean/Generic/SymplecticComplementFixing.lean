import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticDetour
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticPairFourStep
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticComplementProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms common_detour_of_two_witnesses` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fourStepPairWord_fixes` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms projectPair_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

theorem common_detour_of_two_witnesses
    (omega : BilinForm (K := K) (V := V)) (x y zx zy : V)
    (hzx : omega zx x ≠ 0) (hzy : omega y zy ≠ 0) :
    ∃ z ∈ [zx, zy, zx + zy], omega z x ≠ 0 ∧ omega y z ≠ 0 := by
  by_cases hyzx : omega y zx ≠ 0
  · exact ⟨zx, by simp, hzx, hyzx⟩
  by_cases hzyx : omega zy x ≠ 0
  · exact ⟨zy, by simp, hzyx, hzy⟩
  refine ⟨zx + zy, by simp, ?_, ?_⟩
  · simp only [map_add, LinearMap.add_apply, not_ne_iff.mp hzyx, add_zero]
    exact hzx
  · simp only [map_add, LinearMap.add_apply, not_ne_iff.mp hyzx, zero_add]
    exact hzy

theorem fourStepPairWord_fixes
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y v f q : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0)
    (hxq : omega x q = 0) (hzq : omega z q = 0)
    (hyq : omega y q = 0) (hvq : omega v q = 0)
    (hfq : omega f q = 0) :
    wordMap omega (fourStepPairWord omega halt x z y v f hxz hzy) q = q := by
  let vp := firstAlignment omega halt x z y hxz hzy v
  have hzxq : omega (z - x) q = 0 := by
    simp only [map_sub, LinearMap.sub_apply, hzq, hxq, sub_zero]
  have hyzq : omega (y - z) q = 0 := by
    simp only [map_sub, LinearMap.sub_apply, hyq, hzq, sub_zero]
  have hAq : firstAlignment omega halt x z y hxz hzy q = q := by
    rw [firstAlignment_apply]
    simp only [equiv_apply, hzxq, hyzq, mul_zero, zero_smul, add_zero]
  have hvpq : omega vp q = 0 := by
    change omega (firstAlignment omega halt x z y hxz hzy v) q = 0
    rw [← hAq, firstAlignment_preserves, hvq]
  have hwpq : omega (vp + avoidanceScalar (omega f vp) • y) q = 0 := by
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hvpq, hyq, mul_zero, add_zero]
  have hwvpq : omega ((vp + avoidanceScalar (omega f vp) • y) - vp) q = 0 := by
    simp only [map_sub, LinearMap.sub_apply, hwpq, hvpq, sub_zero]
  have hfwq : omega (f - (vp + avoidanceScalar (omega f vp) • y)) q = 0 := by
    simp only [map_sub, LinearMap.sub_apply, hfq, hwpq, sub_zero]
  change equiv omega halt
      (f - (vp + avoidanceScalar (omega f vp) • y))
      (omega f (vp + avoidanceScalar (omega f vp) • y))⁻¹
    (equiv omega halt
      ((vp + avoidanceScalar (omega f vp) • y) - vp)
      (omega (vp + avoidanceScalar (omega f vp) • y) vp)⁻¹
      (firstAlignment omega halt x z y hxz hzy q)) = q
  rw [hAq]
  simp only [equiv_apply, hwvpq, hfwq, mul_zero, zero_smul, add_zero]

theorem projectPair_orthogonal
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (e f c : V)
    (hef : omega e f = 1) :
    omega (projectPair omega e f c) e = 0 ∧
      omega (projectPair omega e f c) f = 0 := by
  have hee := halt e
  have hff := halt f
  have hce := skew_of_alternating omega halt c e
  have hcf := skew_of_alternating omega halt c f
  have hfe := skew_of_alternating omega halt f e
  constructor <;>
    simp only [projectPair, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, hee, hff, hef, hfe, hce, hcf] <;>
    ring

end AlbertLean.Generic.SymplecticTransvection
