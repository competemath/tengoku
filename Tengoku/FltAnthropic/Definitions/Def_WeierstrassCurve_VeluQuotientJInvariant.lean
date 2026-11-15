import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluQuotientMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))

/--
@isnad1 id=eq.0h3v.s6.944e2578584b from=translated src=- shape=d7c8c7eb vocab=19ed667f
-/
lemma veluQuotient_c₄' : (W.veluQuotient S).c₄ = W.c₄ + 240 * W.veluTSum S := by
  simp only [c₄, veluQuotient_b₂, veluQuotient_b₄]
  ring

/--
@isnad1 id=eq.0h2v.s6.1a3565472d1e from=translated src=- shape=50bb98d6 vocab=b785029a
-/
theorem Δ_mul_j (V : WeierstrassCurve R) [V.IsElliptic] : V.Δ * V.j = V.c₄ ^ 3 := by
  rw [j, ← coe_Δ', ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/--
@isnad1 id=eq.0h3v.s7.cab558e825e2 from=translated src=- shape=6568b494 vocab=6c1c4b94
-/
theorem veluQuotient_Δ_mul_j [(W.veluQuotient S).IsElliptic] :
    (W.veluQuotient S).Δ * (W.veluQuotient S).j = (W.c₄ + 240 * W.veluTSum S) ^ 3 := by
  rw [Δ_mul_j, veluQuotient_c₄']

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/--
@isnad1 id=eq.1h3v.s7.3ea92d13107f from=translated src=- shape=9d3b5b70 vocab=3311ab29
-/
theorem veluQuotient_j (hΔ : (W.veluQuotient S).Δ ≠ 0) :
    haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient S).j = (W.c₄ + 240 * W.veluTSum S) ^ 3 / (W.veluQuotient S).Δ := by
  haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [eq_div_iff hΔ, mul_comm]
  exact veluQuotient_Δ_mul_j W S

end Field

namespace VeluQuotientJGates

def W27a3 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩

def S₀ : Finset (ℚ × ℚ) := {(0, 0)}

/--
@isnad1 id=eq.0h0v.s3.d423e0c9630a from=translated src=- shape=f751f94f vocab=614b277c
-/
lemma veluTSum_S₀ : W27a3.veluTSum S₀ = 0 := by
  simp [W27a3, S₀, veluTSum, veluT_eq, b₂, b₄]

/--
@isnad1 id=eq.0h0v.s3.c959f67fb214 from=translated src=- shape=f751f94f vocab=e13bebb6
-/
lemma veluWSum_S₀ : W27a3.veluWSum S₀ = 1 := by
  simp [W27a3, S₀, veluWSum, veluW, veluU, veluGy, veluT_eq, b₂, b₄]

/--
@isnad1 id=eq.0h0v.s5.4386a1bf42ca from=translated src=- shape=38cc445a vocab=7c48a10f
-/
theorem veluQuotient_27a3_eq : W27a3.veluQuotient S₀ = ⟨0, 0, 1, 0, -7⟩ := by
  ext <;>
    simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
      veluQuotient_a₆, veluTSum_S₀, veluWSum_S₀] <;>
    simp [W27a3, b₂]

/--
@isnad1 id=eq.0h0v.s4.0a12f123b9ab from=translated src=- shape=06975fd8 vocab=b52a5095
-/
theorem Δ_veluQuotient_27a3 : (W27a3.veluQuotient S₀).Δ = -19683 := by
  rw [veluQuotient_Δ, veluTSum_S₀, veluWSum_S₀]
  simp only [W27a3, Δ, b₂, b₄, b₆, b₈]
  norm_num

/--
@isnad1 id=isellipt.0h0v.s3.ccfc9d65ae2b from=translated src=- shape=aba4b0e5 vocab=fdbb3a88
-/
instance instIsElliptic27a4 : (W27a3.veluQuotient S₀).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [Δ_veluQuotient_27a3]; norm_num)⟩

/--
@isnad1 id=eq.0h0v.s4.c1836b6f628f from=translated src=- shape=0e11011f vocab=b00122a0
-/
theorem j_veluQuotient_27a3 : (W27a3.veluQuotient S₀).j = 0 := by
  have hΔ : (W27a3.veluQuotient S₀).Δ ≠ 0 := by rw [Δ_veluQuotient_27a3]; norm_num
  rw [veluQuotient_j W27a3 S₀ hΔ, veluTSum_S₀]
  simp [W27a3, c₄, b₂, b₄]

end VeluQuotientJGates

end WeierstrassCurve
