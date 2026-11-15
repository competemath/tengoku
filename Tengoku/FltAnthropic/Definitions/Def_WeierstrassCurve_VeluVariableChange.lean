import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_Velu
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]

section Embedding

variable (C : VariableChange K)

def vcInvEmbedding : K × K ↪ K × K where
  toFun P := (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2)
  inj' := by
    intro P P' h
    have h1 : Affine.vcXInv C P.1 = Affine.vcXInv C P'.1 := congrArg Prod.fst h
    have h2 : Affine.vcYInv C P.1 P.2 = Affine.vcYInv C P'.1 P'.2 := congrArg Prod.snd h
    have hx : P.1 = P'.1 := by
      have := congrArg (Affine.vcX C) h1
      simpa only [Affine.vcX_vcXInv] using this
    have hy : P.2 = P'.2 := by
      have := congrArg (Affine.vcY C (Affine.vcXInv C P.1)) h2
      rw [Affine.vcY_vcYInv, hx] at this
      simpa only [Affine.vcY_vcYInv] using this
    exact Prod.ext hx hy

/--
@isnad1 id=eq.0h3v.s6.2a6e5e5c5885 from=translated src=- shape=1c7c0ef3 vocab=491bf631
-/
@[simp] lemma vcInvEmbedding_apply (P : K × K) :
    vcInvEmbedding C P = (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2) := rfl

end Embedding

section PerPoint

variable (C : VariableChange K) (W : WeierstrassCurve K)

/--
@isnad1 id=eq.0h5v.s7.8c3fcd64a053 from=translated src=- shape=e22630db vocab=672db557
-/
lemma variableChange_veluGy (x y : K) :
    (C • W).veluGy (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 3 * W.veluGy x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

/--
@isnad1 id=eq.0h5v.s7.b32dab129ff5 from=translated src=- shape=7d69a672 vocab=92b47281
-/
lemma variableChange_veluGx (x y : K) :
    (C • W).veluGx (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * (W.veluGx x y + C.s * W.veluGy x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

/--
@isnad1 id=eq.0h5v.s7.1c138c21aec7 from=translated src=- shape=e22630db vocab=24e276b3
-/
lemma variableChange_veluT (x y : K) :
    (C • W).veluT (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluT x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

/--
@isnad1 id=eq.0h5v.s7.7f2bb6d659ec from=translated src=- shape=e22630db vocab=eb344cdd
-/
lemma variableChange_veluU (x y : K) :
    (C • W).veluU (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * W.veluU x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluU, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

/--
@isnad1 id=eq.0h5v.s7.c121f0b65f0e from=translated src=- shape=7d69a672 vocab=4892b6ea
-/
lemma variableChange_veluW (x y : K) :
    (C • W).veluW (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluW x y - C.r * W.veluT x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluW, veluU, veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

end PerPoint

section Sums

variable (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))

/--
@isnad1 id=eq.0h4v.s7.75b53e3fa0b8 from=translated src=- shape=1abc4cdf vocab=b09681f8
-/
lemma variableChange_veluTSum :
    (C • W).veluTSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluTSum S := by
  rw [veluTSum, veluTSum, Finset.sum_map, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluT C W P.1 P.2

/--
@isnad1 id=eq.0h4v.s7.c26cf3ddf1be from=translated src=- shape=8dfba21f vocab=7401824e
-/
lemma variableChange_veluWSum :
    (C • W).veluWSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluWSum S - C.r * W.veluTSum S) := by
  rw [veluWSum, Finset.sum_map]
  rw [show W.veluWSum S - C.r * W.veluTSum S
      = ∑ P ∈ S, (W.veluW P.1 P.2 - C.r * W.veluT P.1 P.2) by
    rw [veluWSum, veluTSum, Finset.mul_sum, ← Finset.sum_sub_distrib]]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluW C W P.1 P.2

end Sums

end WeierstrassCurve
