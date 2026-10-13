/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard, Pietro Monticone, Ruben Van de Velde
-/
module

public import Tengoku

/-!
# TODO

* Rename `Coe.ringHom` to `coeRingHom`
* Protect `PadicInt.norm_mul`, `PadicInt.norm_units`, `PadicInt.norm_pow`
-/

@[expose] public section

open Function Topology Subgroup
open scoped NNReal nonZeroDivisors Pointwise

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt
variable {x : ℤ_[p]}

attribute [local simp] coe_eq_zero

/--
@isnad1 id=eq.0h1v.s7.0d125e128bfa from=translated src=- shape=4aa0daf1 vocab=b0ab22ad
-/
@[local simp, norm_cast] lemma coe_coeRingHom : ⇑(Coe.ringHom (p := p)) = (↑) := rfl

/--
@isnad1 id=injectiv.0h1v.s5.c070b64cef61 from=translated src=- shape=52fcb72b vocab=d7025ff1
-/
lemma coe_injective : Injective ((↑) : ℤ_[p] → ℚ_[p]) := Subtype.val_injective

/--
@isnad1 id=iff.0h3v.s6.d47b28a4c9b1 from=translated src=- shape=2b770ce6 vocab=b6dc7197
-/
@[local simp] lemma coe_inj {x y : ℤ_[p]} : (x : ℚ_[p]) = (y : ℚ_[p]) ↔ x = y := coe_injective.eq_iff

local instance : Infinite ℤ_[p] := CharZero.infinite _

/--
@isnad1 id=eq.0h1v.s6.ee6994aac22e from=translated src=- shape=c5c34f3a vocab=c7a868dd
-/
@[local simp] lemma nnnorm_p : ‖(p : ℤ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by simp [nnnorm]; rfl

/--
@isnad1 id=eq.0h2v.s6.ef3732a230d9 from=translated src=- shape=3aa59947 vocab=50c9538b
-/
@[local simp] protected lemma nnnorm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖₊ = 1 := by
  simp [← norm_toNNReal]

/--
@isnad1 id=ex.1h2v.s7.c63bd0c61bea from=translated src=- shape=f2803ac3 vocab=2daed63a
-/
lemma exists_unit_mul_p_pow_eq (hx : x ≠ 0) : ∃ (u : ℤ_[p]ˣ) (n : ℕ), (u : ℤ_[p]) * p ^ n = x :=
  ⟨_, _, (unitCoeff_spec hx).symm⟩

/--
@isnad1 id=eq.0h3v.s7.d1378f504b8b from=translated src=- shape=52cfce53 vocab=820736e1
-/
@[local simp] lemma image_coe_smul_set (x : ℤ_[p]) (s : Set ℤ_[p]) :
    ((↑) '' (x • s) : Set ℚ_[p]) = x • (↑) '' s := Set.image_comm fun _ ↦ rfl

-- Yaël: Do we really want this as a coercion?
noncomputable local instance : Coe ℤ_[p]ˣ ℚ_[p]ˣ where coe := Units.map Coe.ringHom.toMonoidHom

lemma _root_.AddSubgroup.comap_smul_one (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [FaithfulSMul R A]
    (r : R) : AddSubgroup.comap (algebraMap R A) (r • (1 : Submodule R A).toAddSubgroup) =
    r • (1 : Submodule R R).toAddSubgroup := by
  ext s
  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_coe, AddSubgroup.mem_smul_pointwise_iff_exists,
    Submodule.mem_toAddSubgroup, Submodule.mem_one, exists_exists_eq_and, Ideal.one_eq_top,
    Submodule.top_toAddSubgroup, AddSubgroup.mem_top, smul_eq_mul, true_and]
  apply exists_congr (fun t ↦ ?_)
  rw [Algebra.smul_def, ← map_mul, Injective.eq_iff]
  rwa [← faithfulSMul_iff_algebraMap_injective R A]

/--
@isnad1 id=eq.1h2v.s8.b7bf888c7d05 from=translated src=- shape=d8112fae vocab=be1ee979
-/
lemma index_span_p_pow (hx : x ≠ 0) :
    (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ x.valuation})).index =
      ‖(x : ℚ_[p])‖₊⁻¹ := by
  have quotient_equiv_zmod := RingHom.quotientKerEquivOfSurjective
    (f := PadicInt.toZModPow (x.valuation) (p := p)) (R := ℤ_[p])
    (ZMod.ringHom_surjective (PadicInt.toZModPow x.valuation))
  have card_eq_zmod := Nat.card_congr quotient_equiv_zmod.toEquiv
  have quotient_equiv_quotient :=
    Ideal.quotEquivOfEq (PadicInt.ker_toZModPow (x.valuation) (p := p))
  have card_eq_quotient := Nat.card_congr quotient_equiv_quotient.toEquiv
  rw [card_eq_quotient] at card_eq_zmod
  have quotients_defeq :
    (ℤ_[p] ⧸ (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ x.valuation}))) =
    (ℤ_[p] ⧸ Ideal.span {(p: ℤ_[p]) ^ x.valuation}) := rfl
  simp [AddSubgroup.index, quotients_defeq, card_eq_zmod, NNReal.eq_iff,
    norm_eq_zpow_neg_valuation hx]

/--
@isnad1 id=eq.0h2v.s10.b79374dcf6d0 from=translated src=- shape=8a61aa05 vocab=3ab7a7f3
-/
lemma smul_submodule_one_index :
    (x • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup.index = ‖(x : ℚ_[p])‖₊⁻¹ := by
  by_cases hx: x = 0
  · simp [hx]
  · have x_factor := PadicInt.unitCoeff_spec hx
    nth_rw 1 [x_factor]
    rw [Submodule.smul_one_eq_span, ← smul_eq_mul,
      Submodule.span_singleton_smul_eq (Units.isUnit _),
      Ideal.submodule_span_eq, index_span_p_pow hx]

/-- `x • S` has index `‖x‖⁻¹` in `S`, where `S` is the copy of `ℤ_[p]` inside `ℚ_[p]`
@isnad1 id=eq.0h2v.s9.5a11c37acfdf from=translated src=- shape=daf5582b vocab=c9a61950
-/
lemma smul_submodule_one_relIndex :
    (x • (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup).relIndex
      (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup = ‖x.val‖₊⁻¹ := by
  have relIndex_in_z_p : (x • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup.index = ‖(x : ℚ_[p])‖₊⁻¹ :=
    smul_submodule_one_index
  rw [← AddSubgroup.relIndex_top_right] at relIndex_in_z_p
  -- Use the coercion from ℤ_[p] to ℚ_[p] and `AddSubgroup.relIndex_comap` to convert
  -- our result about subgroups of `Z_[p]` to a result about subgroups of `Q_[p]`.
  let z_q_coe: ℤ_[p] →+ ℚ_[p] := PadicInt.Coe.ringHom.toAddMonoidHom
  let K_Q : AddSubgroup ℚ_[p] := (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup
  let H_Q := (x : ℚ_[p]) • K_Q
  have relIndex_preserved :=
    AddSubgroup.relIndex_comap (H := H_Q) (f := (z_q_coe)) (K := (⊤ : AddSubgroup ℤ_[p]))
  have map_top: (AddSubgroup.map z_q_coe ⊤) = K_Q := by
    ext a
    simp [z_q_coe, K_Q]
  have map_H_Q : (AddSubgroup.comap z_q_coe H_Q) =
    (x • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup := by
    simp only [z_q_coe, H_Q, K_Q, RingHom.toAddMonoidHom_eq_coe,
      Submodule.pointwise_smul_toAddSubgroup, z_q_coe, K_Q,
      ← AddSubgroup.comap_smul_one ℤ_[p] ℚ_[p]]
    rfl
  rw [map_top, map_H_Q] at relIndex_preserved
  rwa [relIndex_preserved] at relIndex_in_z_p

/-- `x • S` has finite  in `S`, where `S` is the copy of `ℤ_[p]` inside `ℚ_[p]`
@isnad1 id=isfinite.1h2v.s9.63217b786a92 from=translated src=- shape=b657adec vocab=abec5e56
-/
lemma smul_submodule_one_isFiniteRelIndex (hx : x ≠ 0) :
    (x • (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup).IsFiniteRelIndex
    (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup where
  relIndex_ne_zero := by
    rw [← Nat.cast_ne_zero (R := ℝ≥0)]
    simp [smul_submodule_one_relIndex, hx]

-- Yaël: Do we really want this as a coercion?
noncomputable local instance : Coe ℤ_[p]⁰ ℚ_[p]ˣ where
  coe x := .mk0 x.1 <| map_ne_zero_of_mem_nonZeroDivisors (M₀ := ℤ_[p])
    Coe.ringHom coe_injective x.2

set_option backward.isDefEq.respectTransparency.types false in
/-- Non-zero p-adic integers generate non-zero p-adic numbers as a group.
@isnad1 id=eq.0h1v.s9.207937db01da from=translated src=- shape=153bc1b2 vocab=e71431fe
-/
lemma closure_nonZeroDivisors_padicInt :
    Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) = ⊤ := by
  set H := Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ))
  rw [eq_top_iff']
  intro x
  obtain ⟨y, z, hz, hyzx⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) x.val
  have hy : y ∈ ℤ_[p]⁰ := by
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq]
    rintro rfl
    simp [eq_comm] at hyzx
  convert div_mem (H := H) (subset_closure <| Set.mem_range_self ⟨y, hy⟩)
    (subset_closure <| Set.mem_range_self ⟨z, hz⟩) using 1
  ext
  simpa using hyzx.symm

end PadicInt

namespace Padic

/--
@isnad1 id=eq.0h1v.s8.8ab7bbf1bbb2 from=translated src=- shape=ea625c7c vocab=f1b70475
-/
lemma submodule_one_eq_closedBall :
    (1 : Submodule ℤ_[p] ℚ_[p]) = Metric.closedBall (0 : ℚ_[p]) 1 := by ext x; simp; simp [PadicInt]

end Padic
-- Tengoku: 9 registration(s) of this module made local so they do not change other libraries (generated)
