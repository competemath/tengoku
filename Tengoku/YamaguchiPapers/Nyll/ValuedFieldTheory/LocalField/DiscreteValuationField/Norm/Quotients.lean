/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Develops quotient groups attached to an abstract valued norm, including kernel, image, and
representative criteria.
-/

/-!
Identifies norm-quotient classes with valuation classes modulo the residue degree and constructs
the resulting cyclic equivalences.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)

/--
The defining evaluation formula for `valuation` is `vG.val (N.toHom x) = (N.residueDegree : ℤ) *
vH.val x`.
@isnad1 id=eq.0h6v.s6.ff195a8a7ebf from=translated src=- shape=aec84282 vocab=082f37b2
-/
@[simp] theorem valuation_apply (x : H) :
    vG.val (N.toHom x) = (N.residueDegree : ℤ) * vH.val x :=
  N.valuation_formula x

/--
`valuation_apply` satisfies the division formula `vG.val (N.toHom (x / y)) = (N.residueDegree : ℤ)
* (vH.val x - vH.val y)`.
@isnad1 id=eq.0h7v.s7.99d3914d4bdc from=translated src=- shape=9ac7d976 vocab=35cb4cb8
-/
@[simp] theorem valuation_apply_div (x y : H) :
    vG.val (N.toHom (x / y)) =
      (N.residueDegree : ℤ) * (vH.val x - vH.val y) := by
  rw [N.valuation_apply, vH.val_div]

/--
`valuation_apply_uniformizer` satisfies the integer-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * n`.
@isnad1 id=eq.1h7v.s7.2614ca55d8f4 from=translated src=- shape=c59cc858 vocab=54f31988
-/
@[simp] theorem valuation_apply_uniformizer_zpow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℤ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.val_uniformizer_zpow hϖH n]

/--
`valuation_apply_uniformizer` satisfies the natural-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * (n : ℤ)`.
@isnad1 id=eq.1h7v.s7.8016c4470c01 from=translated src=- shape=b5913c2d vocab=fa422fa8
-/
@[simp] theorem valuation_apply_uniformizer_pow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℕ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply, vH.val_uniformizer_pow hϖH n]

/--
`valuation_apply_zeroSubgroup_mul_uniformizer` satisfies the integer-power formula `vG.val
(N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * n`.
@isnad1 id=eq.2h8v.s7.1629237cdcd8 from=translated src=- shape=b12ba3e8 vocab=d698e33f
-/
@[simp] theorem valuation_apply_zeroSubgroup_mul_uniformizer_zpow
    {ϖH u : H} (hϖH : vH.IsUniformizer ϖH)
    (hu : u ∈ vH.zeroSubgroup) (n : ℤ) :
    vG.val (N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.valuation_uniformizer_normal_form hϖH hu n]

/--
`valuation_apply_zeroSubgroup_mul_uniformizer` satisfies the natural-power formula `vG.val
(N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ)`.
@isnad1 id=eq.2h8v.s7.786b17404485 from=translated src=- shape=924ce07f vocab=2d905d36
-/
@[simp] theorem valuation_apply_zeroSubgroup_mul_uniformizer_pow
    {ϖH u : H} (hϖH : vH.IsUniformizer ϖH)
    (hu : u ∈ vH.zeroSubgroup) (n : ℕ) :
    vG.val (N.toHom (u * ϖH ^ n)) =
      (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply]
  have hv := vH.valuation_uniformizer_normal_form hϖH hu (n : ℤ)
  simpa using congrArg (fun m : ℤ => (N.residueDegree : ℤ) * m) hv

/--
Establishes the identity `vG.valuationHom (N.toHom x) = vH.valuationHom x ^ (N.residueDegree :
ℤ)`.
@isnad1 id=eq.0h6v.s7.baef72f86d46 from=translated src=- shape=d692b966 vocab=0a533560
-/
@[simp] theorem valuationHom_apply_norm (x : H) :
    vG.valuationHom (N.toHom x) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.valuationHom_apply,
    N.valuation_apply,
    MultiplicativeIntegerValuation.valuationHom_apply,
    mul_comm (N.residueDegree : ℤ) (vH.val x),
    Int.ofAdd_mul]

/--
Establishes the identity `Multiplicative.toAdd (vG.valuationHom (N.toHom x)) = (N.residueDegree :
ℤ) * Multiplicative.toAdd (vH.valuationHom x)`.
@isnad1 id=eq.0h6v.s8.f177e6fc4e9c from=translated src=- shape=2c04ff44 vocab=120e72b7
-/
@[simp] theorem toAdd_valuationHom_apply_norm (x : H) :
    Multiplicative.toAdd (vG.valuationHom (N.toHom x)) =
      (N.residueDegree : ℤ) *
        Multiplicative.toAdd (vH.valuationHom x) := by
  rw [N.valuationHom_apply_norm, Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/--
`valuationHom_apply_norm` satisfies the division formula `vG.valuationHom (N.toHom (x / y)) =
vH.valuationHom (x / y) ^ (N.residueDegree : ℤ)`.
@isnad1 id=eq.0h7v.s7.5593dc074944 from=translated src=- shape=4464148d vocab=00590ff8
-/
@[simp] theorem valuationHom_apply_norm_div (x y : H) :
    vG.valuationHom (N.toHom (x / y)) =
      vH.valuationHom (x / y) ^ (N.residueDegree : ℤ) :=
  N.valuationHom_apply_norm (x / y)

/-- The norm subgroup attached to a valued norm.-/
def normSubgroup : Subgroup G :=
  N.toHom.range

/-- The valuation of any norm is divisible by the residue degree.
@isnad1 id=dvd.1h6v.s6.a34b792edbb8 from=translated src=- shape=b4788f76 vocab=f4bd38c1
-/
theorem residueDegree_dvd_valuation_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    (N.residueDegree : ℤ) ∣ vG.val x := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨vH.val y, N.valuation_apply y⟩

/--
Establishes the identity `((vG.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ) = vH.valuationHom x ^
(N.residueDegree : ℤ)`.
@isnad1 id=eq.0h6v.s9.95eebe96dde3 from=translated src=- shape=27672c6b vocab=a1fc95a3
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
      Multiplicative ℤ) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.coe_quotientZeroSubgroupEquivValueSubgroup_mk]
  exact N.valuationHom_apply_norm x

/--
Establishes the identity `Multiplicative.toAdd (((vG.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ)) =
(N.residueDegree : ℤ) * vH.val x`.
@isnad1 id=eq.0h6v.s9.fc1ef0bd0d06 from=translated src=- shape=cc8ff6c3 vocab=eb18cce7
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    Multiplicative.toAdd
      (((vG.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
        Multiplicative ℤ)) =
      (N.residueDegree : ℤ) * vH.val x := by
  rw [N.coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk,
    Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/-- If all valuation-zero target elements are norms and the source valuation
has a uniformizer, valuation divisibility by the residue degree is sufficient
for norm-subgroup membership.
@isnad1 id=mem.3h7v.s6.5cb1a66e9f94 from=translated src=- shape=ad9b2d71 vocab=665300e2
-/
theorem mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    {x : G} (hx : (N.residueDegree : ℤ) ∣ vG.val x) :
    x ∈ N.normSubgroup := by
  rcases hx with ⟨n, hn⟩
  have hval :
      vG.val x = vG.val (N.toHom (ϖH ^ n)) := by
    rw [N.valuation_apply_uniformizer_zpow hϖH n, hn]
  rcases vG.exists_zeroSubgroup_mul_eq_of_val_eq hval with ⟨u, hu, hux⟩
  have hu_norm : u ∈ N.normSubgroup := hzero hu
  have hnorm : u * N.toHom (ϖH ^ n) ∈ N.normSubgroup :=
    N.normSubgroup.mul_mem hu_norm
      ((MonoidHom.mem_range (f := N.toHom)).2 ⟨ϖH ^ n, rfl⟩)
  simpa [← hux] using hnorm

/-- With source uniformizer and norm-surjectivity on valuation-zero target
elements, the norm subgroup is exactly the elements whose valuation is
divisible by the residue degree.
@isnad1 id=iff.2h7v.s6.71613ddba04c from=translated src=- shape=72fa71af vocab=665300e2
-/
theorem mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    x ∈ N.normSubgroup ↔ (N.residueDegree : ℤ) ∣ vG.val x := by
  constructor
  · exact N.residueDegree_dvd_valuation_of_mem_normSubgroup
  · exact N.mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero

/-- The valuation map modulo the residue-degree multiple subgroup.  This is
the canonical value-group map used to compare norm quotients with
`ℤ / fℤ`.-/
def valueModResidueDegreeHom :
    G →* Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.mk'
      (integerMultipleSubgroup (N.residueDegree : ℤ))).comp
    vG.valuationHom

/--
The defining evaluation formula for `valueModResidueDegreeHom` is `N.valueModResidueDegreeHom x =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (vG.valuationHom x)`.
@isnad1 id=eq.0h6v.s9.25865ad949bb from=translated src=- shape=d4b52e94 vocab=22ec23ea
-/
@[simp] theorem valueModResidueDegreeHom_apply (x : G) :
    N.valueModResidueDegreeHom x =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) :=
  rfl

/-- The specified map is surjective: `Function.Surjective N.valueModResidueDegreeHom`.
@isnad1 id=surjecti.1h6v.s8.26303a0104af from=translated src=- shape=97e1bc7e vocab=3d2b800d
-/
theorem valueModResidueDegreeHom_surjective_of_uniformizer
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Function.Surjective N.valueModResidueDegreeHom := by
  intro q
  rcases
    QuotientGroup.mk'_surjective
      (integerMultipleSubgroup (N.residueDegree : ℤ)) q with
    ⟨m, rfl⟩
  exact ⟨ϖG ^ Multiplicative.toAdd m, by
    rw [N.valueModResidueDegreeHom_apply,
      MultiplicativeIntegerValuation.valuationHom_apply,
      vG.val_uniformizer_zpow hϖG (Multiplicative.toAdd m),
      ofAdd_toAdd]⟩

/--
Characterizes `x ∈ N.valueModResidueDegreeHom.ker` by the equivalent condition `(N.residueDegree :
ℤ) ∣ vG.val x`.
@isnad1 id=iff.0h6v.s7.7537ff6741e3 from=translated src=- shape=ac22d115 vocab=9f9624f5
-/
theorem mem_valueModResidueDegreeHom_ker_iff (x : G) :
    x ∈ N.valueModResidueDegreeHom.ker ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  change N.valueModResidueDegreeHom x = 1 ↔
    (N.residueDegree : ℤ) ∣ vG.val x
  rw [N.valueModResidueDegreeHom_apply,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simp [QuotientGroup.mk'_apply]

/-- The map `G/G⁰ → ℤ/fℤ` induced by valuation modulo the
residue-degree multiple subgroup.-/
def zeroSubgroupQuotientToValueModResidueDegree :
    G ⧸ vG.zeroSubgroup →*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  QuotientGroup.map vG.zeroSubgroup
    (integerMultipleSubgroup (N.residueDegree : ℤ)) vG.valuationHom (by
      intro x hx
      change vG.valuationHom x ∈
        integerMultipleSubgroup (N.residueDegree : ℤ)
      rw [mem_integerMultipleSubgroup_iff,
        MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
        (MultiplicativeIntegerValuation.mem_zeroSubgroup_iff vG x).1 hx]
      exact dvd_zero (N.residueDegree : ℤ))

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
(vG.valuationHom x)`.
@isnad1 id=eq.0h6v.s10.65f1876ff0aa from=translated src=- shape=18bf5932 vocab=2d261235
-/
@[simp] theorem zeroSubgroupQuotientToValueModResidueDegree_mk (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  simp [zeroSubgroupQuotientToValueModResidueDegree]

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
(Multiplicative.ofAdd (vG.val x))`.
@isnad1 id=eq.0h6v.s10.54fa7cc81cc7 from=translated src=- shape=aaf94a01 vocab=b98f7141
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk_ofAdd (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk x,
    MultiplicativeIntegerValuation.valuationHom_apply]

/--
The specified map is surjective: `Function.Surjective
N.zeroSubgroupQuotientToValueModResidueDegree`.
@isnad1 id=surjecti.1h6v.s9.c838ab0c81c4 from=translated src=- shape=6f801d8f vocab=8a0b3296
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_surjective_of_uniformizer
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Function.Surjective N.zeroSubgroupQuotientToValueModResidueDegree := by
  intro q
  rcases
    QuotientGroup.mk'_surjective
      (integerMultipleSubgroup (N.residueDegree : ℤ)) q with
    ⟨m, rfl⟩
  exact ⟨QuotientGroup.mk' vG.zeroSubgroup
      (ϖG ^ Multiplicative.toAdd m), by
    rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk,
      MultiplicativeIntegerValuation.valuationHom_apply,
      vG.val_uniformizer_zpow hϖG (Multiplicative.toAdd m),
      ofAdd_toAdd]⟩

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk' vG.zeroSubgroup x)
= 1` by the equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x`.
@isnad1 id=iff.0h6v.s9.6e581741f714 from=translated src=- shape=41ae3e07 vocab=a0000851
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk_eq_one_iff
    (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) = 1 ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simp [QuotientGroup.mk'_apply]

/--
Establishes the identity `N.valueModResidueDegreeHom.ker = (integerMultipleSubgroup
(N.residueDegree : ℤ)).comap vG.valuationHom`.
@isnad1 id=eq.0h5v.s7.db4abbda9700 from=translated src=- shape=1b41421c vocab=56cc260f
-/
theorem valueModResidueDegreeHom_ker_eq_valuationHom_comap :
    N.valueModResidueDegreeHom.ker =
      (integerMultipleSubgroup (N.residueDegree : ℤ)).comap
        vG.valuationHom := by
  rw [valueModResidueDegreeHom,
    ← MonoidHom.comap_ker
      (QuotientGroup.mk'
        (integerMultipleSubgroup (N.residueDegree : ℤ)))
      vG.valuationHom,
    QuotientGroup.ker_mk']

/-- The subgroup of `G/G⁰` consisting of classes whose value is divisible by the
residue degree.  This is the kernel of the value-mod-residue-degree map.-/
def residueDegreeClassSubgroup :
    Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup)
    N.valueModResidueDegreeHom.ker

/-- The subgroup appearing in `N.residueDegreeClassSubgroup.Normal` is normal.
@isnad1 id=normal.0h5v.s5.bc2a71b6dc2d from=translated src=- shape=46896270 vocab=08a8fb71
-/
instance residueDegreeClassSubgroup_normal :
    N.residueDegreeClassSubgroup.Normal := by
  dsimp [residueDegreeClassSubgroup]
  infer_instance

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree.ker =
N.residueDegreeClassSubgroup`.
@isnad1 id=eq.0h5v.s7.35a02b65f100 from=translated src=- shape=20b58db1 vocab=32bd9d38
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup :
    N.zeroSubgroupQuotientToValueModResidueDegree.ker =
      N.residueDegreeClassSubgroup := by
  rw [zeroSubgroupQuotientToValueModResidueDegree, QuotientGroup.ker_map,
    ← N.valueModResidueDegreeHom_ker_eq_valuationHom_comap]
  rfl

/--
Characterizes `q ∈ N.zeroSubgroupQuotientToValueModResidueDegree.ker` by the equivalent condition
`q ∈ N.residueDegreeClassSubgroup`.
@isnad1 id=iff.0h6v.s8.003d972befa8 from=translated src=- shape=12c74a39 vocab=7a78785a
-/
theorem mem_zeroSubgroupQuotientToValueModResidueDegree_ker_iff
    (q : G ⧸ vG.zeroSubgroup) :
    q ∈ N.zeroSubgroupQuotientToValueModResidueDegree.ker ↔
      q ∈ N.residueDegreeClassSubgroup := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup]

/--
Characterizes `QuotientGroup.mk' vG.zeroSubgroup x ∈ N.residueDegreeClassSubgroup` by the
equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x`.
@isnad1 id=iff.0h6v.s8.764dcafaec0e from=translated src=- shape=22227d4f vocab=6d6a1c1b
-/
theorem quotientZeroSubgroup_mk_mem_residueDegreeClassSubgroup_iff
    (x : G) :
    QuotientGroup.mk' vG.zeroSubgroup x ∈
        N.residueDegreeClassSubgroup ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  rw [← N.mem_zeroSubgroupQuotientToValueModResidueDegree_ker_iff
      (QuotientGroup.mk' vG.zeroSubgroup x),
    MonoidHom.mem_ker,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk_eq_one_iff x]

/-- First-isomorphism form of the value-mod-residue-degree map.  A target
uniformizer makes `G/G⁰ → ℤ/fℤ` surjective.-/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.quotientMulEquivOfEq
    (N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := N.zeroSubgroupQuotientToValueModResidueDegree)
      (N.zeroSubgroupQuotientToValueModResidueDegree_surjective_of_uniformizer hϖG))

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = N.zeroSubgroupQuotientToValueModResidueDegree
q`.
@isnad1 id=eq.1h7v.s11.6f698a207783 from=translated src=- shape=4680dbd5 vocab=d689d292
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToValueModResidueDegree q := by
  change QuotientGroup.kerLift N.zeroSubgroupQuotientToValueModResidueDegree
      ((QuotientGroup.quotientMulEquivOfEq
        N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup.symm)
        (QuotientGroup.mk q)) = N.zeroSubgroupQuotientToValueModResidueDegree q
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk N.zeroSubgroupQuotientToValueModResidueDegree q

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val
x))`.
@isnad1 id=eq.1h7v.s11.2122249f7aec from=translated src=- shape=0a0324e9 vocab=a76b688d
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk hϖG,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk_ofAdd x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
hϖG).symm (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd
(vG.val x))) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
x)`.
@isnad1 id=eq.1h7v.s12.5d5f9dfdf511 from=translated src=- shape=de5718fc vocab=58b03d3d
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd (vG.val x))) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        ((N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
          (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
            (Multiplicative.ofAdd (vG.val x)))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
          hϖG x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
hϖG).symm (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd
n)) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^
n))`.
@isnad1 id=eq.1h7v.s12.f6235d3095a2 from=translated src=- shape=bed0cb82 vocab=d4358b89
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).injective
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
      hϖG (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]
  exact (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).apply_symm_apply _

/-- Equality criterion in the double quotient by the residue-degree class
subgroup.
@isnad1 id=iff.0h7v.s11.697971dc235c from=translated src=- shape=21cf892e vocab=6bdfcf6c
-/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_iff_div_mem
    (q r : G ⧸ vG.zeroSubgroup) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup q =
        QuotientGroup.mk' N.residueDegreeClassSubgroup r ↔
      q / r ∈ N.residueDegreeClassSubgroup := by
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := N.residueDegreeClassSubgroup) (x := q) (y := r))

/--
Characterizes `QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
x) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup y)` by the
equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x - vG.val y`.
@isnad1 id=iff.0h7v.s11.028486e0d479 from=translated src=- shape=df3dffe1 vocab=e8cd310e
-/
theorem zeroQuotientModuloResidueDegreeClass_mk_mk_eq_iff_residueDegree_dvd
    (x y : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_eq_iff_div_mem]
  rw [← (QuotientGroup.mk' vG.zeroSubgroup).map_div x y,
    N.quotientZeroSubgroup_mk_mem_residueDegreeClassSubgroup_iff (x / y),
    vG.val_div x y]

/-- Every residue-degree double-quotient class has the same representative as a
target-uniformizer power with exponent given by the valuation.
@isnad1 id=eq.1h7v.s11.ba4a682fee94 from=translated src=- shape=3ccabd3d vocab=03742107
-/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizer_zpow_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_mk_eq_iff_residueDegree_dvd,
    vG.val_uniformizer_zpow hϖG (vG.val x), sub_self]
  exact dvd_zero (N.residueDegree : ℤ)

/-- Generator-power form of
`zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizer_zpow_val`.
@isnad1 id=eq.1h7v.s11.4d365f9bd3d9 from=translated src=- shape=ee4639be vocab=03742107
-/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizerClass_zpow_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ vG.val x := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) (vG.val x),
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG (vG.val x)]
  exact N.zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizer_zpow_val
    hϖG x

/-- The residue-degree double quotient is generated by the class of any target
uniformizer.
@isnad1 id=ex.1h7v.s10.714622638ff6 from=translated src=- shape=49b83e1f vocab=90462a13
-/
theorem zeroQuotientModuloResidueDegreeClass_generated_by_uniformizerClass
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (q : (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup) :
    ∃ n : ℤ, q =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  refine QuotientGroup.induction_on q ?_
  intro q₀
  refine QuotientGroup.induction_on q₀ ?_
  intro x
  exact ⟨vG.val x,
    N.zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizerClass_zpow_val
      hϖG x⟩

/-- The residue-degree double quotient is cyclic, generated by the class of any
target uniformizer.
@isnad1 id=eq.1h6v.s10.e5bc14753725 from=translated src=- shape=9bccde52 vocab=6a573088
-/
theorem zeroQuotientModuloResidueDegreeClass_closure_uniformizerClass_eq_top
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Subgroup.closure
        (Set.singleton (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) :
          Set ((G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro q hq
    rcases N.zeroQuotientModuloResidueDegreeClass_generated_by_uniformizerClass
        hϖG q with ⟨n, hqpow⟩
    rw [hqpow]
    exact Subgroup.zpow_mem
      (Subgroup.closure
        (Set.singleton (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) :
          Set ((G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup)))
      (Subgroup.subset_closure (by rfl)) n

/--
`zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_uniformizerClass` satisfies the
integer-power formula `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
((QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)`.
@isnad1 id=eq.1h7v.s12.7c1702c41cf3 from=translated src=- shape=484ad306 vocab=2b246759
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_uniformizerClass_zpow
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
      hϖG (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
`zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass`
satisfies the integer-power formula
`(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm (QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) = (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
@isnad1 id=eq.1h7v.s12.f41214142d66 from=translated src=- shape=eb7ddeb5 vocab=d4358b89
-/
@[simp]
theorem
zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass_zpow
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd
      hϖG n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]

/-- Establishes the identity `N.valueModResidueDegreeHom.ker = N.normSubgroup`.
@isnad1 id=eq.2h6v.s7.0c428952b10a from=translated src=- shape=06b6c4dc vocab=0dd5d22f
-/
theorem valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.valueModResidueDegreeHom.ker = N.normSubgroup := by
  ext x
  rw [N.mem_valueModResidueDegreeHom_ker_iff,
    N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero x]

/-- The subgroup `N/G⁰` inside the zero-valuation quotient `G/G⁰`, where
`N` is the norm subgroup.-/
def normSubgroupClassInZeroQuotient : Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup) N.normSubgroup

/-- The subgroup appearing in `N.normSubgroupClassInZeroQuotient.Normal` is normal.
@isnad1 id=normal.0h5v.s6.3e4b83cac9e6 from=translated src=- shape=04ab474e vocab=7bb8ce23
-/
instance normSubgroupClassInZeroQuotient_normal
    [(N.normSubgroup).Normal] :
    N.normSubgroupClassInZeroQuotient.Normal := by
  dsimp [normSubgroupClassInZeroQuotient]
  infer_instance

/-- Establishes the identity `N.residueDegreeClassSubgroup = N.normSubgroupClassInZeroQuotient`.
@isnad1 id=eq.2h6v.s6.c838715b3dad from=translated src=- shape=dce865c4 vocab=5f83607c
-/
theorem residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.residueDegreeClassSubgroup =
      N.normSubgroupClassInZeroQuotient := by
  rw [residueDegreeClassSubgroup, normSubgroupClassInZeroQuotient,
    N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
      hϖH hzero]

/-- The quotient by the value-side residue-degree class subgroup is the same
as the quotient by the norm-class subgroup when valuation-zero target elements
are norms.-/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormClass
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient :=
  QuotientGroup.quotientMulEquivOfEq
    (N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q`.
@isnad1 id=eq.2h7v.s12.a9aded53351c from=translated src=- shape=6d388635 vocab=f1156ac6
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
  rfl

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)`.
@isnad1 id=eq.2h7v.s12.dd45597f01fa from=translated src=- shape=26b361e0 vocab=f1156ac6
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) = QuotientGroup.mk'
N.residueDegreeClassSubgroup q`.
@isnad1 id=eq.2h7v.s12.54639f0babca from=translated src=- shape=bff04b6b vocab=0e96d623
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup q := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)`.
@isnad1 id=eq.2h7v.s12.d7b1aaadae53 from=translated src=- shape=f7bb5635 vocab=0e96d623
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk hϖH hzero]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass` satisfies the integer-power
formula `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero ((QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) = (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
@isnad1 id=eq.3h8v.s12.d67b744d5407 from=translated src=- shape=b1dffe17 vocab=61525894
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n)
= (QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
@isnad1 id=eq.3h8v.s12.6c563a2b3a54 from=translated src=- shape=17cbef8e vocab=af7da573
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    hϖH hzero (ϖG ^ n)]

/-- The natural map `G/G⁰ → G/N`, where `N` is a norm subgroup containing
the valuation-zero subgroup.-/
def zeroSubgroupQuotientToNormQuotient [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ vG.zeroSubgroup →* G ⧸ N.normSubgroup :=
  QuotientGroup.map vG.zeroSubgroup N.normSubgroup (MonoidHom.id G) (by
      intro x hx
      exact hzero hx)

/--
Establishes the identity `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' N.normSubgroup x`.
@isnad1 id=eq.1h6v.s9.3c05b31d8c0f from=translated src=- shape=a1714c37 vocab=d576e30a
-/
@[simp] theorem zeroSubgroupQuotientToNormQuotient_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.normSubgroup x := by
  exact QuotientGroup.map_mk' vG.zeroSubgroup N.normSubgroup
    (MonoidHom.id G) (fun _ hx => hzero hx) x

/-- The third-isomorphism equivalence
`(G/G⁰)/(N/G⁰) ≃ G/N` for the norm subgroup.-/
noncomputable def zeroQuotientModuloNormClassEquivNormQuotient
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient ≃*
      G ⧸ N.normSubgroup :=
  QuotientGroup.quotientQuotientEquivQuotient
    vG.zeroSubgroup N.normSubgroup hzero

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q) = N.zeroSubgroupQuotientToNormQuotient hzero q`.
@isnad1 id=eq.1h6v.s11.0c61c861c873 from=translated src=- shape=e02c0c23 vocab=2b5c9236
-/
@[simp] theorem zeroQuotientModuloNormClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  change
    QuotientGroup.quotientQuotientEquivQuotientAux
        vG.zeroSubgroup N.normSubgroup hzero q =
      N.zeroSubgroupQuotientToNormQuotient hzero q
  exact
    (QuotientGroup.quotientQuotientEquivQuotientAux_mk
      (N := vG.zeroSubgroup) (M := N.normSubgroup) (h := hzero) q)

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) = QuotientGroup.mk'
N.normSubgroup x`.
@isnad1 id=eq.1h6v.s11.a9d187cfa6b2 from=translated src=- shape=3007d5eb vocab=628d4387
-/
@[simp] theorem zeroQuotientModuloNormClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
  rw [N.zeroQuotientModuloNormClassEquivNormQuotient_mk hzero,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]

/-- Direct form of the quotient comparison from the residue-degree class
subgroup to the norm quotient.-/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormQuotient
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      G ⧸ N.normSubgroup :=
  (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).trans
    (N.zeroQuotientModuloNormClassEquivNormQuotient hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = N.zeroSubgroupQuotientToNormQuotient hzero
q`.
@isnad1 id=eq.2h7v.s11.e14a83ed79d1 from=translated src=- shape=06bdaf9c vocab=910dc22b
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup q)) := rfl
    _ = N.zeroSubgroupQuotientToNormQuotient hzero q := by
      rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q,
        N.zeroQuotientModuloNormClassEquivNormQuotient_mk hzero q]

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroup x`.
@isnad1 id=eq.2h7v.s11.2d85dfc7cf27 from=translated src=- shape=12931de1 vocab=ae50e30b
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk hϖH hzero,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' N.residueDegreeClassSubgroup
(QuotientGroup.mk' vG.zeroSubgroup x)`.
@isnad1 id=eq.2h7v.s11.e567d6bd5485 from=translated src=- shape=b7e9bb5c vocab=1ab9f04d
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
          hϖH hzero x]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormQuotient_uniformizerClass` satisfies the
integer-power formula `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
((QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
(QuotientGroup.mk' N.normSubgroup ϖG) ^ n`.
@isnad1 id=eq.3h8v.s11.c3e1f6b77e6b from=translated src=- shape=8e31317b vocab=9a25d8fa
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) = (QuotientGroup.mk' N.residueDegreeClassSubgroup
(QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
@isnad1 id=eq.3h8v.s12.5c119e204bfa from=translated src=- shape=f1a6b20c vocab=d82b9ce2
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_mk
      hϖH hzero (ϖG ^ n),
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]

/-- The actual norm quotient is the value-group quotient `ℤ / fℤ` when
valuation-zero target elements are norms and the target valuation has a
uniformizer.-/
noncomputable def normQuotientEquivValueModResidueDegree
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ N.normSubgroup ≃*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
        hϖH hzero).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      N.valueModResidueDegreeHom
      (N.valueModResidueDegreeHom_surjective_of_uniformizer hϖG))

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (vG.valuationHom x)`.
@isnad1 id=eq.3h8v.s10.c346138a35bc from=translated src=- shape=23a44a0c vocab=2f6dbdab
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  change QuotientGroup.kerLift N.valueModResidueDegreeHom
      ((QuotientGroup.quotientMulEquivOfEq
        (N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
          hϖH hzero).symm) (QuotientGroup.mk x)) = N.valueModResidueDegreeHom x
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk N.valueModResidueDegreeHom x

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (Multiplicative.ofAdd (vG.val x))`.
@isnad1 id=eq.3h8v.s10.70e08efefe18 from=translated src=- shape=9465a168 vocab=ee64988c
-/
theorem normQuotientEquivValueModResidueDegree_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    MultiplicativeIntegerValuation.valuationHom_apply]

/--
`normQuotientEquivValueModResidueDegree_uniformizer` satisfies the integer-power formula
`N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup (ϖG ^
n)) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)`.
@isnad1 id=eq.3h8v.s10.acbd9437d98d from=translated src=- shape=03f79a2c vocab=40e3c43b
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_uniformizer_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [N.normQuotientEquivValueModResidueDegree_mk_ofAdd
      hϖG hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
Establishes the identity `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val
x))) = QuotientGroup.mk' N.normSubgroup x`.
@isnad1 id=eq.3h8v.s11.b0f782e2a60c from=translated src=- shape=5fed7ccd vocab=880b5d4b
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_symm_mk_val
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd (vG.val x))) =
      QuotientGroup.mk' N.normSubgroup x := by
  apply (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).injective
  calc
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        ((N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
          (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
            (Multiplicative.ofAdd (vG.val x)))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
        exact
          (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).apply_symm_apply _
    _ =
      N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) := by
        rw [N.normQuotientEquivValueModResidueDegree_mk_ofAdd
          hϖG hϖH hzero x]

/--
Establishes the identity `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) =
QuotientGroup.mk' N.normSubgroup (ϖG ^ n)`.
@isnad1 id=eq.3h8v.s11.ce387a33720e from=translated src=- shape=b8977db2 vocab=a168655a
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_symm_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) := by
  apply (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).injective
  rw [N.normQuotientEquivValueModResidueDegree_uniformizer_zpow
      hϖG hϖH hzero n]
  exact (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).apply_symm_apply _

/-- Compatibility of the natural map `G/G⁰ → G/N` with the value-modulo
residue-degree map.
@isnad1 id=eq.3h8v.s11.0525df0909bc from=translated src=- shape=0c4ccc77 vocab=fd7a0370
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_zeroSubgroupQuotientToNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroSubgroupQuotientToNormQuotient hzero
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk x]

/-- The direct residue-degree-class quotient to the norm quotient, followed by
the norm-quotient/value-group equivalence, agrees with the direct
value-mod-residue-degree quotient map on representatives.
@isnad1 id=eq.3h8v.s12.1dffdd72ee69 from=translated src=- shape=af790e6d vocab=d51d3836
-/
@[simp]
theorem
normQuotientEquivValueModResidueDegree_zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup q)) =
      N.zeroSubgroupQuotientToValueModResidueDegree q := by
  refine QuotientGroup.induction_on q ?_
  intro x
  change
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x))) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x)
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
      hϖH hzero (QuotientGroup.mk' vG.zeroSubgroup x),
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk x]

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x))) = QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val x))`.
@isnad1 id=eq.3h8v.s12.86bde8571474 from=translated src=- shape=a5502045 vocab=60d2710b
-/
@[simp]
theorem
normQuotientEquivValueModResidueDegree_zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
      hϖH hzero x,
    N.normQuotientEquivValueModResidueDegree_mk_ofAdd hϖG hϖH hzero x]

end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory

universe u v

namespace LocalFieldTheory

noncomputable section

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)

/-- Under the value-group equivalence, the `n`th power of the target
uniformizer class maps to the class of `n` modulo the residue-degree subgroup.
@isnad1 id=eq.3h8v.s10.b6565ba60177 from=translated src=- shape=41378b01 vocab=40e3c43b
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]
  exact N.normQuotientEquivValueModResidueDegree_uniformizer_zpow
    hϖG hϖH hzero n

/--
`normQuotientEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass` satisfies the
integer-power formula `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) =
(QuotientGroup.mk' N.normSubgroup ϖG) ^ n`.
@isnad1 id=eq.3h8v.s11.7b51db6fd522 from=translated src=- shape=7aacd7fd vocab=a168655a
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  rw [N.normQuotientEquivValueModResidueDegree_symm_mk_ofAdd
      hϖG hϖH hzero n,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]

/-- The actual norm quotient as the standard cyclic group
`Multiplicative (ZMod f)`, where `f` is the residue degree in the valuation
formula.-/
noncomputable def normQuotientEquivZMod
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ N.normSubgroup ≃* Multiplicative (ZMod N.residueDegree) :=
  (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).trans
    (valueModIntegerMultipleSubgroupEquivZMod (N.residueDegree : ℤ))

/--
Establishes the identity `N.normQuotientEquivZMod hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup
x) = Multiplicative.ofAdd ((vG.val x : ℤ) : ZMod N.residueDegree)`.
@isnad1 id=eq.3h8v.s10.db2589eb7db5 from=translated src=- shape=83a27800 vocab=f11edb6d
-/
@[simp] theorem normQuotientEquivZMod_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      Multiplicative.ofAdd ((vG.val x : ℤ) : ZMod N.residueDegree) := by
  rw [normQuotientEquivZMod, MulEquiv.trans_apply,
    N.normQuotientEquivValueModResidueDegree_mk_ofAdd hϖG hϖH hzero x]
  rfl

/--
`normQuotientEquivZMod_uniformizer` satisfies the integer-power formula `N.normQuotientEquivZMod
hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) = Multiplicative.ofAdd ((n : ℤ) : ZMod
N.residueDegree)`.
@isnad1 id=eq.3h8v.s10.1085d92820d8 from=translated src=- shape=7e77e8a5 vocab=2ddbe331
-/
@[simp] theorem normQuotientEquivZMod_uniformizer_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree) := by
  rw [N.normQuotientEquivZMod_mk hϖG hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
`normQuotientEquivZMod_uniformizerClass` satisfies the integer-power formula
`N.normQuotientEquivZMod hϖG hϖH hzero ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree)`.
@isnad1 id=eq.3h8v.s10.56258391a152 from=translated src=- shape=337f3529 vocab=2ddbe331
-/
@[simp] theorem normQuotientEquivZMod_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree) := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    N.normQuotientEquivZMod_uniformizer_zpow hϖG hϖH hzero n]

/--
Establishes the identity `(N.normQuotientEquivZMod hϖG hϖH hzero).symm (Multiplicative.ofAdd ((n :
ℤ) : ZMod N.residueDegree)) = QuotientGroup.mk' N.normSubgroup (ϖG ^ n)`.
@isnad1 id=eq.3h8v.s10.c1a06ff0840a from=translated src=- shape=a4432dbf vocab=7154dc4c
-/
@[simp] theorem normQuotientEquivZMod_symm_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivZMod hϖG hϖH hzero).symm
        (Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) := by
  apply (N.normQuotientEquivZMod hϖG hϖH hzero).injective
  rw [MulEquiv.apply_symm_apply,
    N.normQuotientEquivZMod_uniformizer_zpow hϖG hϖH hzero n]

end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory
