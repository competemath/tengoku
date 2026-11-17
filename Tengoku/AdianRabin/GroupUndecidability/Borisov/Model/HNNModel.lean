import Tengoku.AdianRabin.GroupUndecidability.GroupTheory.CoprodILemmas
import Tengoku.Seed.GroupTheory.HNNExtension
import Tengoku.Seed.GroupTheory.FreeGroup.CyclicallyReduced
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two-stage HNN model for Borisov's four-relator group

The base is the free group on `d` and `e`.  Two injective substitutions encode
the power maps

```
  alpha : d ↦ d,  e ↦ e⁴,
  beta  : d ↦ d⁴, e ↦ e.
```

The first HNN extension adjoins `s₁` along these substitutions.  The second
adjoins `s₂` along the transported copies of the same associated subgroups.
The resulting group `Gamma3`, together with `d3`, `e3`, `s1_3`, and `s2_3`,
is the low-level semantic model used by the Borisov normal-form arguments.
The presentation-facing equivalence is constructed separately in
`GroupUndecidability.Borisov.Model.G0HNN`.
-/

open Function
open Monoid

namespace Undecidability.BorisovHNNModel

noncomputable section

/-! ## The rank-two free base and the two injective substitutions -/

abbrev Base := FreeGroup (Fin 2)

def d : Base := FreeGroup.of 0
def e : Base := FreeGroup.of 1

private def intFour : Multiplicative ℤ →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (4 * Multiplicative.toAdd z)
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp [mul_add]

private theorem intFour_injective : Injective intFour := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  simp only [intFour] at h'
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h'

private def cyclicFour : FreeGroup Unit →* FreeGroup Unit :=
  FreeGroup.mulEquivIntOfUnique.symm.toMonoidHom.comp
    (intFour.comp FreeGroup.mulEquivIntOfUnique.toMonoidHom)

private theorem cyclicFour_injective : Injective cyclicFour :=
  FreeGroup.mulEquivIntOfUnique.symm.injective.comp
    (intFour_injective.comp FreeGroup.mulEquivIntOfUnique.injective)

private theorem cyclicFour_generator :
    cyclicFour (FreeGroup.of ()) = FreeGroup.of () ^ 4 := by
  apply FreeGroup.mulEquivIntOfUnique.injective
  simp [cyclicFour, intFour, FreeGroup.mulEquivIntOfUnique,
    FreeGroup.equivIntOfUnique]

private def componentA : (i : Fin 2) → FreeGroup Unit →* FreeGroup Unit
  | 0 => MonoidHom.id _
  | 1 => cyclicFour

private def componentB : (i : Fin 2) → FreeGroup Unit →* FreeGroup Unit
  | 0 => cyclicFour
  | 1 => MonoidHom.id _

private theorem componentA_injective (i : Fin 2) : Injective (componentA i) := by
  fin_cases i
  · exact Function.injective_id
  · exact cyclicFour_injective

private theorem componentB_injective (i : Fin 2) : Injective (componentB i) := by
  fin_cases i
  · exact cyclicFour_injective
  · exact Function.injective_id

private def freeProductSubstitution
    (f : (i : Fin 2) → FreeGroup Unit →* FreeGroup Unit) : Base →* Base :=
  freeGroupEquivCoprodI.symm.toMonoidHom.comp
    ((CoprodI.familyMap f).comp freeGroupEquivCoprodI.toMonoidHom)

def alpha : Base →* Base := freeProductSubstitution componentA
def beta : Base →* Base := freeProductSubstitution componentB

/--
@isnad1 id=injectiv.0h0v.s6.41bfecad1f00 from=translated src=- shape=7f20522c vocab=c42ed3ea
-/
theorem alpha_injective : Injective alpha :=
  freeGroupEquivCoprodI.symm.injective.comp
    ((CoprodI.familyMap_injective componentA componentA_injective).comp
      freeGroupEquivCoprodI.injective)

/--
@isnad1 id=injectiv.0h0v.s6.461f248b31c3 from=translated src=- shape=7f20522c vocab=01366371
-/
theorem beta_injective : Injective beta :=
  freeGroupEquivCoprodI.symm.injective.comp
    ((CoprodI.familyMap_injective componentB componentB_injective).comp
      freeGroupEquivCoprodI.injective)

/--
@isnad1 id=eq.0h0v.s6.5c68737f96c5 from=translated src=- shape=9bb9467d vocab=a87ee1af
-/
@[simp] theorem alpha_d : alpha d = d := by
  simp [alpha, d, freeProductSubstitution, componentA, CoprodI.familyMap]

/--
@isnad1 id=eq.0h0v.s6.1ae67e040436 from=translated src=- shape=1bccbf1c vocab=72f32646
-/
@[simp] theorem alpha_e : alpha e = e ^ 4 := by
  simp [alpha, e, freeProductSubstitution, componentA, cyclicFour_generator,
    CoprodI.familyMap]

/--
@isnad1 id=eq.0h0v.s6.c8e616b08efa from=translated src=- shape=1bccbf1c vocab=238db54d
-/
@[simp] theorem beta_d : beta d = d ^ 4 := by
  simp [beta, d, freeProductSubstitution, componentB, cyclicFour_generator,
    CoprodI.familyMap]

/--
@isnad1 id=eq.0h0v.s6.907d99d5fd55 from=translated src=- shape=9bb9467d vocab=bddb69ab
-/
@[simp] theorem beta_e : beta e = e := by
  simp [beta, e, freeProductSubstitution, componentB, CoprodI.familyMap]

/--
@isnad1 id=eq.0h0v.s9.4cd495de1194 from=translated src=- shape=e341614f vocab=6115de28
-/
theorem alpha_eq_lift : alpha = FreeGroup.lift ![d, e ^ 4] := by
  ext i
  fin_cases i
  · simpa [d] using alpha_d
  · simpa [e] using alpha_e

/--
@isnad1 id=eq.0h0v.s9.bad3cf4ab151 from=translated src=- shape=dbb92a8e vocab=c977cedb
-/
theorem beta_eq_lift : beta = FreeGroup.lift ![d ^ 4, e] := by
  ext i
  fin_cases i
  · simpa [d] using beta_d
  · simpa [e] using beta_e

/-! ## The first HNN extension, adjoining `s₁` -/

abbrev A0 : Subgroup Base := alpha.range
abbrev B0 : Subgroup Base := beta.range

noncomputable def inA0 : Base ≃* A0 := MonoidHom.ofInjective alpha_injective
noncomputable def inB0 : Base ≃* B0 := MonoidHom.ofInjective beta_injective

noncomputable def phi0 : A0 ≃* B0 :=
  inA0.symm.trans inB0

/--
@isnad1 id=eq.0h1v.s9.5dbc53fe6637 from=translated src=- shape=ebc22338 vocab=ab749cd1
-/
@[simp] theorem phi0_inA0 (x : Base) : phi0 (inA0 x) = inB0 x := by
  simp [phi0]

/--
@isnad1 id=eq.0h1v.s8.a4b96e77afc6 from=translated src=- shape=84ae1b51 vocab=6927fac6
-/
@[simp] theorem coe_inA0 (x : Base) : (inA0 x : Base) = alpha x :=
  MonoidHom.ofInjective_apply alpha_injective

/--
@isnad1 id=eq.0h1v.s8.bfd1cbb6b9c6 from=translated src=- shape=84ae1b51 vocab=9dcda930
-/
@[simp] theorem coe_inB0 (x : Base) : (inB0 x : Base) = beta x :=
  MonoidHom.ofInjective_apply beta_injective

abbrev Stage1 := HNNExtension Base A0 B0 phi0

def of0 : Base →* Stage1 := HNNExtension.of
def s1 : Stage1 := HNNExtension.t

/--
@isnad1 id=injectiv.0h0v.s6.28785bfa4a45 from=translated src=- shape=f51e303a vocab=fc0deddf
-/
theorem of0_injective : Injective of0 := HNNExtension.of_injective phi0

/--
@isnad1 id=eq.0h0v.s7.0d7f865db4ce from=translated src=- shape=a6819032 vocab=56e320ee
-/
theorem stage1_s1_mul_d : s1 * of0 d = of0 (d ^ 4) * s1 := by
  simpa [s1, of0] using
    (HNNExtension.t_mul_of (φ := phi0) (inA0 d))

/--
@isnad1 id=eq.0h0v.s7.e1b2e2bc345e from=translated src=- shape=d5cb5abd vocab=f251b585
-/
theorem stage1_s1_mul_e_four : s1 * of0 (e ^ 4) = of0 e * s1 := by
  simpa [s1, of0] using
    (HNNExtension.t_mul_of (φ := phi0) (inA0 e))

/--
@isnad1 id=eq.0h0v.s7.cc0da717d104 from=translated src=- shape=13b36de3 vocab=56e320ee
-/
theorem stage1_d_four_mul_s1 : of0 (d ^ 4) * s1 = s1 * of0 d :=
  stage1_s1_mul_d.symm

/--
@isnad1 id=eq.0h0v.s7.5b5e06b2ad7a from=translated src=- shape=8ff96385 vocab=f251b585
-/
theorem stage1_e_mul_s1 : of0 e * s1 = s1 * of0 (e ^ 4) :=
  stage1_s1_mul_e_four.symm

/-! ## The second HNN extension

This adjoins `s₂` to a transported copy of the same pair of associated
subgroups.
-/

abbrev A1 : Subgroup Stage1 := A0.map of0
abbrev B1 : Subgroup Stage1 := B0.map of0

noncomputable def inA1 : A0 ≃* A1 :=
  A0.equivMapOfInjective of0 of0_injective

noncomputable def inB1 : B0 ≃* B1 :=
  B0.equivMapOfInjective of0 of0_injective

noncomputable def phi1 : A1 ≃* B1 :=
  inA1.symm.trans (phi0.trans inB1)

/--
@isnad1 id=eq.0h1v.s11.c8dddc3c3315 from=translated src=- shape=8c50f2e9 vocab=b0e22a13
-/
@[simp] theorem phi1_inA1 (a : A0) : phi1 (inA1 a) = inB1 (phi0 a) := by
  simp [phi1]

/--
@isnad1 id=eq.0h1v.s9.9491d6e9efd5 from=translated src=- shape=4c07690f vocab=69d0032e
-/
@[simp] theorem coe_inA1 (a : A0) : (inA1 a : Stage1) = of0 a :=
  Subgroup.coe_equivMapOfInjective_apply A0 of0 of0_injective a

/--
@isnad1 id=eq.0h1v.s9.1890ff4fa4c1 from=translated src=- shape=4c07690f vocab=9f4afc58
-/
@[simp] theorem coe_inB1 (b : B0) : (inB1 b : Stage1) = of0 b :=
  Subgroup.coe_equivMapOfInjective_apply B0 of0 of0_injective b

abbrev Gamma3 := HNNExtension Stage1 A1 B1 phi1

def of1 : Stage1 →* Gamma3 := HNNExtension.of
def d3 : Gamma3 := of1 (of0 d)
def e3 : Gamma3 := of1 (of0 e)
def s1_3 : Gamma3 := of1 s1
def s2_3 : Gamma3 := HNNExtension.t

/--
@isnad1 id=injectiv.0h0v.s6.d878e62d7d0f from=translated src=- shape=f51e303a vocab=42380272
-/
theorem of1_injective : Injective of1 := HNNExtension.of_injective phi1

/--
@isnad1 id=injectiv.0h0v.s7.51bf95c2bbe9 from=translated src=- shape=5c6080d0 vocab=01642fbf
-/
theorem baseEmbedding_injective : Injective (of1.comp of0) :=
  of1_injective.comp of0_injective

/--
@isnad1 id=eq.0h0v.s6.0f00073441ae from=translated src=- shape=297c55a4 vocab=fcfb2010
-/
theorem gamma3_d_four_mul_s1 : d3 ^ 4 * s1_3 = s1_3 * d3 := by
  simpa [d3, s1_3, map_pow] using congrArg of1 stage1_d_four_mul_s1

/--
@isnad1 id=eq.0h0v.s6.52ba7ce444f4 from=translated src=- shape=3c00f348 vocab=70009c4b
-/
theorem gamma3_e_mul_s1 : e3 * s1_3 = s1_3 * e3 ^ 4 := by
  simpa [e3, s1_3, map_pow] using congrArg of1 stage1_e_mul_s1

/--
@isnad1 id=eq.0h0v.s6.5d09fd0cfbed from=translated src=- shape=7661594d vocab=06778e63
-/
theorem gamma3_s2_mul_d : s2_3 * d3 = d3 ^ 4 * s2_3 := by
  simpa [s2_3, d3, of1] using
    (HNNExtension.t_mul_of (φ := phi1) (inA1 (inA0 d)))

/--
@isnad1 id=eq.0h0v.s6.f1ab3cd20c54 from=translated src=- shape=79880926 vocab=6c10c3ef
-/
theorem gamma3_s2_mul_e_four : s2_3 * e3 ^ 4 = e3 * s2_3 := by
  simpa [s2_3, e3, of1, map_pow] using
    (HNNExtension.t_mul_of (φ := phi1) (inA1 (inA0 e)))

/--
@isnad1 id=eq.0h0v.s6.bba787bc8224 from=translated src=- shape=297c55a4 vocab=06778e63
-/
theorem gamma3_d_four_mul_s2 : d3 ^ 4 * s2_3 = s2_3 * d3 :=
  gamma3_s2_mul_d.symm

/--
@isnad1 id=eq.0h0v.s6.dcf11ebf8adf from=translated src=- shape=3c00f348 vocab=6c10c3ef
-/
theorem gamma3_e_mul_s2 : e3 * s2_3 = s2_3 * e3 ^ 4 :=
  gamma3_s2_mul_e_four.symm

end
end Undecidability.BorisovHNNModel
