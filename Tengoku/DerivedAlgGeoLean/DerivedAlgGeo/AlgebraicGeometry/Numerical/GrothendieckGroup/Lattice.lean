/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.EulerPairing
import Tengoku.Seed.LinearAlgebra.FreeModule.PID

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The numerical Grothendieck lattice

The numerical Grothendieck group is the quotient by the radical of the Euler pairing.  This
file makes that construction explicit from `NumericalVarietyData.chi₂` and records the precise
finiteness input needed before the quotient is a lattice.

The Euler pairing supplied by `NumericalVarietyData` is `ℚ`-valued.  Consequently the descended
pairing below is also `ℚ`-valued; no integrality statement is silently assumed.  The integral
object is its underlying finite free `ℤ`-module.

## Main results

* `NumericalVarietyData.leftRadical` and `NumericalVarietyData.rightRadical` are the two
  Euler radicals.
* `NumericalVarietyData.leftRadical_eq_rightRadical` identifies them when the Euler form
  is symmetric.
* `NumericalVarietyData.NumericalQuotient` is the quotient by the radical.
* `NumericalVarietyData.numericalPairing` is the descended, nondegenerate pairing.
* `NumericalQuotient` is finitely generated over `ℤ` whenever `N` is
  (`instFiniteNumericalQuotient`, from `Module.Finite.quotient`), and free
  whenever it is also torsion-free, by Mathlib's instance
  `Module.free_of_finite_type_torsion_free'`. The lattice structure is
  therefore Mathlib's `[Module.Finite ℤ _] [Module.Free ℤ _]`; the repository
  no longer carries a class for it.
* `K3.numericalPairing_mk_eq_neg_mukaiPairing` fixes the K3 sign convention.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

namespace NumericalVarietyData

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData n A N)

/-- The Euler pairing with its second argument packaged as an additive homomorphism.-/
noncomputable def eulerPairingRow (E : N) : N →+ ℚ :=
  AddMonoidHom.mk' (V.chi₂ E) (V.chi₂_add_right E)

/-- The Euler pairing as a biadditive homomorphism `N →+ (N →+ ℚ)`.-/
noncomputable def eulerPairing : N →+ (N →+ ℚ) :=
  AddMonoidHom.mk' (V.eulerPairingRow) fun E F => by
    ext G
    exact V.chi₂_add_left E F G

/-- The transposed Euler pairing as a biadditive homomorphism.-/
noncomputable def eulerPairingFlip : N →+ (N →+ ℚ) :=
  AddMonoidHom.mk' (fun F => AddMonoidHom.mk' (fun E => V.chi₂ E F)
    (fun E G => V.chi₂_add_left E G F)) fun E F => by
      ext G
      exact V.chi₂_add_right G E F

/-- Unbundling `eulerPairing` recovers the original numerical Euler form `chi₂`.
@isnad1 id=eq.0h6v.s8.9b62497c061d from=translated src=- shape=cef30d50 vocab=1838ccef
-/
@[simp]
theorem eulerPairing_apply (E F : N) : V.eulerPairing E F = V.chi₂ E F :=
  rfl

/--
@isnad1 id=eq.0h6v.s8.3661c0678568 from=translated src=- shape=f84781da vocab=1ebf8e99
-/
@[simp]
theorem eulerPairingFlip_apply (E F : N) :
    V.eulerPairingFlip E F = V.chi₂ F E :=
  rfl

/-- The left radical: classes pairing to zero against every class on the right.-/
noncomputable def leftRadical : Submodule ℤ N :=
  AddSubgroup.toIntSubmodule (V.eulerPairing).ker

/-- The right radical: classes pairing to zero against every class on the left.-/
noncomputable def rightRadical : Submodule ℤ N :=
  AddSubgroup.toIntSubmodule (V.eulerPairingFlip).ker

/-- Membership in the left radical is pointwise vanishing of the Euler pairing in the
second argument.
@isnad1 id=iff.0h5v.s6.d11c40f82d1c from=translated src=- shape=b6ea5be5 vocab=29b16738
-/
theorem mem_leftRadical_iff (E : N) :
    E ∈ V.leftRadical ↔ ∀ F : N, V.chi₂ E F = 0 := by
  rw [leftRadical]
  change E ∈ (V.eulerPairing).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h F
    simpa using DFunLike.congr_fun h F
  · intro h
    ext F
    simpa using h F

/-- Membership in the right radical is pointwise vanishing of the Euler pairing in the
first argument.
@isnad1 id=iff.0h5v.s6.40fc2dc392ed from=translated src=- shape=f7fd5613 vocab=5852bf93
-/
theorem mem_rightRadical_iff (F : N) :
    F ∈ V.rightRadical ↔ ∀ E : N, V.chi₂ E F = 0 := by
  rw [rightRadical]
  change F ∈ (V.eulerPairingFlip).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h E
    simpa using DFunLike.congr_fun h E
  · intro h
    ext E
    simpa using h E

/-- The symmetry hypothesis under which the project uses a single Euler radical.-/
def IsEulerPairingSymmetric : Prop :=
  ∀ E F : N, V.chi₂ E F = V.chi₂ F E

/-- Symmetry turns vanishing against every right argument into vanishing against every left
argument, so the two kernels used to define the numerical quotient coincide.
@isnad1 id=eq.1h4v.s6.66c4468f7af8 from=translated src=- shape=a3bc7d77 vocab=2a051021
-/
theorem leftRadical_eq_rightRadical (hSymm : IsEulerPairingSymmetric V) :
    V.leftRadical (N := N) = V.rightRadical (N := N) := by
  ext E
  rw [mem_leftRadical_iff, mem_rightRadical_iff]
  constructor
  · intro h F
    rw [hSymm F E]
    exact h F
  · intro h F
    rw [hSymm E F]
    exact h F

/-- The numerical Grothendieck quotient by the left Euler radical.

Under `IsEulerPairingSymmetric`, `leftRadical_eq_rightRadical` shows that this is equivalently
the quotient by the right radical.-/
abbrev NumericalQuotient := N ⧸ V.leftRadical

/-- Descend the right argument of the Euler pairing to the numerical quotient.-/
noncomputable def eulerPairingDescendRight
    (hSymm : IsEulerPairingSymmetric V) (E : N) :
    NumericalQuotient V →+ ℚ :=
  QuotientAddGroup.lift V.leftRadical.toAddSubgroup
    (V.eulerPairingRow E) <| by
    intro F hF
    rw [AddMonoidHom.mem_ker]
    change V.chi₂ E F = 0
    rw [hSymm E F]
    exact (V.mem_leftRadical_iff F).mp hF E

/-- Evaluating the one-sided descent on a quotient representative recovers `chi₂`.
@isnad1 id=eq.1h6v.s7.527bccfa0c95 from=translated src=- shape=9b0a0208 vocab=9d95744f
-/
@[simp]
theorem eulerPairingDescendRight_mk
    (hSymm : IsEulerPairingSymmetric V) (E F : N) :
    V.eulerPairingDescendRight hSymm E (Submodule.Quotient.mk F) =
      V.chi₂ E F :=
  rfl

/-- The Euler pairing with its right argument descended, still additive in the left argument.-/
noncomputable def eulerPairingToQuotient
    (hSymm : IsEulerPairingSymmetric V) :
    N →+ (NumericalQuotient V →+ ℚ) :=
  AddMonoidHom.mk' (V.eulerPairingDescendRight hSymm) fun E F => by
    ext q
    refine Submodule.Quotient.induction_on _ q ?_
    intro G
    exact V.chi₂_add_left E F G

/-- The left-additive one-sided descent still evaluates to `chi₂` on representatives.
@isnad1 id=eq.1h6v.s9.61eb6ab4cd93 from=translated src=- shape=928dfde8 vocab=1baf7853
-/
@[simp]
theorem eulerPairingToQuotient_mk
    (hSymm : IsEulerPairingSymmetric V) (E F : N) :
    V.eulerPairingToQuotient hSymm E (Submodule.Quotient.mk F) =
      V.chi₂ E F :=
  rfl

/-- The Euler pairing descended to the numerical quotient in both arguments.-/
noncomputable def numericalPairing
    (hSymm : IsEulerPairingSymmetric V) :
    NumericalQuotient V →+ (NumericalQuotient V →+ ℚ) :=
  QuotientAddGroup.lift V.leftRadical.toAddSubgroup
    (V.eulerPairingToQuotient hSymm) <| by
      intro E hE
      rw [AddMonoidHom.mem_ker]
      ext q
      refine Submodule.Quotient.induction_on _ q ?_
      intro F
      exact (V.mem_leftRadical_iff E).mp hE F

/-- The fully descended numerical pairing is computed by `chi₂` on representatives.
@isnad1 id=eq.1h6v.s10.8b115be6c07a from=translated src=- shape=d8d36b84 vocab=f7b16cd8
-/
@[simp]
theorem numericalPairing_mk
    (hSymm : IsEulerPairingSymmetric V) (E F : N) :
    V.numericalPairing hSymm (Submodule.Quotient.mk E) (Submodule.Quotient.mk F) =
      V.chi₂ E F :=
  rfl

/-- The descended pairing remains symmetric.
@isnad1 id=eq.1h6v.s10.079d34cf0ed1 from=translated src=- shape=687e920e vocab=9a0a8c31
-/
theorem numericalPairing_symm
    (hSymm : IsEulerPairingSymmetric V)
    (x y : NumericalQuotient V) :
    V.numericalPairing hSymm x y = V.numericalPairing hSymm y x := by
  refine Submodule.Quotient.induction_on _ x fun E => ?_
  refine Submodule.Quotient.induction_on _ y fun F => ?_
  exact hSymm E F

/-- The descended pairing has zero left radical, by construction.
@isnad1 id=eq.2h5v.s10.37fc868eb591 from=translated src=- shape=eb7f99ce vocab=9a0a8c31
-/
theorem numericalPairing_left_nondegenerate
    (hSymm : IsEulerPairingSymmetric V)
    (x : NumericalQuotient V)
    (hx : ∀ y : NumericalQuotient V, V.numericalPairing hSymm x y = 0) :
    x = 0 := by
  revert hx
  refine Submodule.Quotient.induction_on _ x fun E hx => ?_
  rw [Submodule.Quotient.mk_eq_zero, mem_leftRadical_iff]
  intro F
  simpa using hx (Submodule.Quotient.mk F)

/-- The descended pairing has zero right radical as well.
@isnad1 id=eq.2h5v.s10.fccbba015977 from=translated src=- shape=e69fd603 vocab=9a0a8c31
-/
theorem numericalPairing_right_nondegenerate
    (hSymm : IsEulerPairingSymmetric V)
    (y : NumericalQuotient V)
    (hy : ∀ x : NumericalQuotient V, V.numericalPairing hSymm x y = 0) :
    y = 0 := by
  apply V.numericalPairing_left_nondegenerate hSymm y
  intro x
  rw [V.numericalPairing_symm hSymm]
  exact hy x

/-- The kernel of the descended pairing is zero.
@isnad1 id=eq.1h4v.s8.27a8862b89a6 from=translated src=- shape=926418b9 vocab=f625ce79
-/
theorem numericalPairing_ker_eq_bot
    (hSymm : IsEulerPairingSymmetric V) :
    (V.numericalPairing hSymm).ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [AddSubgroup.mem_bot]
    apply V.numericalPairing_left_nondegenerate hSymm x
    intro y
    have hzero := AddMonoidHom.mem_ker.mp hx
    simpa using DFunLike.congr_fun hzero y
  · exact bot_le

end NumericalVarietyData

namespace K3

open NumericalVarietyData

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- A K3 Euler pairing satisfies the symmetry hypothesis used by the numerical quotient.
@isnad1 id=iseulerp.1h3v.s5.ddd798c0e4ad from=translated src=- shape=e41900a1 vocab=bc421d2d
-/
theorem isEulerPairingSymmetric (hK3 : IsK3 V) : IsEulerPairingSymmetric V :=
  fun E F => chi₂_comm V hK3 E F

/-- On a K3, the two Euler radicals agree.
@isnad1 id=eq.1h3v.s6.2a2d99f8fc2d from=translated src=- shape=07749ccf vocab=35a9f450
-/
theorem leftRadical_eq_rightRadical (hK3 : IsK3 V) :
    V.leftRadical = V.rightRadical :=
  NumericalVarietyData.leftRadical_eq_rightRadical V (isEulerPairingSymmetric V hK3)

/-- On representatives, the numerical quotient pairing is minus the Mukai pairing.

Thus quotienting and descending preserve exactly the sign convention fixed by
`chi₂_eq_neg_mukaiPairing`.
@isnad1 id=eq.1h5v.s10.cd6d8ec41b27 from=translated src=- shape=6c286fe9 vocab=5a3ee259
-/
theorem numericalPairing_mk_eq_neg_mukaiPairing (hK3 : IsK3 V) (E F : N) :
    V.numericalPairing (isEulerPairingSymmetric V hK3)
        (Submodule.Quotient.mk E) (Submodule.Quotient.mk F) =
      -mukaiPairing V E F := by
  rw [NumericalVarietyData.numericalPairing_mk, chi₂_eq_neg_mukaiPairing V hK3]

end K3

end AlgebraicGeometry.Numerical
