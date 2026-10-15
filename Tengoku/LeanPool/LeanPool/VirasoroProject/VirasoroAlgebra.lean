/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Tengoku.LeanPool.LeanPool.VirasoroProject.IsCentralExtension
public import Tengoku.LeanPool.LeanPool.VirasoroProject.VirasoroCocycle
public import Tengoku.LeanPool.LeanPool.VirasoroProject.ToMathlib.Algebra.Lie.Abelian
public import Tengoku

/-!
# The Virasoro algebra

This file defines the Virasoro algebra, an infinite-dimensional Lie algebra which is the unique
one-dimensional central extension of the Witt algebra.

(In two-dimensional conformal field theory (CFT), the Virasoro algebra describes the effects of
infinitesimal conformal transformations on the state space of the theory, or equivalently on its
space of local fields.)

## Main definitions

* `VirasoroAlgebra`: The Virasoro algebra.
* `VirasoroAlgebra.lgen`: The (commonly used) elements Lₙ, n ∈ ℤ, of the Virasoro algebra.
* `VirasoroAlgebra.cgen`: The (commonly used) central element C of the Virasoro algebra.
* `VirasoroAlgebra.basisLC`: The basis of the Virasoro algebra consisting of `Lₙ` (`n ∈ ℤ`) and `C`.
* `VirasoroAlgebra.ofCentral` and `VirasoroAlgebra.toWittAlgebra`: The maps in the short exact
  sequence 0 ⟶ 𝕜 ⟶ VirasoroAlgebra ⟶ WittAlgebra ⟶ 0.

## Main statements

* `VirasoroAlgebra.instLieAlgebra`: The Virasoro algebra is a Lie algebra.
* `VirasoroAlgebra.isCentralExtension`: The Virasoro algebra is a cetral extension of the
  Witt algebra.

## Implementation notes

The Virasoro algebra is defined as a central extension of the Witt algebra. (A more direct
definition based on defining a Lie bracket on a countably infinite dimensional vector space
would also be possible.)

## Tags

Virasoro algebra

-/

@[expose] public section

namespace VirasoroProject

-- `LieRing.ofAssociativeRing` is only a local instance in Mathlib; it provides the Lie ring
-- structure on the scalar field `𝕜`, which acts as the abelian centre of the central extension.
attribute [local instance 100] LieRing.ofAssociativeRing

section VirasoroAlgebra

/-! ### The Virasoro algebra -/

variable (𝕜 : Type*) [Field 𝕜]
variable [CharZero 𝕜]

/-- The Virasoro algebra. -/
def VirasoroAlgebra := LieTwoCocycle.CentralExtension (WittAlgebra.virasoroCocycle 𝕜)

namespace VirasoroAlgebra

/--
@isnad1 id=eq.2h3v.s6.65a8a9b9e039 from=translated src=- shape=d6c4bebd vocab=99c4dc6e
-/
lemma ext' {X Y : VirasoroAlgebra 𝕜} (h₁ : X.1 = Y.1) (h₂ : X.2 = Y.2) :
    X = Y :=
  LieTwoCocycle.CentralExtension.ext h₁ h₂

/-- The Virasoro algebra is a Lie ring. -/
noncomputable instance : LieRing (VirasoroAlgebra 𝕜) :=
  LieTwoCocycle.CentralExtension.instLieRing _

/-- The Virasoro algebra is a Lie algebra. -/
noncomputable instance : LieAlgebra 𝕜 (VirasoroAlgebra 𝕜) :=
  LieTwoCocycle.CentralExtension.instLieAlgebra _

variable {𝕜}

/-- The projection from Virasoro algebra to Witt algebra. -/
noncomputable def toWittAlgebra : VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ WittAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.proj (WittAlgebra.virasoroCocycle 𝕜)

variable (𝕜)

/-- The embedding of central elements to Virasoro algebra. -/
noncomputable def ofCentral : 𝕜 →ₗ⁅𝕜⁆ VirasoroAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.emb (WittAlgebra.virasoroCocycle 𝕜)

/--
@isnad1 id=eq.0h3v.s9.db4bedcf4be4 from=translated src=- shape=32eac9c7 vocab=ca2f034f
-/
lemma bracket_def' (X Y : VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆ = ⟨⁅toWittAlgebra X, toWittAlgebra Y⁆,
              (WittAlgebra.virasoroCocycle 𝕜) (toWittAlgebra X) (toWittAlgebra Y)⟩ := by
  rfl

/--
@isnad1 id=eq.0h3v.s8.1f3a16e8c6d0 from=translated src=- shape=e8c37eb9 vocab=a3df726a
-/
@[simp] lemma bracket_fst (X Y : VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆.1 = ⁅toWittAlgebra X, toWittAlgebra Y⁆ := rfl

/--
@isnad1 id=eq.0h3v.s9.a73fa39bbf78 from=translated src=- shape=b5f7ef5e vocab=2863b189
-/
@[simp] lemma bracket_snd (X Y : VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆.2 = (WittAlgebra.virasoroCocycle 𝕜) (toWittAlgebra X) (toWittAlgebra Y) := rfl

/--
@isnad1 id=eq.0h3v.s7.b09a7e6a13e1 from=translated src=- shape=32169279 vocab=6bfda5b8
-/
lemma add_def' (X Y : VirasoroAlgebra 𝕜) :
    X + Y = ⟨X.1 + Y.1, X.2 + Y.2⟩ := rfl

/--
@isnad1 id=eq.0h3v.s8.b1b2e411c4e0 from=translated src=- shape=7667a623 vocab=989ad067
-/
lemma smul_def' (c : 𝕜) (X : VirasoroAlgebra 𝕜) :
    c • X = ⟨c • X.1, c * X.2⟩ := rfl

/--
@isnad1 id=eq.0h3v.s7.8befa9066b23 from=translated src=- shape=fdb18a03 vocab=19d91a5b
-/
@[simp] lemma add_fst (X Y : VirasoroAlgebra 𝕜) :
    (X + Y).1 = X.1 + Y.1 := rfl

/--
@isnad1 id=eq.0h3v.s6.9f3af5f1cd30 from=translated src=- shape=3c01e2a3 vocab=c137f586
-/
@[simp] lemma add_snd (X Y : VirasoroAlgebra 𝕜) :
    (X + Y).2 = X.2 + Y.2 := rfl

/--
@isnad1 id=eq.0h3v.s8.345cbf87bba3 from=translated src=- shape=86edcb4a vocab=f2350e6c
-/
@[simp] lemma smul_fst (c : 𝕜) (X : VirasoroAlgebra 𝕜) :
    (c • X).1 = c • X.1 := rfl

/--
@isnad1 id=eq.0h3v.s7.f424e6199fb7 from=translated src=- shape=0c20f2e9 vocab=dbe7990a
-/
@[simp] lemma smul_snd (c : 𝕜) (X : VirasoroAlgebra 𝕜) :
    (c • X).2 = c * X.2 := rfl

/-- The Virasoro algebra is a central extension of the Witt algebra.
@isnad1 id=iscentra.0h1v.s6.5980f43a5484 from=translated src=- shape=763be3b9 vocab=b0f2758a
-/
theorem isCentralExtension : LieAlgebra.IsCentralExtension (ofCentral 𝕜) toWittAlgebra :=
  LieTwoCocycle.CentralExtension.isCentralExtension _

/-- The (commonly used) `Lₙ` elements of the Virasoro algebra, for `n ∈ ℤ`. -/
noncomputable def lgen (n : ℤ) : VirasoroAlgebra 𝕜 :=
  ⟨WittAlgebra.lgen 𝕜 n, 0⟩

/-- The (commonly used) `C` central element of the Virasoro algebra. -/
noncomputable def cgen : VirasoroAlgebra 𝕜 := ofCentral 𝕜 1

/--
@isnad1 id=eq.0h1v.s7.5eee4a7ceceb from=translated src=- shape=d595286d vocab=25d80697
-/
lemma cgen_eq_ofCentral_one : cgen 𝕜 = ofCentral 𝕜 1 := rfl

/--
@isnad1 id=eq.0h1v.s6.3343da148dab from=translated src=- shape=21da0a0f vocab=c361101c
-/
lemma cgen_eq' : cgen 𝕜 = ⟨0, 1⟩ := rfl

/--
@isnad1 id=eq.0h2v.s7.88f3dac44b11 from=translated src=- shape=353d352b vocab=c9857324
-/
lemma lgen_eq' (n : ℤ) : lgen 𝕜 n = ⟨WittAlgebra.lgen 𝕜 n, 0⟩ := rfl

/--
@isnad1 id=eq.0h2v.s8.67b3b27ba167 from=translated src=- shape=f3569008 vocab=87a4a3be
-/
@[simp] lemma ofCentral_apply (a : 𝕜) : ofCentral 𝕜 a = a • (cgen 𝕜) := by
  change (⟨0, a⟩ : VirasoroAlgebra 𝕜) = a • ⟨0, 1⟩
  aesop

/--
@isnad1 id=eq.0h1v.s7.aa0f39c0cb51 from=translated src=- shape=13f9393d vocab=7180eec7
-/
@[simp] lemma toWittAlgebra_cgen :
  toWittAlgebra (cgen 𝕜) = 0 := rfl

/--
@isnad1 id=eq.0h2v.s7.6a23da993e0b from=translated src=- shape=baa1e9ed vocab=9ce50e44
-/
@[simp] lemma toWittAlgebra_lgen (n : ℤ) :
  toWittAlgebra (lgen 𝕜 n) = WittAlgebra.lgen 𝕜 n := rfl

/--
@isnad1 id=eq.0h2v.s6.c48ea3fd53b6 from=translated src=- shape=d1c16bbb vocab=6b340935
-/
@[simp] lemma cgen_bracket (Z : VirasoroAlgebra 𝕜) :
    ⁅cgen 𝕜, Z⁆ = 0 :=
  (isCentralExtension 𝕜).central 1 Z

/--
@isnad1 id=eq.0h2v.s6.74c9d55de718 from=translated src=- shape=7f942e2a vocab=6b340935
-/
@[simp] lemma bracket_cgen (Z : VirasoroAlgebra 𝕜) :
    ⁅Z, cgen 𝕜⁆ = 0 := by
  simp [← lie_skew Z (cgen 𝕜)]

/--
@isnad1 id=eq.0h3v.s9.44f956d00357 from=translated src=- shape=c868e41a vocab=b54b4e90
-/
@[simp] lemma lgen_bracket (n m : ℤ) :
    ⁅lgen 𝕜 n, lgen 𝕜 m⁆
      = (n - m : 𝕜) • lgen 𝕜 (n + m) + if n + m = 0 then ((n^3 - n : 𝕜)/12) • cgen 𝕜 else 0 := by
  apply ext'
  · suffices (n - m : 𝕜) • WittAlgebra.lgen 𝕜 (n + m) =
        (n - m : 𝕜) • (lgen 𝕜 (n + m)).1
          + (if n + m = 0 then ((n ^ 3 - n : 𝕜) / 12) • cgen 𝕜 else 0).1 by
      simp_all
    split_ifs
    · rw [smul_fst]
      simp [lgen_eq', cgen_eq']
    · simp only [lgen_eq']
      change (n - m : 𝕜) • WittAlgebra.lgen 𝕜 (n + m) =
        (n - m : 𝕜) • WittAlgebra.lgen 𝕜 (n + m) + (0 : WittAlgebra 𝕜)
      rw [add_zero]
  · suffices (if n + m = 0 then (n ^ 3 - n : 𝕜) / 12 else 0) =
        (n - m : 𝕜) * (lgen 𝕜 (n + m)).2
          + (if n + m = 0 then ((n ^ 3 - n : 𝕜) / 12) • cgen 𝕜 else 0).2 by
      simpa only [bracket_snd, toWittAlgebra_lgen,
        WittAlgebra.virasoroCocycle_apply_lgen_lgen, add_snd, smul_snd] using this
    split_ifs
    · rw [smul_snd]
      simp [lgen_eq', cgen_eq']
    · simp only [lgen_eq']
      change (0 : 𝕜) = (n - m : 𝕜) * 0 + 0
      ring

/-- A section of the standard projection from the Virasoro algebra to the Witt algebra. -/
noncomputable def lsection : WittAlgebra 𝕜 →ₗ[𝕜] VirasoroAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.stdSection (WittAlgebra.virasoroCocycle 𝕜)

/--
@isnad1 id=eq.0h1v.s9.fe5d4ef942aa from=translated src=- shape=91c2c226 vocab=ab9aaa8b
-/
lemma lsection_prop : toWittAlgebra.toLinearMap ∘ₗ lsection 𝕜 = 1 := by
  ext X
  rfl

/--
@isnad1 id=eq.0h2v.s8.58c596bdad07 from=translated src=- shape=43cd07fa vocab=4f599ea0
-/
@[simp] lemma lsection_lgen (n : ℤ) :
    lsection 𝕜 (WittAlgebra.lgen 𝕜 n) = lgen 𝕜 n :=
  rfl

open Module in
/-- The most commonly used basis of the Virasoro algebra, consisting of `Lₙ` (`n ∈ ℤ`)
and the central element `C`. (Lean notation: `lgen _ n` and `cgen _`, respectively.) -/
noncomputable def basisLC : Basis (Option ℤ) 𝕜 (VirasoroAlgebra 𝕜) :=
  ((isCentralExtension 𝕜).basis (lsection 𝕜) (lsection_prop 𝕜)
        (Basis.singleton Unit 𝕜) (WittAlgebra.lgen 𝕜)).reindex
    { toFun uz := match uz with
        | Sum.inl _ => none
        | Sum.inr l => some l
      invFun oz := match oz with
        | none => Sum.inl ⟨⟩
        | some l => Sum.inr l
      left_inv uz := match uz with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      right_inv oz := match oz with
        | none => rfl
        | some _ => rfl }

/--
@isnad1 id=eq.0h2v.s7.7d254b3c4a95 from=translated src=- shape=4db5ca73 vocab=318e5d63
-/
@[simp] lemma basisLC_some (n : ℤ) :
    basisLC 𝕜 (some n) = lgen 𝕜 n := by
  unfold basisLC
  rw [Module.Basis.reindex_apply]
  change ((isCentralExtension 𝕜).basis (lsection 𝕜) (lsection_prop 𝕜)
    (Module.Basis.singleton Unit 𝕜) (WittAlgebra.lgen 𝕜)) (Sum.inr n) = lgen 𝕜 n
  rw [LieAlgebra.IsExtension.basis_eq_of_right, lsection_lgen]

/--
@isnad1 id=eq.0h1v.s7.a243b7251d3d from=translated src=- shape=085892c0 vocab=591f2554
-/
@[simp] lemma basisLC_none :
    basisLC 𝕜 none = cgen 𝕜 := by
  unfold basisLC
  rw [Module.Basis.reindex_apply]
  change ((isCentralExtension 𝕜).basis (lsection 𝕜) (lsection_prop 𝕜)
    (Module.Basis.singleton Unit 𝕜) (WittAlgebra.lgen 𝕜)) (Sum.inl PUnit.unit) = cgen 𝕜
  rw [LieAlgebra.IsExtension.basis_eq_of_left]
  simp

end VirasoroAlgebra -- namespace

end VirasoroAlgebra -- section

end VirasoroProject -- namespace
