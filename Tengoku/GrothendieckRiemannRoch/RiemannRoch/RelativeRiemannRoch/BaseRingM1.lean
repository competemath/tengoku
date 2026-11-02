/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.KrullDimension.PID
import Tengoku.Seed.RingTheory.KrullDimension.Field
import Tengoku.Seed.RingTheory.PrincipalIdealDomain
import Tengoku.Seed.RingTheory.DedekindDomain.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M1: finite-dimensional base rings

`M1.FiniteDimBase R` : the Krull dimension of the (noetherian) base ring `R` is finite.
`M1.FiniteDimBase.d R : ℕ` is the dimension.
Instances: fields, PIDs, Dedekind domains; `M1.finiteDimBase_of_krullDimLE` for `Ring.KrullDimLE n R`.
-/

universe u

namespace M1

private theorem natCast_lt_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) < ⊤ :=
  WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)

/-- The base ring has finite Krull dimension.-/
class FiniteDimBase (R : Type u) [CommRing R] : Prop where
  /-- The Krull dimension is finite.-/
  krullDim_lt_top : ringKrullDim R < ⊤

/-- A ring of Krull dimension `≤ n` (`Ring.KrullDimLE n R`) has finite Krull dimension.  Not an
instance (the bound `n` is not inferable from the goal); use `FiniteDimBase.of_krullDimLE`.-/
theorem finiteDimBase_of_krullDimLE (R : Type u) [CommRing R] (n : ℕ) [Ring.KrullDimLE n R] :
    FiniteDimBase R :=
  ⟨lt_of_le_of_lt (Ring.krullDimLE_iff.1 inferInstance) (natCast_lt_top n)⟩

namespace FiniteDimBase

/-- Alias of `M1.finiteDimBase_of_krullDimLE`.-/
theorem of_krullDimLE (R : Type u) [CommRing R] (n : ℕ) [Ring.KrullDimLE n R] :
    FiniteDimBase R :=
  finiteDimBase_of_krullDimLE R n

/-- The Krull dimension of the base ring as a natural number.-/
noncomputable def d (R : Type u) [CommRing R] [FiniteDimBase R] : ℕ :=
  ((ringKrullDim R).unbotD 0).toNat

theorem ringKrullDim_le (R : Type u) [CommRing R] [FiniteDimBase R] :
    ringKrullDim R ≤ (d R : WithBot ℕ∞) := by
  have h := FiniteDimBase.krullDim_lt_top (R := R)
  unfold d
  cases hx : ringKrullDim R with
  | bot => exact bot_le
  | coe a =>
    rw [hx] at h
    have ha : a ≠ ⊤ := fun h' => by simp [h'] at h
    have : ((a.toNat : ℕ∞)) = a := ENat.natCast_toNat ha
    simp only [WithBot.unbotD_coe]
    exact_mod_cast this.ge

end FiniteDimBase
end M1
