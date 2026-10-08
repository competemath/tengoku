/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Tengoku.Seed.Data.Finite.Sigma

/-!
# Existence of a rank function to natural numbers

In this file, we show that if `P : A.Pairing` is
a regular pairing of subcomplex `A` of a simplicial set `X`,
then there exists a rank function for `P` with values in `ℕ`.

-/

@[expose] public section

universe u

open Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable (P : A.Pairing)

instance (y : P.II) : Finite { x // P.AncestralRel x y } := by
  let T := { x : P.II // P.AncestralRel x y }
  let U := Σ (d : Fin (P.p y).1.dim), ⦋d⦌ ⟶ ⦋(P.p y).1.1.1.1⦌
  let ψ : U → X.S := fun ⟨d, f⟩ ↦ S.mk (X.map f.op (P.p y).1.simplex)
  have h (t : T) : ∃ u, ψ u = t.1.1.toS := by
    obtain ⟨f, _, hf⟩ := N.le_iff_exists_mono.1 t.2.2.le
    refine ⟨⟨⟨t.1.1.dim, ?_⟩, f⟩, ?_⟩
    · simpa using SSet.N.dim_lt_of_lt t.2.2
    · rwa [SSet.S.ext_iff]
  choose φ hφ using h
  apply Finite.of_injective φ
  intro t₁ t₂ h
  rw [Subtype.ext_iff, Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff, ← hφ, ← hφ, h]

section

variable {y : P.II} (hy : Acc P.AncestralRel y)

/-- Auxiliary definition for `SSet.Subcomplex.Pairing.Rank`. -/
noncomputable def rank' : ℕ :=
  Acc.recOn hy (fun y _ r ↦ ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)

/--
@isnad1 id=eq.1h4v.s7.20ce8ab9683a from=seed src=0 shape=cbf3a30b vocab=6c717c33
-/
lemma rank'_eq :
    P.rank' hy = ⨆ (x : { x // P.AncestralRel x y }), P.rank' (hy.inv x.2) + 1 := by
  change P.rank' (Acc.intro y fun _ => hy.inv) = _
  rfl

/--
@isnad1 id=lt.2h5v.s6.377d31f312f4 from=seed src=0 shape=39ebd64c vocab=948c9bc1
-/
lemma rank'_lt {x : P.II} (r : P.AncestralRel x y) :
    P.rank' (hy.inv r) < P.rank' hy := by
  rw [P.rank'_eq hy, ← Nat.add_one_le_iff]
  exact le_csSup (Finite.bddAbove_range _) ⟨⟨x, r⟩, rfl⟩

end

section IsRegular

variable [P.IsRegular]

/-- The rank function with values in `ℕ` relative to the well founded
ancestrality relation of a regular pairing. -/
noncomputable def rank (x : P.II) : ℕ :=
  P.rank' (P.wf.apply x)

variable {P} in
/--
@isnad1 id=lt.1h5v.s5.408c4eb8431c from=seed src=0 shape=6e06511b vocab=9b43bc85
-/
lemma rank_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank x < P.rank y :=
  P.rank'_lt _ h

/-- The canonical rank function with values in `ℕ` of a regular pairing. -/
noncomputable def rankFunction : P.RankFunction ℕ where
  rank := P.rank
  lt := P.rank_lt

instance : Nonempty (P.RankFunction ℕ) := ⟨P.rankFunction⟩

instance : Nonempty (P.WeakRankFunction ℕ) := ⟨P.rankFunction.toWeakRankFunction⟩

end IsRegular

/--
@isnad1 id=iff.0h3v.s4.0e05b9e32ed4 from=seed src=0 shape=8b6ce974 vocab=c176b72e
-/
lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

/--
@isnad1 id=iff.0h3v.s4.8eb6f1041684 from=seed src=0 shape=8b6ce974 vocab=bea813fe
-/
lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

end Pairing

namespace PairingCore

variable (P : A.PairingCore)

/--
@isnad1 id=iff.0h3v.s4.2f99b9fea623 from=seed src=0 shape=8b6ce974 vocab=f740cb80
-/
lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction ℕ) := by
  rw [← isRegular_pairing_iff, Pairing.isRegular_iff_nonempty_rankFunction]
  exact (P.rankFunctionEquiv ℕ).symm.nonempty_congr

/--
@isnad1 id=iff.0h3v.s4.8a7e96385f0a from=seed src=0 shape=8b6ce974 vocab=4d17237e
-/
lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction ℕ) := by
  rw [← isRegular_pairing_iff, Pairing.isRegular_iff_nonempty_weakRankFunction]
  exact (P.weakRankFunctionEquiv ℕ).symm.nonempty_congr

end PairingCore

end SSet.Subcomplex
