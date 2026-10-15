/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Tengoku.LeanPool.LeanPool.Kurosh.KuroshPathEndpoint

/-!
# Kurosh Kernel

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshKernelDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

/--
@isnad1 id=eq.0h4v.s10.430869ee97dc from=translated src=- shape=e3992104 vocab=0cc83db2
-/
theorem Internal.treeKuroshRootStabilizer_subsingleton {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ x : treeVertexStabilizer G H (rawBassSerreOrbitRoot G H), x = 1 := by
  intro x
  apply Subtype.ext
  have hx : (x.1 : FreeProduct G) • rawTreeRepresentative G H
      (rawBassSerreOrbitRoot G H) =
      rawTreeRepresentative G H (rawBassSerreOrbitRoot G H) := x.property
  rw [Internal.rawTreeRepresentative_root G H] at hx
  have hx' : (x.1 : FreeProduct G) = 1 :=
    (rawBassSerre_central_fixed_iff G 1 (x.1 : FreeProduct G)).mp hx
  have hxH : x.1 = (1 : H) := Subtype.ext hx'
  change x.1 = (1 : treeVertexStabilizer G H
    (rawBassSerreOrbitRoot G H)).1
  exact hxH

/--
@isnad1 id=eq.0h3v.s7.e6e47d93e7fe from=translated src=- shape=6a299f1a vocab=ffe16e61
-/
theorem Internal.treeDataGenerated_eq_top_for_kernel {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Internal.treeDataGenerated G H = ⊤ := by
  apply le_antisymm le_top
  intro h _
  let p := Internal.rawSpanningTreePath G
    (h.1 • RawBassSerreVertex.central (G := G) 1)
  let a := Internal.rawPathAlignmentGenerated G H p
  have horbit :
      actionOrbitMk H (RawBassSerreVertex G)
          (h.1 • RawBassSerreVertex.central (G := G) 1) =
        rawBassSerreOrbitRoot G H := by
    change actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • RawBassSerreVertex.central (G := G) 1) =
      actionOrbitMk H (RawBassSerreVertex G)
        (RawBassSerreVertex.central (G := G) 1)
    exact actionOrbitMk_smul H (RawBassSerreVertex G) h
      (RawBassSerreVertex.central (G := G) 1)
  have hrep : rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • RawBassSerreVertex.central (G := G) 1)) =
      RawBassSerreVertex.central (G := G) 1 := by
    rw [horbit]
    exact Internal.rawTreeRepresentative_root G H
  have hpath : h.1 • RawBassSerreVertex.central (G := G) 1 =
      a.1 • RawBassSerreVertex.central (G := G) 1 := by
    calc
      h.1 • RawBassSerreVertex.central (G := G) 1 = a.1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G)
              (h.1 • RawBassSerreVertex.central (G := G) 1)) := a.2.1
      _ = a.1 • RawBassSerreVertex.central (G := G) 1 :=
        congrArg (fun z => (a.1 : FreeProduct G) • z) hrep
  have hval : h.1 = a.1 := by
    change RawBassSerreVertex.central (G := G) ((h.1 : FreeProduct G) * 1) =
      RawBassSerreVertex.central (G := G) ((a.1 : FreeProduct G) * 1) at hpath
    injection hpath with hmul
    simpa only [mul_one] using hmul
  have heq : h = a.1 := Subtype.ext hval
  exact heq ▸ a.2.2

/--
@isnad1 id=or.0h4v.s8.0d64d4485fff from=translated src=- shape=cfaeb692 vocab=1a2e7da0
-/
theorem Internal.treeVertexStabilizer_central_or_factor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    (∃ g : FreeProduct G,
      rawTreeRepresentative G H a = RawBassSerreVertex.central g ∧
      treeVertexStabilizer G H a = ⊥) ∨
    (∃ (i : ι) (g : FreeProduct G),
      rawTreeRepresentative G H a =
        RawBassSerreVertex.factor i (factorCosetMk G i g) ∧
      treeVertexStabilizer G H a = intersectionFactorInH H i g) := by
  let r := rawTreeRepresentative G H a
  cases hr : r with
  | central g =>
      left
      refine ⟨g, hr, ?_⟩
      apply (Subgroup.eq_bot_iff_forall _).2
      intro x hx
      have hfix : (x.1 : FreeProduct G) • RawBassSerreVertex.central g =
          RawBassSerreVertex.central g := by
        change (x.1 : FreeProduct G) • r = r at hx
        rw [hr] at hx
        exact hx
      have hx' : (x.1 : FreeProduct G) = 1 :=
        (rawBassSerre_central_fixed_iff G g (x.1 : FreeProduct G)).mp hfix
      exact Subtype.ext hx'
  | factor i c =>
      right
      have hc : factorCosetMk G i (Quotient.out c) = c := by
        simp [factorCosetMk, rightCosetMk]
      have hrep : rawTreeRepresentative G H a =
          RawBassSerreVertex.factor i
            (factorCosetMk G i (Quotient.out c)) :=
        hr.trans (congrArg (RawBassSerreVertex.factor i) hc.symm)
      refine ⟨i, Quotient.out c, hrep, ?_⟩
      apply Subgroup.ext
      intro x
      constructor
      · intro hx
        change (x.1 : FreeProduct G) ∈ intersectionFactor H i
            (Quotient.out c)
        apply (rawBassSerre_factor_fixed_iff G H i (Quotient.out c) x).1
        change (x.1 : FreeProduct G) •
            rawTreeRepresentative G H a = rawTreeRepresentative G H a at hx
        simpa [hrep] using hx
      · intro hx
        change (x.1 : FreeProduct G) •
            rawTreeRepresentative G H a = rawTreeRepresentative G H a
        rw [hrep]
        apply (rawBassSerre_factor_fixed_iff G H i (Quotient.out c) x).2
        exact hx

end GraphCoveringTheory.Kurosh
