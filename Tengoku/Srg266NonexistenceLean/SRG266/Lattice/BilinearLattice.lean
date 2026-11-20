/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Algebra.Module.ZMod
import Tengoku.Seed.LinearAlgebra.BilinearForm.DualLattice
import Tengoku.Seed.LinearAlgebra.BilinearForm.Orthogonal
import Tengoku.Seed.LinearAlgebra.Dimension.Localization
import Tengoku.Seed.LinearAlgebra.Dimension.RankNullity
import Tengoku.Seed.LinearAlgebra.FreeModule.PID
import Tengoku.Seed.LinearAlgebra.Projection
import Tengoku.Seed.RingTheory.Localization.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Full lattices, integral forms, duality, and bounded torsion -/

namespace SRG266.Lattice

section RationalLattice

variable {R S W : Type*} [CommRing R] [Field S] [AddCommGroup W]
variable [Algebra R S] [Module R W] [Module S W] [IsScalarTower R S W]

structure IsLattice (S : Type*) [Field S] [Algebra R S] [Module S W]
    [IsScalarTower R S W] (N : Submodule R W) : Prop where
  /-- Finite generation over the integral coefficient ring.-/
  fg : N.FG
  /-- The lattice spans the ambient vector space.-/
  spans : Submodule.span S (N : Set W) = ⊤

variable (B : LinearMap.BilinForm S W)

def IsIntegral (N : Submodule R W) : Prop := N ≤ B.dualSubmodule N

/--
@isnad1 id=iff.0h5v.s8.9f625f42e248 from=translated src=- shape=7ccf4f61 vocab=5dba8225
-/
theorem integral_iff_le_dual {N : Submodule R W} :
    IsIntegral B N ↔ N ≤ B.dualSubmodule N := Iff.rfl

/--
@isnad1 id=iff.0h5v.s9.1bc4f0daa3a7 from=translated src=- shape=73976ed0 vocab=d10525a6
-/
theorem isIntegral_iff_forall {N : Submodule R W} :
    IsIntegral B N ↔ ∀ u ∈ N, ∀ v ∈ N, B u v ∈ (1 : Submodule R S) :=
  ⟨fun h _ hu v hv => h hu v hv, fun h _ hu v hv => h _ hu v hv⟩

end RationalLattice

section IntegerLattice

open Module

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable (B : LinearMap.BilinForm ℚ W)

/--
@isnad1 id=ex.1h2v.s6.0542f8c259aa from=translated src=- shape=0b86d628 vocab=59d1fa24
-/
theorem exists_basis_of_isLattice {N : Submodule ℤ W} (hN : IsLattice ℚ N) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ W), N = Submodule.span ℤ (Set.range b) := by
  classical
  have : Module.Finite ℤ N := Module.Finite.iff_fg.mpr hN.fg
  have hnzW : NoZeroSMulDivisors ℤ W := by
    refine ⟨fun {c x} h => ?_⟩
    rcases eq_or_ne c 0 with hc | hc
    · exact Or.inl hc
    · refine Or.inr ?_
      have hq : ((c : ℚ)) • x = 0 := by
        rw [Int.cast_smul_eq_zsmul ℚ c x]
        exact h
      exact (smul_eq_zero.mp hq).resolve_left (Int.cast_ne_zero.mpr hc)
  have hnzN : NoZeroSMulDivisors ℤ (N : Type _) :=
    Function.Injective.noZeroSMulDivisors (N.subtype) Subtype.val_injective rfl
      (fun _ _ => rfl)
  obtain ⟨n, b0⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := N)
  set v : Fin n → W := fun i => ((b0 i : N) : W) with hv
  have hspanN : Submodule.span ℤ (Set.range v) = N := by
    have hmap : Submodule.map N.subtype (Submodule.span ℤ (Set.range b0)) =
        Submodule.span ℤ (Set.range v) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hmap, b0.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hindepZ : LinearIndependent ℤ v :=
    b0.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hindep : LinearIndependent ℚ v :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hindepZ
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    refine top_unique ?_
    rw [← hN.spans, Submodule.span_le, ← hspanN]
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      exact Submodule.add_mem _ hy hz
    · intro a y _ hy
      have hcast : a • y = ((a : ℚ)) • y := by
        rw [← Int.cast_smul_eq_zsmul ℚ a y]
      rw [hcast]
      exact Submodule.smul_mem _ _ hy
  refine ⟨n, Basis.mk hindep (by rw [hspanQ]), ?_⟩
  rw [← hspanN]
  congr 1
  simp [Basis.coe_mk]

/--
@isnad1 id=eq.3h3v.s6.2a13f496376e from=translated src=- shape=3d09d68c vocab=c8dab979
-/
theorem dual_dual {N : Submodule ℤ W} (hN : IsLattice ℚ N)
    (hnd : B.Nondegenerate) (hsymm : B.IsSymm) :
    B.dualSubmodule (B.dualSubmodule N) = N := by
  obtain ⟨n, b, rfl⟩ := exists_basis_of_isLattice hN
  exact B.dualSubmodule_dualSubmodule_of_basis hnd hsymm b

/--
@isnad1 id=islattic.2h3v.s6.b6129de3dbeb from=translated src=- shape=0976022c vocab=b1976e25
-/
theorem dual_isLattice {N : Submodule ℤ W} (hN : IsLattice ℚ N)
    (hnd : B.Nondegenerate) :
    IsLattice ℚ (B.dualSubmodule N) := by
  classical
  obtain ⟨n, b, rfl⟩ := exists_basis_of_isLattice hN
  have : Module.Finite ℚ W := Module.Finite.of_basis b
  rw [B.dualSubmodule_span_of_basis hnd b]
  refine ⟨⟨Finset.image (B.dualBasis hnd b) Finset.univ, ?_⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · rw [Submodule.span_span_of_tower ℤ]
    exact (B.dualBasis hnd b).span_eq

end IntegerLattice

section BoundedTorsion

/--
@isnad1 id=finite.1h2v.s6.7c2027d846e6 from=translated src=- shape=ad859c0d vocab=a41ab4db
-/
theorem finite_of_nsmul_eq_zero {Q : Type*} [AddCommGroup Q] [Module.Finite ℤ Q]
    {n : ℕ} [NeZero n] (h : ∀ q : Q, n • q = 0) : Finite Q := by
  classical
  have : Module (ZMod n) Q := AddCommGroup.zmodModule h
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := Q)
  have hspan : Submodule.span (ZMod n) (S : Set Q) = ⊤ := by
    refine top_unique fun q _ => ?_
    have hq : q ∈ Submodule.span ℤ (S : Set Q) := by rw [hS]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · exact fun y hy => Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · exact fun y z _ _ hy hz => Submodule.add_mem _ hy hz
    · intro a y _ hy
      rw [← Int.cast_smul_eq_zsmul (ZMod n) a y]
      exact Submodule.smul_mem _ _ hy
  have : Module.Finite (ZMod n) Q := ⟨⟨S, hspan⟩⟩
  exact Module.finite_of_finite (ZMod n)

/--
@isnad1 id=eq.1h5v.s11.d4fb4eede83a from=translated src=- shape=b1178e07 vocab=98de4685
-/
theorem quotient_nsmul_eq_zero {W : Type*} [AddCommGroup W]
    {N P : Submodule ℤ W} {n : ℕ} (hsmul : ∀ y ∈ P, (n : ℤ) • y ∈ N)
    (q : P ⧸ N.comap P.subtype) : n • q = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  have hy := hsmul (y : W) y.2
  rwa [Nat.cast_smul_eq_nsmul ℤ] at hy

/--
@isnad1 id=finite.2h4v.s8.677f37da02f3 from=translated src=- shape=57cc6d37 vocab=90a9ec18
-/
theorem finite_quotient_of_nsmul_le {W : Type*} [AddCommGroup W]
    {N P : Submodule ℤ W} (hP : P.FG) {n : ℕ} [NeZero n]
    (hsmul : ∀ y ∈ P, (n : ℤ) • y ∈ N) :
    Finite (P ⧸ N.comap P.subtype) := by
  have : Module.Finite ℤ P := Module.Finite.iff_fg.mpr hP
  have : Module.Finite ℤ (P ⧸ N.comap P.subtype) := Module.Finite.quotient ℤ _
  exact finite_of_nsmul_eq_zero (n := n) (quotient_nsmul_eq_zero hsmul)

end BoundedTorsion

end SRG266.Lattice
