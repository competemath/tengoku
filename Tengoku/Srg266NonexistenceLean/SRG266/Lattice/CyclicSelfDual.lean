/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U} {u : W} {v : U}

theorem cyclicGlueLattice_dual_eq_self (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hN : IsIntegral B N) (hM : IsIntegral C M)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ {u})
    (hdM : C.dualSubmodule M = M ⊔ Submodule.span ℤ {v})
    {p : ℤ} (hpv : p • v ∈ M)
    (hdiag : B u u + C v v ∈ (1 : Submodule ℤ ℚ))
    (hunit : ∀ a : ℤ, (a : ℚ) * B u u ∈ (1 : Submodule ℤ ℚ) → p ∣ a) :
    (prodForm B C).dualSubmodule (cyclicGlueLattice N M u v) =
      cyclicGlueLattice N M u v := by
  let S : GlueSystem B C N M Unit := {
    y := fun _ => u
    m := fun _ => v
    pr := fun _ => p
    symmB := hsB
    symmC := hsC
    intN := hN
    intM := hM
    dualN := by simpa using hdN
    dualM := by simpa using hdM
    smul_mem := fun _ => hpv
    crossW := fun i j hij => False.elim (hij (Subsingleton.elim i j))
    crossU := fun i j hij => False.elim (hij (Subsingleton.elim i j))
    diag := fun _ => hdiag
    unit := by
      intro _ a b hab
      apply hunit (a - b)
      have heq : ((a - b : ℤ) : ℚ) * B u u =
          ((a : ℚ) * B u u + (b : ℚ) * C v v) -
          (b : ℚ) * (B u u + C v v) := by
        push_cast
        ring
      rw [heq]
      apply sub_mem hab
      simpa only [zsmul_eq_mul] using (1 : Submodule ℤ ℚ).smul_mem b hdiag }
  have heq : glueLattice N M S.gen = cyclicGlueLattice N M u v := by
    change N.prod M ⊔ Submodule.span ℤ (Set.range (fun _ : Unit => (u, v))) =
      N.prod M ⊔ Submodule.span ℤ {(u, v)}
    rw [Set.range_const]
  rw [← heq]
  exact S.glue_dual_eq_self

theorem complete_even_cyclic_glue (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hlN : IsLattice ℚ N) (hlM : IsLattice ℚ M)
    (hiN : IsIntegral B N) (hiM : IsIntegral C M)
    (heN : IsEven B N) (heM : IsEven C M)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ {u})
    (hdM : C.dualSubmodule M = M ⊔ Submodule.span ℤ {v})
    {p : ℤ} (hpv : p • v ∈ M)
    (hdiag : ∃ k : ℤ, B u u + C v v = 2 * (k : ℚ))
    (hunit : ∀ a : ℤ, (a : ℚ) * B u u ∈ (1 : Submodule ℤ ℚ) → p ∣ a) :
    IsLattice ℚ (cyclicGlueLattice N M u v) ∧
      IsEven (prodForm B C) (cyclicGlueLattice N M u v) ∧
      (prodForm B C).dualSubmodule (cyclicGlueLattice N M u v) =
        cyclicGlueLattice N M u v := by
  have hd : B u u + C v v ∈ (1 : Submodule ℤ ℚ) := by
    obtain ⟨k, hk⟩ := hdiag
    exact mem_one_iff.mpr ⟨2 * k, by rw [hk]; push_cast; rfl⟩
  have hu : u ∈ B.dualSubmodule N := by
    rw [hdN]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hv : v ∈ C.dualSubmodule M := by
    rw [hdM]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact ⟨cyclicGlueLattice_isLattice hlN hlM,
    cyclicGlueLattice_isEven hsB hsC (cyclicGlueLattice_isIntegral hsB hsC hiN hiM hu hv hd)
      heN heM hdiag,
    cyclicGlueLattice_dual_eq_self hsB hsC hiN hiM hdN hdM hpv hd hunit⟩

omit [Module ℚ W] [AddCommGroup U] [Module ℚ U] in

theorem sup_span_smul_eq_of_bezout {p a b k : ℤ} (hp : p • u ∈ N)
    (hab : a * b + p * k = 1) :
    N ⊔ Submodule.span ℤ {a • u} = N ⊔ Submodule.span ℤ {u} := by
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro _ (rfl : _ = a • u)
    exact Submodule.mem_sup_right
      (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro z (hz : z = u)
    subst z
    have heq : (a * b + p * k) • u = b • (a • u) + k • (p • u) := by module
    rw [hab, one_smul] at heq
    have hmem : b • (a • u) + k • (p • u) ∈ N ⊔ Submodule.span ℤ {a • u} :=
      Submodule.add_mem _
      (Submodule.mem_sup_right (Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_left (Submodule.smul_mem _ k hp))
    exact (congrArg (fun w : W => w ∈ N ⊔ Submodule.span ℤ {a • u}) heq).mpr hmem

end SRG266.Lattice
