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
variable {N : Submodule ℤ W} {M : Submodule ℤ U} {ι : Type*}

/--
@isnad1 id=iseven.2h6v.s7.29100bc3a2ce from=translated src=- shape=261ee96f vocab=a9b01377
-/
theorem isEven_prod (hN : IsEven B N) (hM : IsEven C M) :
    IsEven (prodForm B C) (N.prod M) := by
  intro z hz
  obtain ⟨i, hi⟩ := hN z.1 hz.1
  obtain ⟨j, hj⟩ := hM z.2 hz.2
  refine ⟨i + j, ?_⟩
  rw [prodForm_apply, hi, hj]
  push_cast
  ring

/--
@isnad1 id=iseven.3h8v.s9.a646d33cd3d2 from=translated src=- shape=2bec5660 vocab=1c8d45ba
-/
theorem GlueSystem.glue_isEven (S : GlueSystem B C N M ι)
    (hN : IsEven B N) (hM : IsEven C M)
    (hdiag : ∀ i, ∃ k : ℤ, B (S.y i) (S.y i) + C (S.m i) (S.m i) = 2 * (k : ℚ)) :
    IsEven (prodForm B C) (glueLattice N M S.gen) := by
  refine isEven_sup_span (prodForm_isSymm S.symmB S.symmC) S.glue_isIntegral
    (isEven_prod hN hM) ?_
  rintro _ ⟨i, rfl⟩
  exact hdiag i

/--
@isnad1 id=and.15h10v.s11.026bd4b52344 from=translated src=- shape=aba17f31 vocab=a8e4a5cb
-/
theorem complete_even_glue [Fintype ι] [DecidableEq ι]
    (u : ι → W) (v : ι → U) (p : ι → ℤ)
    (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hlN : IsLattice ℚ N) (hlM : IsLattice ℚ M)
    (hiN : IsIntegral B N) (hiM : IsIntegral C M)
    (heN : IsEven B N) (heM : IsEven C M)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ (Set.range u))
    (hdM : C.dualSubmodule M = M ⊔ Submodule.span ℤ (Set.range v))
    (hpv : ∀ i, p i • v i ∈ M)
    (hcrossN : ∀ i j, i ≠ j → B (u i) (u j) ∈ (1 : Submodule ℤ ℚ))
    (hcrossM : ∀ i j, i ≠ j → C (v i) (v j) ∈ (1 : Submodule ℤ ℚ))
    (hdiag : ∀ i, ∃ k : ℤ, B (u i) (u i) + C (v i) (v i) = 2 * (k : ℚ))
    (hunit : ∀ i (a : ℤ), (a : ℚ) * B (u i) (u i) ∈ (1 : Submodule ℤ ℚ) → p i ∣ a) :
    IsLattice ℚ (glueLattice N M (fun i => (u i, v i))) ∧
      IsEven (prodForm B C) (glueLattice N M (fun i => (u i, v i))) ∧
      (prodForm B C).dualSubmodule (glueLattice N M (fun i => (u i, v i))) =
        glueLattice N M (fun i => (u i, v i)) := by
  have hdiagInt (i : ι) : B (u i) (u i) + C (v i) (v i) ∈ (1 : Submodule ℤ ℚ) := by
    obtain ⟨k, hk⟩ := hdiag i
    exact mem_one_iff.mpr ⟨2 * k, by rw [hk]; push_cast; rfl⟩
  let S : GlueSystem B C N M ι := {
    y := u
    m := v
    pr := p
    symmB := hsB
    symmC := hsC
    intN := hiN
    intM := hiM
    dualN := hdN
    dualM := hdM
    smul_mem := hpv
    crossW := hcrossN
    crossU := hcrossM
    diag := hdiagInt
    unit := by
      intro i a b hab
      apply hunit i (a - b)
      have heq : ((a - b : ℤ) : ℚ) * B (u i) (u i) =
          ((a : ℚ) * B (u i) (u i) + (b : ℚ) * C (v i) (v i)) -
          (b : ℚ) * (B (u i) (u i) + C (v i) (v i)) := by
        push_cast
        ring
      rw [heq]
      apply sub_mem hab
      simpa only [zsmul_eq_mul] using (1 : Submodule ℤ ℚ).smul_mem b (hdiagInt i) }
  exact ⟨S.glue_isLattice hlN hlM, S.glue_isEven heN heM hdiag, S.glue_dual_eq_self⟩

end SRG266.Lattice
