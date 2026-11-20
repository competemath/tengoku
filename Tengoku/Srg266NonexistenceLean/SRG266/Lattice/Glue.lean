/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Discriminant
import Tengoku.Seed.RingTheory.Finiteness.Prod
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

section RightIntegral

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

def rightIntegral (F : LinearMap.BilinForm ℚ X) (z : X) : Submodule ℤ X where
  carrier := {w | F z w ∈ (1 : Submodule ℤ ℚ)}
  add_mem' {a b} ha hb := by
    show F z (a + b) ∈ (1 : Submodule ℤ ℚ)
    rw [map_add]
    exact add_mem ha hb
  zero_mem' := by
    show F z 0 ∈ (1 : Submodule ℤ ℚ)
    rw [map_zero]
    exact zero_mem _
  smul_mem' c w hw := by
    show F z (c • w) ∈ (1 : Submodule ℤ ℚ)
    rw [map_zsmul]
    exact Submodule.smul_mem _ _ (hw : F z w ∈ (1 : Submodule ℤ ℚ))

/--
@isnad1 id=iff.0h4v.s8.cc6a95fa3921 from=translated src=- shape=440ff81d vocab=0492cb5b
-/
theorem mem_rightIntegral {F : LinearMap.BilinForm ℚ X} {z w : X} :
    w ∈ rightIntegral F z ↔ F z w ∈ (1 : Submodule ℤ ℚ) := Iff.rfl

/--
@isnad1 id=isintegr.4h4v.s9.525c6b7e738e from=translated src=- shape=c68c129a vocab=2309acda
-/
theorem isIntegral_sup_span {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    {N : Submodule ℤ X} {s : Set X} (hN : IsIntegral F N)
    (hNs : ∀ z ∈ N, ∀ w ∈ s, F z w ∈ (1 : Submodule ℤ ℚ))
    (hss : ∀ z ∈ s, ∀ w ∈ s, F z w ∈ (1 : Submodule ℤ ℚ)) :
    IsIntegral F (N ⊔ Submodule.span ℤ s) := by
  have hA : ∀ z ∈ N, N ⊔ Submodule.span ℤ s ≤ rightIntegral F z := by
    intro z hz
    refine sup_le (fun w hw => ?_) (Submodule.span_le.mpr fun w hw => ?_)
    · exact mem_rightIntegral.mpr (hN hz w hw)
    · exact mem_rightIntegral.mpr (hNs z hz w hw)
  have hB : ∀ z ∈ s, N ⊔ Submodule.span ℤ s ≤ rightIntegral F z := by
    intro z hz
    refine sup_le (fun w hw => ?_) (Submodule.span_le.mpr fun w hw => ?_)
    · refine mem_rightIntegral.mpr ?_
      rw [hsymm.eq z w]
      exact hNs w hw z hz
    · exact mem_rightIntegral.mpr (hss z hz w hw)
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr fun z hz => ?_)
  · exact fun w hw => hA z hz hw
  · exact fun w hw => hB z hz hw

/--
@isnad1 id=mem.6h7v.s9.8181e44ef9dd from=translated src=- shape=4ad4136c vocab=e2b21167
-/
theorem inner_mem_one_of_coprime {F : LinearMap.BilinForm ℚ X} {P : Submodule ℤ X}
    (hsymm : F.IsSymm) {a b : ℤ} (hab : IsCoprime a b) {y z : X}
    (hy : y ∈ F.dualSubmodule P) (hya : a • y ∈ P)
    (hz : z ∈ F.dualSubmodule P) (hzb : b • z ∈ P) :
    F y z ∈ (1 : Submodule ℤ ℚ) := by
  refine mem_one_of_coprime hab ?_ ?_
  · have hcalc : ((a : ℚ)) * F y z = F z (a • y) := by
      rw [map_zsmul, zsmul_eq_mul, hsymm.eq z y]
    rw [hcalc]
    exact hz _ hya
  · have hcalc : ((b : ℚ)) * F y z = F y (b • z) := by
      rw [map_zsmul, zsmul_eq_mul]
    rw [hcalc]
    exact hy _ hzb

end RightIntegral

section ProdForm

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

def prodForm (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U) :
    LinearMap.BilinForm ℚ (W × U) :=
  B.compl₁₂ (LinearMap.fst ℚ W U) (LinearMap.fst ℚ W U) +
    C.compl₁₂ (LinearMap.snd ℚ W U) (LinearMap.snd ℚ W U)

/--
@isnad1 id=eq.0h6v.s9.31edf98b9035 from=translated src=- shape=13bb05dd vocab=a7f6e2d5
-/
@[simp]
theorem prodForm_apply (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (z w : W × U) : prodForm B C z w = B z.1 w.1 + C z.2 w.2 := rfl

/--
@isnad1 id=issymm.2h4v.s6.da936e29ad9b from=translated src=- shape=4d424f4d vocab=608b6ba7
-/
theorem prodForm_isSymm {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
    (hB : B.IsSymm) (hC : C.IsSymm) : (prodForm B C).IsSymm :=
  ⟨fun z w => by rw [prodForm_apply, prodForm_apply, hB.eq z.1 w.1, hC.eq z.2 w.2]⟩

/--
@isnad1 id=lt.3h5v.s10.2a5fb2d04cc7 from=translated src=- shape=0fd5852e vocab=848d4191
-/
theorem prodForm_posDef {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
    (hB : ∀ v : W, v ≠ 0 → 0 < B v v) (hC : ∀ v : U, v ≠ 0 → 0 < C v v) :
    ∀ z : W × U, z ≠ 0 → 0 < prodForm B C z z := by
  intro z hz
  have hB0 : 0 ≤ B z.1 z.1 := by
    rcases eq_or_ne z.1 0 with h | h
    · rw [h, map_zero]
    · exact (hB z.1 h).le
  have hC0 : 0 ≤ C z.2 z.2 := by
    rcases eq_or_ne z.2 0 with h | h
    · rw [h, map_zero]
    · exact (hC z.2 h).le
  rw [prodForm_apply]
  rcases eq_or_ne z.1 0 with h1 | h1
  · have h2 : z.2 ≠ 0 := by
      intro h2
      exact hz (Prod.ext h1 h2)
    exact add_pos_of_nonneg_of_pos hB0 (hC z.2 h2)
  · exact add_pos_of_pos_of_nonneg (hB z.1 h1) hC0

/--
@isnad1 id=le.1h3v.s9.2daba0817efc from=translated src=- shape=11c31b62 vocab=bb105ecc
-/
theorem ratNonneg_of_posDef {X : Type*} [AddCommGroup X] [Module ℚ X]
    {F : LinearMap.BilinForm ℚ X} (hpd : ∀ v : X, v ≠ 0 → 0 < F v v) (v : X) :
    0 ≤ F v v := by
  rcases eq_or_ne v 0 with rfl | h
  · rw [map_zero]
  · exact (hpd v h).le

/--
@isnad1 id=nondegen.2h2v.s8.753908087cf4 from=translated src=- shape=4bb86b23 vocab=d686df70
-/
theorem nondegenerate_of_posDef {X : Type*} [AddCommGroup X] [Module ℚ X]
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    (hpd : ∀ v : X, v ≠ 0 → 0 < F v v) : F.Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff' F (ratNonneg_of_posDef hpd)
    (LinearMap.BilinForm.isSymm_iff.mp hsymm)).mpr hpd

/--
@isnad1 id=eq.0h6v.s7.bd786facc95c from=translated src=- shape=94f4c996 vocab=fc8c4a6a
-/
theorem dualSubmodule_prodForm (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (N : Submodule ℤ W) (M : Submodule ℤ U) :
    (prodForm B C).dualSubmodule (N.prod M) =
      (B.dualSubmodule N).prod (C.dualSubmodule M) := by
  ext z
  constructor
  · intro h
    refine Submodule.mem_prod.mpr ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hmem := h (y, 0) (Submodule.mem_prod.mpr ⟨hy, M.zero_mem⟩)
      simpa using hmem
    · have hmem := h (0, y) (Submodule.mem_prod.mpr ⟨N.zero_mem, hy⟩)
      simpa using hmem
  · intro h w hw
    obtain ⟨h1, h2⟩ := Submodule.mem_prod.mp h
    obtain ⟨hw1, hw2⟩ := Submodule.mem_prod.mp hw
    rw [prodForm_apply]
    exact add_mem (h1 w.1 hw1) (h2 w.2 hw2)

/--
@isnad1 id=isintegr.2h6v.s7.53a35bd1a0f3 from=translated src=- shape=6cb00f54 vocab=3dec1273
-/
theorem isIntegral_prod {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
    {N : Submodule ℤ W} {M : Submodule ℤ U} (hN : IsIntegral B N) (hM : IsIntegral C M) :
    IsIntegral (prodForm B C) (N.prod M) := by
  rw [IsIntegral, dualSubmodule_prodForm]
  exact Submodule.prod_mono hN hM

/--
@isnad1 id=islattic.2h4v.s7.43cd1ba3d52a from=translated src=- shape=996669db vocab=01b87d1f
-/
theorem isLattice_prod {N : Submodule ℤ W} {M : Submodule ℤ U}
    (hN : IsLattice ℚ N) (hM : IsLattice ℚ M) : IsLattice ℚ (N.prod M) := by
  refine ⟨Submodule.FG.prod hN.fg hM.fg, ?_⟩
  have h1 : LinearMap.range (LinearMap.inl ℚ W U) ≤
      Submodule.span ℚ ((N.prod M : Submodule ℤ (W × U)) : Set (W × U)) := by
    rw [← Submodule.map_top, ← hN.spans, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.mem_prod.mpr ⟨hx, M.zero_mem⟩
  have h2 : LinearMap.range (LinearMap.inr ℚ W U) ≤
      Submodule.span ℚ ((N.prod M : Submodule ℤ (W × U)) : Set (W × U)) := by
    rw [← Submodule.map_top, ← hM.spans, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.mem_prod.mpr ⟨N.zero_mem, hx⟩
  refine top_unique fun z _ => ?_
  have hz : z = (z.1, (0 : U)) + ((0 : W), z.2) := by
    apply Prod.ext <;> simp
  rw [hz]
  exact add_mem (h1 ⟨z.1, rfl⟩) (h2 ⟨z.2, rfl⟩)

end ProdForm

section Glue

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

def glueLattice {ι : Type*} (N : Submodule ℤ W) (M : Submodule ℤ U) (g : ι → W × U) :
    Submodule ℤ (W × U) :=
  N.prod M ⊔ Submodule.span ℤ (Set.range g)

omit [Module ℚ W] [Module ℚ U] in
/--
@isnad1 id=mem.0h7v.s7.be757aad2bd6 from=translated src=- shape=c7776800 vocab=ada2de6c
-/
theorem gen_mem_glueLattice {ι : Type*} {N : Submodule ℤ W} {M : Submodule ℤ U}
    {g : ι → W × U} (i : ι) : g i ∈ glueLattice N M g :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

omit [Module ℚ W] [Module ℚ U] in
/--
@isnad1 id=le.0h6v.s7.be4c3b7e4aba from=translated src=- shape=504160d7 vocab=e5d19da9
-/
theorem prod_le_glueLattice {ι : Type*} {N : Submodule ℤ W} {M : Submodule ℤ U}
    {g : ι → W × U} : N.prod M ≤ glueLattice N M g := le_sup_left

def inclLeft {ι : Type*} (N : Submodule ℤ W) (M : Submodule ℤ U) (g : ι → W × U) :
    N →ₗ[ℤ] glueLattice N M g where
  toFun x := ⟨((x : W), 0),
    prod_le_glueLattice (Submodule.mem_prod.mpr ⟨x.2, M.zero_mem⟩)⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    apply Prod.ext <;> simp

omit [Module ℚ W] [Module ℚ U] in
/--
@isnad1 id=eq.0h7v.s10.f837bdf38def from=translated src=- shape=e339ff73 vocab=3b004d0f
-/
@[simp]
theorem inclLeft_coe {ι : Type*} (N : Submodule ℤ W) (M : Submodule ℤ U) (g : ι → W × U)
    (x : N) : ((inclLeft N M g x : glueLattice N M g) : W × U) = ((x : W), 0) := rfl

omit [Module ℚ W] [Module ℚ U] in
/--
@isnad1 id=injectiv.0h6v.s10.bb2035babe2c from=translated src=- shape=104b7ed0 vocab=bfe2b54c
-/
theorem inclLeft_injective {ι : Type*} (N : Submodule ℤ W) (M : Submodule ℤ U)
    (g : ι → W × U) : Function.Injective (inclLeft N M g) := by
  intro x y hxy
  have h := congrArg (fun z => ((z : W × U)).1) (Subtype.ext_iff.mp hxy)
  exact Subtype.ext h

structure GlueSystem (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (N : Submodule ℤ W) (M : Submodule ℤ U) (ι : Type*) where

  y : ι → W

  m : ι → U

  pr : ι → ℤ

  symmB : B.IsSymm

  symmC : C.IsSymm

  intN : IsIntegral B N

  intM : IsIntegral C M

  dualN : B.dualSubmodule N = N ⊔ Submodule.span ℤ (Set.range y)

  dualM : C.dualSubmodule M = M ⊔ Submodule.span ℤ (Set.range m)

  smul_mem : ∀ i, pr i • m i ∈ M

  crossW : ∀ i j, i ≠ j → B (y i) (y j) ∈ (1 : Submodule ℤ ℚ)

  crossU : ∀ i j, i ≠ j → C (m i) (m j) ∈ (1 : Submodule ℤ ℚ)

  diag : ∀ i, B (y i) (y i) + C (m i) (m i) ∈ (1 : Submodule ℤ ℚ)

  unit : ∀ (i : ι) (a b : ℤ),
    ((a : ℚ) * B (y i) (y i) + (b : ℚ) * C (m i) (m i)) ∈ (1 : Submodule ℤ ℚ) →
      pr i ∣ a - b

namespace GlueSystem

variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U} {ι : Type*}

def gen (S : GlueSystem B C N M ι) : ι → W × U := fun i => (S.y i, S.m i)

/--
@isnad1 id=eq.0h9v.s6.0bef5fb24dda from=translated src=- shape=e2076759 vocab=bb30c43c
-/
@[simp] theorem gen_fst (S : GlueSystem B C N M ι) (i : ι) : (S.gen i).1 = S.y i := rfl
/--
@isnad1 id=eq.0h9v.s6.019aacfbbe1b from=translated src=- shape=2f95d0dd vocab=eae1a356
-/
@[simp] theorem gen_snd (S : GlueSystem B C N M ι) (i : ι) : (S.gen i).2 = S.m i := rfl

/--
@isnad1 id=mem.0h9v.s7.216e7ffb0610 from=translated src=- shape=e6f65394 vocab=bcebfe10
-/
theorem y_mem_dual (S : GlueSystem B C N M ι) (i : ι) : S.y i ∈ B.dualSubmodule N := by
  rw [S.dualN]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

/--
@isnad1 id=mem.0h9v.s7.4a30b7c2e1d6 from=translated src=- shape=bf8a1a30 vocab=c6d55f66
-/
theorem m_mem_dual (S : GlueSystem B C N M ι) (i : ι) : S.m i ∈ C.dualSubmodule M := by
  rw [S.dualM]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

/--
@isnad1 id=mem.1h10v.s9.d0b1d847b834 from=translated src=- shape=7ad1aea6 vocab=7f175fe7
-/
theorem pairing_lattice_gen (S : GlueSystem B C N M ι) {z : W × U}
    (hz : z ∈ N.prod M) (j : ι) : prodForm B C z (S.gen j) ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨hz1, hz2⟩ := Submodule.mem_prod.mp hz
  simp only [prodForm_apply, gen_fst, gen_snd]
  refine add_mem ?_ ?_
  · rw [S.symmB.eq z.1 (S.y j)]
    exact S.y_mem_dual j z.1 hz1
  · rw [S.symmC.eq z.2 (S.m j)]
    exact S.m_mem_dual j z.2 hz2

/--
@isnad1 id=mem.0h10v.s9.6371a70d1314 from=translated src=- shape=6d4f488a vocab=3c4f4bdc
-/
theorem pairing_gen_gen (S : GlueSystem B C N M ι) (i j : ι) :
    prodForm B C (S.gen i) (S.gen j) ∈ (1 : Submodule ℤ ℚ) := by
  simp only [prodForm_apply, gen_fst, gen_snd]
  rcases eq_or_ne i j with rfl | hij
  · exact S.diag i
  · exact add_mem (S.crossW i j hij) (S.crossU i j hij)

/--
@isnad1 id=isintegr.0h8v.s7.117ced04a1d7 from=translated src=- shape=9e842943 vocab=6b4c55ae
-/
theorem glue_isIntegral (S : GlueSystem B C N M ι) :
    IsIntegral (prodForm B C) (glueLattice N M S.gen) := by
  refine isIntegral_sup_span (prodForm_isSymm S.symmB S.symmC)
    (isIntegral_prod S.intN S.intM) ?_ ?_
  · rintro z hz _ ⟨j, rfl⟩
    exact S.pairing_lattice_gen hz j
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact S.pairing_gen_gen i j

/--
@isnad1 id=islattic.2h8v.s7.4f7821a727da from=translated src=- shape=748d4994 vocab=7bb8ec06
-/
theorem glue_isLattice (S : GlueSystem B C N M ι) [Finite ι]
    (hN : IsLattice ℚ N) (hM : IsLattice ℚ M) :
    IsLattice ℚ (glueLattice N M S.gen) := by
  refine ⟨Submodule.FG.sup (isLattice_prod hN hM).fg
    (Submodule.fg_span (Set.finite_range _)), ?_⟩
  refine top_unique ?_
  rw [← (isLattice_prod hN hM).spans]
  exact Submodule.span_mono (fun z hz => prod_le_glueLattice hz)

end GlueSystem

end Glue

section Unimodular

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
@isnad1 id=eq.0h8v.s7.2f0c579ca4fd from=translated src=- shape=511125bb vocab=2e2b4d6a
-/
theorem GlueSystem.glue_dual_eq_self (S : GlueSystem B C N M ι) :
    (prodForm B C).dualSubmodule (glueLattice N M S.gen) = glueLattice N M S.gen := by
  refine le_antisymm ?_ S.glue_isIntegral
  intro z hz

  have hz' : z ∈ (prodForm B C).dualSubmodule (N.prod M) :=
    fun w hw => hz w (prod_le_glueLattice hw)
  rw [dualSubmodule_prodForm] at hz'
  obtain ⟨hz1, hz2⟩ := Submodule.mem_prod.mp hz'
  rw [S.dualN] at hz1
  rw [S.dualM] at hz2
  obtain ⟨lam, hlam, t1, ht1, hsum1⟩ := Submodule.mem_sup.mp hz1
  obtain ⟨mu, hmu, t2, ht2, hsum2⟩ := Submodule.mem_sup.mp hz2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht1
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht2

  have hz1eq : z.1 = lam + ∑ i, a i • S.y i := by rw [← hsum1, ha]
  have hz2eq : z.2 = mu + ∑ i, b i • S.m i := by rw [← hsum2, hb]
  have hdvd : ∀ j, S.pr j ∣ a j - b j := by
    intro j
    refine S.unit j (a j) (b j) ?_
    have hzj : prodForm B C z (S.gen j) ∈ (1 : Submodule ℤ ℚ) :=
      hz _ (gen_mem_glueLattice j)
    have e1 : B z.1 (S.y j) = B lam (S.y j) + ∑ i, (a i : ℚ) * B (S.y i) (S.y j) := by
      rw [hz1eq, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
    have e2 : C z.2 (S.m j) = C mu (S.m j) + ∑ i, (b i : ℚ) * C (S.m i) (S.m j) := by
      rw [hz2eq, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
    have hsplitW : ∀ f : ι → ℚ, ∑ i, f i = f j + ∑ i ∈ Finset.univ.erase j, f i :=
      fun f => (Finset.add_sum_erase _ f (Finset.mem_univ j)).symm
    have key : (a j : ℚ) * B (S.y j) (S.y j) + (b j : ℚ) * C (S.m j) (S.m j)
        = prodForm B C z (S.gen j) - (B lam (S.y j) + C mu (S.m j))
          - ∑ i ∈ Finset.univ.erase j,
              ((a i : ℚ) * B (S.y i) (S.y j) + (b i : ℚ) * C (S.m i) (S.m j)) := by
      simp only [prodForm_apply, GlueSystem.gen_fst, GlueSystem.gen_snd]
      rw [e1, e2,
        hsplitW (fun i => (a i : ℚ) * B (S.y i) (S.y j)),
        hsplitW (fun i => (b i : ℚ) * C (S.m i) (S.m j)), Finset.sum_add_distrib]
      ring
    rw [key]
    refine sub_mem (sub_mem hzj (add_mem ?_ ?_)) (Submodule.sum_mem _ fun i hi => ?_)
    · rw [S.symmB.eq lam (S.y j)]
      exact S.y_mem_dual j lam hlam
    · rw [S.symmC.eq mu (S.m j)]
      exact S.m_mem_dual j mu hmu
    · have hij : i ≠ j := Finset.ne_of_mem_erase hi
      refine add_mem ?_ ?_
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_mem _ _ (S.crossW i j hij)
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_mem _ _ (S.crossU i j hij)

  choose c hc using hdvd
  have hfst : (z - ∑ i, a i • S.gen i).1 = lam := by
    rw [Prod.fst_sub, Prod.fst_sum, hz1eq]
    simp only [Prod.smul_fst, GlueSystem.gen_fst]
    abel
  have hsnd : (z - ∑ i, a i • S.gen i).2 = mu + ∑ i, (-(c i)) • (S.pr i • S.m i) := by
    rw [Prod.snd_sub, Prod.snd_sum, hz2eq]
    simp only [Prod.smul_snd, GlueSystem.gen_snd]
    have hterm : ∀ i, b i • S.m i - a i • S.m i = (-(c i)) • (S.pr i • S.m i) := by
      intro i
      rw [smul_smul, ← sub_smul]
      congr 1
      have := hc i
      linarith [this]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => hterm i)
  have hmem : z - ∑ i, a i • S.gen i ∈ N.prod M := by
    refine Submodule.mem_prod.mpr ⟨?_, ?_⟩
    · rw [hfst]; exact hlam
    · rw [hsnd]
      exact M.add_mem hmu
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (S.smul_mem i))
  have hz'' : z = (z - ∑ i, a i • S.gen i) + ∑ i, a i • S.gen i := by abel
  rw [hz'']
  refine Submodule.add_mem _ (prod_le_glueLattice hmem) ?_
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (gen_mem_glueLattice i)

end Unimodular

end SRG266.Lattice
