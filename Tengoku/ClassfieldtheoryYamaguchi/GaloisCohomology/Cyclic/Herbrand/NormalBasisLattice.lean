/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.NormalBasis
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-! Provides the public normal-basis lattice declarations used in Herbrand computations. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The `Gal(L / K)` orbit of Mathlib's normal-basis generator spans `L` over `K`.
@isnad1 id=eq.0h2v.s9.4b0f63720e51 from=translated src=- shape=1428c3f3 vocab=6f227230
-/
theorem normalBasisConjugates_span_eq_top :
    Submodule.span K
        (Set.range (fun σ : Gal(L / K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L / K))))) = ⊤ := by
  have hset :
      Set.range (fun σ : Gal(L / K) =>
        σ (IsGalois.normalBasis K L (1 : Gal(L / K)))) =
        Set.range (IsGalois.normalBasis K L) := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, IsGalois.normalBasis_apply (K := K) (L := L) σ⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, (IsGalois.normalBasis_apply (K := K) (L := L) σ).symm⟩
  rw [hset]
  exact (IsGalois.normalBasis K L).span_eq

variable [ValuativeRel K]

/-- The classical normal-basis lattice candidate `M`: the `𝒪_K`-span of the
normal-basis orbit.  Bounds comparing this lattice with `𝒪_L` are deliberately
made explicit in the lattice-comparison theorems below.-/
def chosenNormalBasisIntegerLattice : Submodule 𝒪[K] L :=
  Submodule.span 𝒪[K]
    (Set.range (fun σ : Gal(L / K) =>
      σ (IsGalois.normalBasis K L (1 : Gal(L / K)))))

/-- Public characterization of the chosen normal-basis lattice as the span of
the chosen generator's Galois orbit.
@isnad1 id=eq.0h2v.s10.37cf6ef7f158 from=translated src=- shape=9c7a4263 vocab=955ee54e
-/
theorem chosenNormalBasisIntegerLattice_eq_span :
    chosenNormalBasisIntegerLattice K L =
      Submodule.span 𝒪[K]
        (Set.range (fun σ : Gal(L / K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L / K))))) :=
  rfl

/-- Every normal-basis vector lies in the `𝒪_K`-span lattice `M`.
@isnad1 id=mem.0h3v.s10.bf0308958d80 from=translated src=- shape=56d20bdc vocab=264dbae1
-/
theorem normalBasis_mem_integerLattice (σ : Gal(L / K)) :
    IsGalois.normalBasis K L σ ∈ chosenNormalBasisIntegerLattice K L := by
  rw [IsGalois.normalBasis_apply]
  exact Submodule.subset_span (Set.mem_range_self σ)

/-- Mathlib's normal-basis generator lies in the `𝒪_K`-span lattice `M`.
@isnad1 id=mem.0h2v.s10.c0b3513997c8 from=translated src=- shape=08f57423 vocab=264dbae1
-/
theorem normalBasis_one_mem_integerLattice :
    IsGalois.normalBasis K L (1 : Gal(L / K)) ∈
      chosenNormalBasisIntegerLattice K L :=
  normalBasis_mem_integerLattice (K := K) (L := L) (1 : Gal(L / K))

/-- After extending scalars back to `K`, the normal-basis lattice spans all of
`L`.
@isnad1 id=eq.0h2v.s10.a69a87e9b936 from=translated src=- shape=7cd5afa3 vocab=a3be7100
-/
theorem chosenNormalBasisIntegerLattice_field_span_eq_top :
    Submodule.span K ((chosenNormalBasisIntegerLattice K L : Submodule 𝒪[K] L) : Set L) =
      ⊤ := by
  refine le_antisymm le_top ?_
  rw [← normalBasisConjugates_span_eq_top (K := K) (L := L)]
  refine Submodule.span_mono ?_
  intro x hx
  exact Submodule.subset_span hx

/-- The normal-basis lattice `M` is stable under the actual `Gal(L / K)`
action.
@isnad1 id=mem.1h4v.s11.84edda9c6f75 from=translated src=- shape=725305cc vocab=f3599541
-/
theorem galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
    (τ : Gal(L / K)) {x : L}
    (hx : x ∈ chosenNormalBasisIntegerLattice K L) :
    τ x ∈ chosenNormalBasisIntegerLattice K L := by
  refine Submodule.span_induction
    (p := fun x _ => τ x ∈ chosenNormalBasisIntegerLattice K L)
    ?hgen ?hzero ?hadd ?hsmul hx
  · intro x hx
    rcases hx with ⟨σ, rfl⟩
    have hτ :
        τ (σ (IsGalois.normalBasis K L (1 : Gal(L / K)))) =
          IsGalois.normalBasis K L (τ * σ) := by
      rw [IsGalois.normalBasis_apply (K := K) (L := L) (τ * σ)]
      rfl
    rw [hτ]
    exact normalBasis_mem_integerLattice (K := K) (L := L) (τ * σ)
  · simp
  · intro x y _ _ hx hy
    simpa using
      (chosenNormalBasisIntegerLattice K L).add_mem hx hy
  · intro a x _ hx
    have ha : τ (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change τ (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact τ.commutes (a : K)
    simpa [Algebra.smul_def, ha, map_mul] using
      (chosenNormalBasisIntegerLattice K L).smul_mem a hx

/-- The normal-basis lattice `M` is finitely generated over `𝒪_K`.
@isnad1 id=fg.0h2v.s8.5608a1ca2be9 from=translated src=- shape=78970128 vocab=7d06466c
-/
theorem chosenNormalBasisIntegerLattice_fg :
    (chosenNormalBasisIntegerLattice K L).FG := by
  dsimp [chosenNormalBasisIntegerLattice]
  exact Submodule.fg_span (Set.finite_range _)

/-- Multiplication by a base integer-ring element, as an `𝒪_K`-linear endomorphism
of the extension field.-/
def baseIntegerScalarMulLinearMap (a : 𝒪[K]) : L →ₗ[𝒪[K]] L where
  toFun x := algebraMap 𝒪[K] L a * x
  map_add' := by
    intro x y
    rw [mul_add]
  map_smul' := by
    intro r x
    simp [Algebra.smul_def, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Evaluates the linear map given by scalar multiplication from the base integer ring.
@isnad1 id=eq.0h4v.s11.405792c67e5f from=translated src=- shape=cfa17004 vocab=0d568c7e
-/
@[simp]
theorem baseIntegerScalarMulLinearMap_apply (a : 𝒪[K]) (x : L) :
    baseIntegerScalarMulLinearMap K L a x = algebraMap 𝒪[K] L a * x :=
  rfl

/-- The image of an `𝒪_K`-submodule under multiplication by a base
integer-ring element.-/
def baseIntegerScalarMulSubmodule (a : 𝒪[K]) (N : Submodule 𝒪[K] L) :
    Submodule 𝒪[K] L :=
  N.map (baseIntegerScalarMulLinearMap K L a)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Characterizes membership in the submodule generated by base-integer scalar multiples.
@isnad1 id=iff.0h5v.s11.5bc1eee9038f from=translated src=- shape=819e242d vocab=08b8fc43
-/
theorem mem_baseIntegerScalarMulSubmodule_iff
    (a : 𝒪[K]) (N : Submodule 𝒪[K] L) (x : L) :
    x ∈ baseIntegerScalarMulSubmodule K L a N ↔
      ∃ y : L, y ∈ N ∧ algebraMap 𝒪[K] L a * y = x :=
  Iff.rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Scalar multiplication by base integers preserves finite generation of submodules.
@isnad1 id=fg.1h4v.s10.20e67e53183e from=translated src=- shape=d2672a8b vocab=c8122e0f
-/
theorem baseIntegerScalarMulSubmodule_fg_of_fg
    (a : 𝒪[K]) {N : Submodule 𝒪[K] L} (hN : N.FG) :
    (baseIntegerScalarMulSubmodule K L a N).FG :=
  hN.map (baseIntegerScalarMulLinearMap K L a)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Multiplication of an `𝒪_K`-submodule by a power of the chosen base
uniformizer.  The name deliberately records the construction's dependence on
`chosenIntegerRingUniformizer K`; no uniformizer-independence result is part of
this API.  This is the concrete shape of the `π_K^n` lattices used in the local
class-field-axiom calculation.-/
def chosenBaseUniformizerPowSubmodule (n : Nat) (N : Submodule 𝒪[K] L) :
    Submodule 𝒪[K] L :=
  baseIntegerScalarMulSubmodule K L (chosenIntegerRingUniformizer K ^ n) N

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Characterizes membership in a chosen uniformizer-power submodule.
@isnad1 id=iff.0h5v.s12.97d739c3bfdb from=translated src=- shape=e81a8d5c vocab=7af67e95
-/
@[simp]
theorem mem_chosenBaseUniformizerPowSubmodule_iff
    (n : Nat) (N : Submodule 𝒪[K] L) (x : L) :
    x ∈ chosenBaseUniformizerPowSubmodule K L n N ↔
      ∃ y : L, y ∈ N ∧
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x :=
  Iff.rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Multiplication by a chosen uniformizer power preserves finite generation.
@isnad1 id=fg.1h4v.s10.42117ee7bd0e from=translated src=- shape=8a3d508e vocab=5db8d931
-/
theorem chosenBaseUniformizerPowSubmodule_fg_of_fg
    (n : Nat) {N : Submodule 𝒪[K] L} (hN : N.FG) :
    (chosenBaseUniformizerPowSubmodule K L n N).FG :=
  baseIntegerScalarMulSubmodule_fg_of_fg (K := K) (L := L)
    (chosenIntegerRingUniformizer K ^ n) hN

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Increasing the base-uniformizer exponent preserves membership after
denominator clearing.
@isnad1 id=mem.2h6v.s12.5d1acfdacb72 from=translated src=- shape=bd60ba1f vocab=55168ddd
-/
theorem chosenBaseUniformizerPow_mul_mem_mono
    {M : Submodule 𝒪[K] L} {m n : Nat} {x : L} (hmn : m ≤ n)
    (hx : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x ∈ M) :
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  rw [hd]
  have hscaled :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
          (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x) ∈ M := by
    simpa [Algebra.smul_def, mul_assoc] using
      M.smul_mem (chosenIntegerRingUniformizer K ^ d) hx
  simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The lattices `π_K^n N` form a descending filtration.
@isnad1 id=le.1h5v.s11.6045df2e00c5 from=translated src=- shape=a6af0c21 vocab=134c3037
-/
theorem chosenBaseUniformizerPowSubmodule_antitone
    (N : Submodule 𝒪[K] L) {m n : Nat} (hmn : m ≤ n) :
    chosenBaseUniformizerPowSubmodule K L n N ≤
      chosenBaseUniformizerPowSubmodule K L m N := by
  intro x hx
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n N x).1 hx with
    ⟨y, hyN, rfl⟩
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) m N _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) * y, ?_, ?_⟩
  · simpa [Algebra.smul_def, mul_assoc] using
      N.smul_mem (chosenIntegerRingUniformizer K ^ d) hyN
  · simp [hd, pow_add, map_mul, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Successive chosen uniformizer-power submodules form a descending chain.
@isnad1 id=le.0h4v.s11.e3c3284c3e1f from=translated src=- shape=a3b28f6e vocab=94b1e1f9
-/
theorem chosenBaseUniformizerPowSubmodule_succ_le
    (n : Nat) (N : Submodule 𝒪[K] L) :
    chosenBaseUniformizerPowSubmodule K L (n + 1) N ≤
      chosenBaseUniformizerPowSubmodule K L n N :=
  chosenBaseUniformizerPowSubmodule_antitone (K := K) (L := L) N (Nat.le_succ n)

/-- Every chosen uniformizer-power normal-basis lattice is finitely generated.
@isnad1 id=fg.0h3v.s9.bc117b050807 from=translated src=- shape=05e02c8c vocab=69dcc1a0
-/
theorem chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_fg (n : Nat) :
    (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)).FG :=
  chosenBaseUniformizerPowSubmodule_fg_of_fg (K := K) (L := L) n
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If an `𝒪_K`-submodule spans `L` after extending scalars to `K`, then every
element of `L` enters that submodule after multiplying by a high enough power
of the base prime element.  The scalar-denominator step is exactly the local
DVR denominator clearing in `IdealQuotients`.
@isnad1 id=ex.1h4v.s11.5e14f275ad36 from=translated src=- shape=77e02394 vocab=8ff21a91
-/
theorem exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
    {M : Submodule 𝒪[K] L}
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) (x : L) :
    ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M := by
  have hx : x ∈ Submodule.span K ((M : Set L)) := by
    rw [hMspan]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun y _ =>
      ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M)
    ?hgen ?hzero ?hadd ?hsmul hx
  · intro y hyM
    refine ⟨0, ?_⟩
    simpa using hyM
  · refine ⟨0, ?_⟩
    simp
  · intro y z _ _ hy hz
    rcases hy with ⟨m, hm⟩
    rcases hz with ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    have hy' := chosenBaseUniformizerPow_mul_mem_mono
      (K := K) (L := L) (M := M) (Nat.le_max_left m n) hm
    have hz' := chosenBaseUniformizerPow_mul_mem_mono
      (K := K) (L := L) (M := M) (Nat.le_max_right m n) hn
    simpa [mul_add] using M.add_mem hy' hz'
  · intro c y _ hy
    rcases hy with ⟨m, hm⟩
    obtain ⟨d, hd⟩ := exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing K c
    let cInt : 𝒪[K] :=
      ⟨(((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ d) * c, hd⟩
    refine ⟨d + m, ?_⟩
    have hscaled :
        algebraMap 𝒪[K] L cInt *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using M.smul_mem cInt hm
    have hcInt :
        algebraMap 𝒪[K] L cInt =
          algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            algebraMap K L c := by
      change algebraMap K L
          ((((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ d) * c) = _
      simp only [map_mul, map_pow]
      rfl
    rw [hcInt] at hscaled
    convert hscaled using 1
    rw [Algebra.smul_def, pow_add, map_mul]
    ring

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Finite-generation version of
`exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top`: one exponent works
for all elements of a finitely generated `𝒪_K`-submodule.
@isnad1 id=ex.2h4v.s11.67af4a1eddd1 from=translated src=- shape=d6334973 vocab=c19e3fb2
-/
theorem exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top
    {M N : Submodule 𝒪[K] L} (hN : N.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ n : Nat, chosenBaseUniformizerPowSubmodule K L n N ≤ M := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  let t : Finset L := hSfinite.toFinset
  let nOf : L → Nat := fun y =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan y)
  let n : Nat := t.sup nOf
  have hnOf_spec (y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ nOf y) * y ∈ M :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan y)
  have hpow_mono {m : Nat} {y : L} (hmn : m ≤ n)
      (hy : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y ∈ M) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    rw [hd]
    have hscaled :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using
        M.smul_mem (chosenIntegerRingUniformizer K ^ d) hy
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hN_mem (y : L) (hyN : y ∈ N) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M := by
    rw [← hSspan] at hyN
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M)
      ?hgen ?hzero ?hadd ?hsmul hyN
    · intro y hyS
      have hyt : y ∈ t := by
        exact (Set.Finite.mem_toFinset hSfinite).2 hyS
      exact hpow_mono (Finset.le_sup hyt) (hnOf_spec y)
    · simp
    · intro y z _ _ hy hz
      simpa [mul_add] using M.add_mem hy hz
    · intro a y _ hy
      have hscaled :
          algebraMap 𝒪[K] L a *
              (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y) ∈ M := by
        simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hy
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled
  refine ⟨n, ?_⟩
  intro z hz
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n N z).1 hz with
    ⟨y, hyN, rfl⟩
  exact hN_mem y hyN

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Product-denominator bound for multiplicative lattice control.  If `N` and `P` are finitely generated
`𝒪_K`-submodules and `M` spans `L` after inverting `𝒪_K`, then one power of the
base prime element sends every product `xy`, `x ∈ N`, `y ∈ P`, back into `M`.

This is the multiplicative source needed before proving that `1 + π_K^n M` is
closed under multiplication for large `n`.
@isnad1 id=ex.3h5v.s13.1623c8c11d12 from=translated src=- shape=79d43d83 vocab=dd049d0d
-/
theorem exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
    {M N P : Submodule 𝒪[K] L} (hN : N.FG) (hP : P.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ n : Nat, ∀ x : L, x ∈ N → ∀ y : L, y ∈ P →
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  rcases Submodule.fg_def.mp hP with ⟨T, hTfinite, hTspan⟩
  let s : Finset L := hSfinite.toFinset
  let t : Finset L := hTfinite.toFinset
  let pairExp : L × L → Nat := fun p =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan (p.1 * p.2))
  let n : Nat := (s.product t).sup pairExp
  have hpair_spec (x y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (pairExp (x, y))) * (x * y) ∈ M :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan (x * y))
  have hpow_mono {m : Nat} {z : L} (hmn : m ≤ n)
      (hz : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z ∈ M) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * z ∈ M := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    rw [hd]
    have hscaled :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using
        M.smul_mem (chosenIntegerRingUniformizer K ^ d) hz
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hgen (x y : L) (hxS : x ∈ S) (hyT : y ∈ T) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
    have hxs : x ∈ s := (Set.Finite.mem_toFinset hSfinite).2 hxS
    have hyt : y ∈ t := (Set.Finite.mem_toFinset hTfinite).2 hyT
    exact hpow_mono (Finset.le_sup (Finset.mem_product.2 ⟨hxs, hyt⟩))
      (hpair_spec x y)
  have hleft (x : L) (hxS : x ∈ S) :
      ∀ y : L, y ∈ P →
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
    intro y hyP
    rw [← hTspan] at hyP
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M)
      ?hgen ?hzero ?hadd ?hsmul hyP
    · intro y hyT
      exact hgen x y hxS hyT
    · simp
    · intro y z _ _ hy hz
      simpa [mul_add] using M.add_mem hy hz
    · intro a y _ hy
      have hscaled :
          algebraMap 𝒪[K] L a *
              (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y)) ∈ M := by
        simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hy
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled
  refine ⟨n, ?_⟩
  intro x hxN y hyP
  rw [← hSspan] at hxN
  refine Submodule.span_induction
    (p := fun x _ =>
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M)
    ?gen ?zero ?add ?smul hxN
  · intro x hxS
    exact hleft x hxS y hyP
  · simp
  · intro x z _ _ hx hz
    convert M.add_mem hx hz using 1 ; ring
  · intro a x _ hx
    have hscaled :
        algebraMap 𝒪[K] L a *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y)) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hx
    simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- A sufficiently deep uniformizer-power normal-basis lattice absorbs the indicated products.
@isnad1 id=ex.0h2v.s12.83a26ea62e4c from=translated src=- shape=0879cbfd vocab=d4eb25d2
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem :
    ∃ n : Nat, ∀ x : L, x ∈ chosenNormalBasisIntegerLattice K L →
      ∀ y : L, y ∈ chosenNormalBasisIntegerLattice K L →
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈
          chosenNormalBasisIntegerLattice K L :=
  exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (N := chosenNormalBasisIntegerLattice K L)
    (P := chosenNormalBasisIntegerLattice K L)
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- For sufficiently large `n`, the lattice `π_K^n M` is closed under
multiplication.  It supplies the multiplicative
closure of `1 + π_K^n M` in the principal-unit lattice.
@isnad1 id=ex.2h3v.s12.795f8e376fd6 from=translated src=- shape=13532d08 vocab=455d5d84
-/
theorem exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n M →
      ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
        x * y ∈ chosenBaseUniformizerPowSubmodule K L n M := by
  rcases exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
      (K := K) (L := L) (M := M) (N := M) (P := M) hMfg hMfg hMspan with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn x hx y hy
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M x).1 hx with
    ⟨x0, hx0M, rfl⟩
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M y).1 hy with
    ⟨y0, hy0M, rfl⟩
  have hprod :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x0 * y0) ∈ M :=
    chosenBaseUniformizerPow_mul_mem_mono (K := K) (L := L) hcn
      (hc x0 hx0M y0 hy0M)
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x0 * y0),
    hprod, ?_⟩
  simp [mul_assoc, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- For sufficiently large `n`, products of two elements of `π_K^n M` land in
the next lattice step `π_K^(n+1) M`.

This is the product-depth estimate needed before the map
`V^n/V^(n+1) -> π_K^nM/π_K^(n+1)M` can be made well-defined.
@isnad1 id=ex.2h3v.s12.78b73c9c5672 from=translated src=- shape=05e470de vocab=29b5f304
-/
theorem exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n M →
      ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
        x * y ∈ chosenBaseUniformizerPowSubmodule K L (n + 1) M := by
  rcases exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
      (K := K) (L := L) (M := M) (N := M) (P := M) hMfg hMfg hMspan with
    ⟨c, hc⟩
  refine ⟨c + 1, ?_⟩
  intro n hcn x hx y hy
  rcases Nat.exists_eq_add_of_le hcn with ⟨d, hd⟩
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M x).1 hx with
    ⟨x0, hx0M, rfl⟩
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M y).1 hy with
    ⟨y0, hy0M, rfl⟩
  have hprod :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (c + d)) * (x0 * y0) ∈ M :=
    chosenBaseUniformizerPow_mul_mem_mono (K := K) (L := L)
      (Nat.le_add_right c d) (hc x0 hx0M y0 hy0M)
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) (n + 1) M _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (c + d)) * (x0 * y0),
    hprod, ?_⟩
  rw [hd]
  simp only [map_mul, pow_add, pow_one]
  ring

/-- A sufficiently deep uniformizer-power normal-basis lattice is closed under
the indicated self-products.
@isnad1 id=ex.0h2v.s11.55920e1ff4e5 from=translated src=- shape=6af9312b vocab=2f3a95b5
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

/-- A sufficiently deep lattice sends the indicated products into the next uniformizer level.
@isnad1 id=ex.0h2v.s11.772bd9c47dd7 from=translated src=- shape=8d2daff8 vocab=67cc2ab5
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succ :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L) :=
  exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Powers of an element stay in a multiplicatively closed additive lattice.

This is the finite algebraic input to the geometric-series inverse argument; completeness supplies the limit of these finite approximations.
@isnad1 id=mem.2h5v.s12.5cbf7fe5ab9d from=translated src=- shape=cb23bac4 vocab=d41337d7
-/
theorem submodule_pow_succ_mem_of_mul_closed
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) :
    ∀ m : Nat, x ^ (m + 1) ∈ E := by
  intro m
  induction m with
  | zero =>
      simpa using hx
  | succ m ih =>
      have hmul_mem : x ^ (m + 1) * x ∈ E := hmul (x ^ (m + 1)) ih x hx
      simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using hmul_mem

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The finite inverse-correction sum
`(-x) + (-x)^2 + ... + (-x)^d`.

When `x` is topologically nilpotent and the lattice is complete, these are the
finite approximations to `(1+x)⁻¹ - 1`.-/
def inverseCorrectionPartialSum (x : L) (d : Nat) : L :=
  (Finset.range d).sum fun i => (-x) ^ (i + 1)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The zeroth inverse-correction partial sum is its initial term.
@isnad1 id=eq.0h2v.s5.e0110a210ebf from=translated src=- shape=4e114734 vocab=301856c1
-/
@[simp]
theorem inverseCorrectionPartialSum_zero (x : L) :
    inverseCorrectionPartialSum (L := L) x 0 = 0 := by
  simp [inverseCorrectionPartialSum]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Expands the inverse-correction partial sum at a successor index.
@isnad1 id=eq.0h3v.s6.2ab362ff05b2 from=translated src=- shape=357bdcd1 vocab=09f9e571
-/
theorem inverseCorrectionPartialSum_succ (x : L) (d : Nat) :
    inverseCorrectionPartialSum (L := L) x (d + 1) =
      inverseCorrectionPartialSum (L := L) x d + (-x) ^ (d + 1) := by
  simp [inverseCorrectionPartialSum, Finset.sum_range_succ]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Adding `1` turns the inverse-correction sum into the usual finite
geometric sum with ratio `-x`.
@isnad1 id=eq.0h3v.s6.512884c3c7dd from=translated src=- shape=04ad12af vocab=53858c06
-/
theorem one_add_inverseCorrectionPartialSum_eq_geom_sum (x : L) (d : Nat) :
    1 + inverseCorrectionPartialSum (L := L) x d =
      (Finset.range (d + 1)).sum fun i => (-x) ^ i := by
  induction d with
  | zero =>
      simp [inverseCorrectionPartialSum]
  | succ d ih =>
      rw [inverseCorrectionPartialSum_succ, Finset.sum_range_succ, ← ih]
      simp [add_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Finite geometric inverse identity for the approximants to `(1+x)⁻¹`.
@isnad1 id=eq.0h3v.s7.3770d066be78 from=translated src=- shape=900b6c3c vocab=86d6603b
-/
theorem one_add_mul_one_add_inverseCorrectionPartialSum (x : L) (d : Nat) :
    (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) =
      1 - (-x) ^ (d + 1) := by
  rw [one_add_inverseCorrectionPartialSum_eq_geom_sum]
  simpa [sub_neg_eq_add] using
    (mul_neg_geom_sum (x := (-x : L)) (n := d + 1))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The residual error after applying a finite inverse correction.
@isnad1 id=eq.0h3v.s7.ad6c9d5b1580 from=translated src=- shape=7194609e vocab=86d6603b
-/
theorem one_add_mul_one_add_inverseCorrectionPartialSum_sub_one
    (x : L) (d : Nat) :
    (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) - 1 =
      -((-x) ^ (d + 1)) := by
  rw [one_add_mul_one_add_inverseCorrectionPartialSum]
  simp [sub_eq_add_neg, add_assoc]

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Inverse-correction partial sums remain in any additive set closed under multiplication.
@isnad1 id=mem.2h5v.s12.765672c266b2 from=translated src=- shape=1e5263bb vocab=574785c4
-/
theorem inverseCorrectionPartialSum_mem_of_mul_closed
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) (d : Nat) :
    inverseCorrectionPartialSum (L := L) x d ∈ E := by
  unfold inverseCorrectionPartialSum
  refine Submodule.sum_mem E ?_
  intro i _
  exact submodule_pow_succ_mem_of_mul_closed (K := K) (L := L)
    hmul (E.neg_mem hx) i

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A finite inverse correction kills `1+x` modulo the same multiplicatively
closed additive lattice.
@isnad1 id=mem.2h5v.s12.646ab52ada2d from=translated src=- shape=20c08d0c vocab=88a1484e
-/
theorem inverseCorrectionPartialProductError_mem_of_mul_closed
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) (d : Nat) :
    (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) - 1 ∈ E := by
  rw [one_add_mul_one_add_inverseCorrectionPartialSum_sub_one]
  exact E.neg_mem
    (submodule_pow_succ_mem_of_mul_closed (K := K) (L := L)
      hmul (E.neg_mem hx) d)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An additive `𝒪_K`-submodule containing a neighborhood of `0` is open.
@isnad1 id=isopen.1h3v.s11.9cbdceae8f82 from=translated src=- shape=1f8f7225 vocab=4f15a4f4
-/
theorem submodule_isOpen_of_mem_nhds_zero
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : (E : Set L) ∈ nhds (0 : L)) :
    IsOpen (E : Set L) := by
  simpa using AddSubgroup.isOpen_of_mem_nhds E.toAddSubgroup hE

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An open additive `𝒪_K`-submodule is closed.
@isnad1 id=isclosed.1h3v.s11.146f3198cd3f from=translated src=- shape=f27764ea vocab=7d07b212
-/
theorem submodule_isClosed_of_isOpen
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : IsOpen (E : Set L)) :
    IsClosed (E : Set L) := by
  simpa using AddSubgroup.isClosed_of_isOpen E.toAddSubgroup hE

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A neighborhood submodule is closed in a topological additive group.
@isnad1 id=isclosed.1h3v.s11.6f1c56394ec9 from=translated src=- shape=1f8f7225 vocab=8473d4e1
-/
theorem submodule_isClosed_of_mem_nhds_zero
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : (E : Set L) ∈ nhds (0 : L)) :
    IsClosed (E : Set L) :=
  submodule_isClosed_of_isOpen (K := K) (L := L)
    (submodule_isOpen_of_mem_nhds_zero (K := K) (L := L) hE)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- If every term of a convergent sequence lies in a closed submodule, then the
limit lies in that submodule.
@isnad1 id=mem.3h5v.s11.77a06c4418f8 from=translated src=- shape=42a6af89 vocab=6ca3bca5
-/
theorem submodule_mem_of_tendsto_of_forall_mem_of_closed
    [TopologicalSpace L] {E : Submodule 𝒪[K] L} {f : Nat → L} {x : L}
    (hclosed : IsClosed (E : Set L)) (hf : Tendsto f atTop (nhds x))
    (hmem : ∀ d : Nat, f d ∈ E) :
    x ∈ E := by
  exact hclosed.mem_of_tendsto hf (Eventually.of_forall hmem)

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Under a valuation extension, the chosen base prime element maps into the
maximal ideal of the extension valuation ring.
@isnad1 id=mem.0h2v.s11.1eae0b08a8db from=translated src=- shape=a5c12475 vocab=e7aa2f31
-/
theorem integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension :
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K) ∈
      (𝓂[L] : Ideal 𝒪[L]) := by
  have hπK :
      chosenIntegerRingUniformizer K ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    exact Ideal.subset_span (Set.mem_singleton (chosenIntegerRingUniformizer K))
  exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
    (ValuativeRel.valuation K) (ValuativeRel.valuation L)).2 hπK

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension-field denominator clearing by powers of the base prime element.

For any `x : L`, a sufficiently high power of the chosen prime element of
`𝒪[K]`, mapped to `L`, sends `x` into `𝒪[L]`.  This is the denominator-clearing input used before comparing the normal-basis lattice with `𝒪_L`: it uses only the
DVR structure of `𝒪_L` and the fact that the image of the base prime lies in
`𝓂_L`.
@isnad1 id=ex.0h3v.s10.919f3bae728c from=translated src=- shape=5b9fff75 vocab=8063ba97
-/
theorem exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (x : L) :
    ∃ n : Nat,
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ 𝒪[L] := by
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := 𝒪[L]) x
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, ub, hb_factor⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne
      (chosenIntegerRingUniformizer_irreducible L)
  refine ⟨m, ?_⟩
  let πK_L : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπK_L_mem : πK_L ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    dsimp [πK_L]
    exact integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension
      (K := K) (L := L)
  have hπK_L_pow_mem : πK_L ^ m ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) :=
    Ideal.pow_mem_pow hπK_L_mem m
  have hπK_L_span :
      πK_L ^ m ∈
        Ideal.span ({chosenIntegerRingUniformizer L ^ m} : Set 𝒪[L]) := by
    simpa [maximalIdeal_pow_eq_span_uniformizer_pow L m] using hπK_L_pow_mem
  rcases Ideal.mem_span_singleton'.mp hπK_L_span with ⟨c, hc⟩
  rw [← hfrac, hb_factor]
  have hϖL_ne : (((chosenIntegerRingUniformizer L : 𝒪[L]) : L)) ≠ 0 := by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible L).ne_zero
      ((IsFractionRing.injective 𝒪[L] L) h)
  have hϖL_pow_ne :
      (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m) ≠ 0 :=
    pow_ne_zero m hϖL_ne
  have hub_ne : (((ub : 𝒪[L]) : L)) ≠ 0 := by
    intro h
    exact ub.ne_zero ((IsFractionRing.injective 𝒪[L] L) h)
  have hub_inv :
      (((↑ub⁻¹ : 𝒪[L]) : L)) = (((ub : 𝒪[L]) : L))⁻¹ := by
    exact map_units_inv (algebraMap 𝒪[L] L) ub
  have hbase :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) =
        ((πK_L ^ m : 𝒪[L]) : L) := by
    dsimp [πK_L, integerRingMapOfValuationExtension]
    simp only [map_pow]
    change (algebraMap K L ((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ^ m =
      (algebraMap K L ((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ^ m
    rfl
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) *
      ((a : L) /
        (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) ∈ 𝒪[L]
  rw [hbase]
  have hclear :
      ((πK_L ^ m : 𝒪[L]) : L) *
          ((a : L) /
            (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) =
        ((c * ↑ub⁻¹ * a : 𝒪[L]) : L) := by
    calc
      ((πK_L ^ m : 𝒪[L]) : L) *
          ((a : L) /
            (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L))
          =
          ((c * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L) *
            ((a : L) /
              (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) := by
            rw [← hc]
      _ = ((c : L) * (((ub : 𝒪[L]) : L))⁻¹ * (a : L)) := by
            change
              ((c : L) * (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m)) *
                  ((a : L) /
                    (((ub : 𝒪[L]) : L) *
                      (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m))) =
                (c : L) * (((ub : 𝒪[L]) : L))⁻¹ * (a : L)
            field_simp [hub_ne, hϖL_pow_ne]
      _ = ((c * ↑ub⁻¹ * a : 𝒪[L]) : L) := by
            rw [← hub_inv]
            simp [mul_assoc]
  rw [hclear]
  exact (c * ↑ub⁻¹ * a : 𝒪[L]).2

/-- The inclusion `𝒪_L -> L` as an `𝒪_K`-linear map, using the valuation-extension
map `𝒪_K -> 𝒪_L` for the scalar action.-/
def integerRingToFieldLinearMap : 𝒪[L] →ₗ[𝒪[K]] L where
  toFun x := (x : L)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

/-- The valuation integer ring of `L`, viewed as an `𝒪_K`-submodule of `L`.
This is the `𝒪_L` lattice compared with the normal-basis lattice.-/
def integerRingFieldSubmodule : Submodule 𝒪[K] L where
  carrier := {x | x ∈ 𝒪[L]}
  zero_mem' := by
    change (0 : L) ∈ 𝒪[L]
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    change x + y ∈ 𝒪[L]
    exact add_mem hx hy
  smul_mem' := by
    intro a x hx
    change a • x ∈ 𝒪[L]
    rw [Algebra.smul_def]
    have ha : algebraMap 𝒪[K] L a ∈ 𝒪[L] := by
      change algebraMap K L (a : K) ∈ 𝒪[L]
      exact (integerRingMapOfValuationExtension K L a).2
    exact mul_mem ha hx

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- Characterizes the field elements lying in the embedded integer-ring submodule.
@isnad1 id=iff.0h3v.s10.64de4a2f5455 from=translated src=- shape=5a4f7198 vocab=e552a613
-/
@[simp]
theorem mem_integerRingFieldSubmodule_iff (x : L) :
    x ∈ integerRingFieldSubmodule K L ↔ x ∈ 𝒪[L] :=
  Iff.rfl

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- Every integer-ring element lies in the corresponding field submodule.
@isnad1 id=mem.0h3v.s10.32e7ab7e1e3b from=translated src=- shape=7d44cf58 vocab=f8d17f14
-/
theorem integerRing_mem_integerRingFieldSubmodule (x : 𝒪[L]) :
    (x : L) ∈ integerRingFieldSubmodule K L :=
  x.2

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A base-uniformizer multiple of `𝒪_L` is a zero-neighborhood in `L`.
@isnad1 id=mem.0h3v.s10.2d3755628a50 from=translated src=- shape=4f401497 vocab=926b7d60
-/
theorem chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (m : Nat) :
    ((chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L) : Set L)) ∈ nhds (0 : L) := by
  let a : L := algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m)
  have hπ_ne : (chosenIntegerRingUniformizer K ^ m : 𝒪[K]) ≠ 0 :=
    pow_ne_zero m (chosenIntegerRingUniformizer_irreducible K).ne_zero
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    change algebraMap K L ((chosenIntegerRingUniformizer K ^ m : 𝒪[K]) : K) ≠ 0
    apply (map_ne_zero (algebraMap K L)).2
    intro h
    exact hπ_ne ((IsFractionRing.injective 𝒪[K] K) h)
  have ha_val_pos : 0 < ValuativeRel.valuation L a := by
    exact (ValuativeRel.valuation L).pos_iff.2 ha_ne
  let γ : (ValuativeRel.ValueGroupWithZero L)ˣ :=
    Units.mk0 (ValuativeRel.valuation L a) (ne_of_gt ha_val_pos)
  refine Filter.mem_of_superset
    ((IsValuativeTopology.hasBasis_nhds_zero L).mem_of_mem (i := γ) trivial) ?_
  intro x hx
  refine (mem_chosenBaseUniformizerPowSubmodule_iff
    (K := K) (L := L) m (integerRingFieldSubmodule K L) x).2 ?_
  refine ⟨a⁻¹ * x, ?_, ?_⟩
  · rw [mem_integerRingFieldSubmodule_iff]
    rw [Valuation.mem_integer_iff]
    have hxle : ValuativeRel.valuation L x ≤ ValuativeRel.valuation L a := le_of_lt hx
    have hval :
        ValuativeRel.valuation L (a⁻¹ * x) =
          (ValuativeRel.valuation L a)⁻¹ * ValuativeRel.valuation L x := by
      simp [map_mul]
    rw [hval]
    exact (inv_mul_le_one₀ ha_val_pos).2 hxle
  · change a * (a⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- The maximal ideal `𝓂_L`, viewed inside `L` as an `𝒪_K`-submodule.-/
def maximalIdealFieldSubmodule : Submodule 𝒪[K] L where
  carrier := {x | ∃ a : 𝒪[L], a ∈ (𝓂[L] : Ideal 𝒪[L]) ∧ (a : L) = x}
  zero_mem' := by
    refine ⟨0, by simp, by simp⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    refine ⟨a + b, (𝓂[L] : Ideal 𝒪[L]).add_mem ha hb, by simp⟩
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨integerRingMapOfValuationExtension K L c * a, ?_, ?_⟩
    · exact Ideal.mul_mem_left _ (integerRingMapOfValuationExtension K L c) ha
    · change ((integerRingMapOfValuationExtension K L c : 𝒪[L]) : L) * (a : L) =
        c • (a : L)
      rw [Algebra.smul_def]
      congr 1

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- Characterizes membership in the field submodule induced by the maximal ideal.
@isnad1 id=iff.0h3v.s11.ee34d0c54947 from=translated src=- shape=cbfc9f0e vocab=ef331e67
-/
@[simp]
theorem mem_maximalIdealFieldSubmodule_iff (x : L) :
    x ∈ maximalIdealFieldSubmodule K L ↔
      ∃ a : 𝒪[L], a ∈ (𝓂[L] : Ideal 𝒪[L]) ∧ (a : L) = x :=
  Iff.rfl

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- The maximal-ideal field submodule is contained in the integer-ring field submodule.
@isnad1 id=le.0h2v.s10.efd347ff2f03 from=translated src=- shape=29d1eaa2 vocab=c22375c6
-/
theorem maximalIdealFieldSubmodule_le_integerRingFieldSubmodule :
    maximalIdealFieldSubmodule K L ≤ integerRingFieldSubmodule K L := by
  intro x hx
  rcases (mem_maximalIdealFieldSubmodule_iff (K := K) (L := L) x).1 hx with
    ⟨a, _, rfl⟩
  exact integerRing_mem_integerRingFieldSubmodule (K := K) (L := L) a

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A finitely generated `𝒪_K`-submodule of `L` is sent into `𝒪_L` after
multiplication by a single sufficiently high power of the base prime element.

This proves the `π_K^b N ≤ 𝒪_L` first direction of the lattice-bound statement for
any finitely generated `N`; applying it to the normal-basis lattice gives the
needed denominator bound for `M`.
@isnad1 id=ex.1h3v.s11.1aa7c64f70f9 from=translated src=- shape=a739b924 vocab=ee19329f
-/
theorem exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n N ≤ integerRingFieldSubmodule K L := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  let t : Finset L := hSfinite.toFinset
  let nOf : L → Nat := fun y =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
        (K := K) (L := L) y)
  let n : Nat := t.sup nOf
  have hnOf_spec (y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ nOf y) * y ∈ 𝒪[L] :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
        (K := K) (L := L) y)
  have hpow_mono {m : Nat} {y : L} (hmn : m ≤ n)
      (hy : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y ∈ 𝒪[L]) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L] := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    have hd_mem :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) ∈ 𝒪[L] := by
      change algebraMap K L ((chosenIntegerRingUniformizer K ^ d : 𝒪[K]) : K) ∈ 𝒪[L]
      exact (integerRingMapOfValuationExtension K L
        (chosenIntegerRingUniformizer K ^ d)).2
    rw [hd]
    rw [pow_add, map_mul]
    simpa [mul_assoc, mul_comm, mul_left_comm] using mul_mem hd_mem hy
  have hN_mem (y : L) (hyN : y ∈ N) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L] := by
    rw [← hSspan] at hyN
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L])
      ?hgen ?hzero ?hadd ?hsmul hyN
    · intro y hyS
      have hyt : y ∈ t := by
        exact (Set.Finite.mem_toFinset hSfinite).2 hyS
      exact hpow_mono (Finset.le_sup hyt) (hnOf_spec y)
    · simp
    · intro y z _ _ hy hz
      simpa [mul_add] using add_mem hy hz
    · intro a y _ hy
      have ha_mem : algebraMap 𝒪[K] L a ∈ 𝒪[L] := by
        change algebraMap K L (a : K) ∈ 𝒪[L]
        exact (integerRingMapOfValuationExtension K L a).2
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        mul_mem ha_mem hy
  refine ⟨n, ?_⟩
  intro z hz
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n N z).1 hz with
    ⟨y, hyN, rfl⟩
  exact hN_mem y hyN

/-- Some uniformizer-power normal-basis lattice lies inside the integer-ring field submodule.
@isnad1 id=ex.0h2v.s10.588ec7594424 from=translated src=- shape=26a05f95 vocab=d6603778
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        integerRingFieldSubmodule K L :=
  exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
    (K := K) (L := L) (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Multiplying an existing containment by a further base-uniformizer power.
@isnad1 id=le.1h6v.s12.fec0737af0e0 from=translated src=- shape=ddd5dac5 vocab=94b1e1f9
-/
theorem chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
    {N M : Submodule 𝒪[K] L} {a n : Nat}
    (h : chosenBaseUniformizerPowSubmodule K L a N ≤ M) :
    chosenBaseUniformizerPowSubmodule K L (a + n) N ≤
      chosenBaseUniformizerPowSubmodule K L n M := by
  intro x hx
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) (a + n) N x).1 hx with
    ⟨y, hyN, rfl⟩
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ a) * y, ?_, ?_⟩
  · exact h ((mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) a N _).2
      ⟨y, hyN, rfl⟩)
  · simp [pow_add, map_mul, mul_assoc, mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If `π_K^b N` is integral, then `π_K^(b+1) N` lands in the maximal ideal of
`𝒪_L`.
@isnad1 id=le.1h4v.s11.e9c2b94200c8 from=translated src=- shape=23c0d3f7 vocab=a3e95b42
-/
theorem chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule
    {N : Submodule 𝒪[K] L} {b : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b N ≤ integerRingFieldSubmodule K L) :
    chosenBaseUniformizerPowSubmodule K L (b + 1) N ≤
      maximalIdealFieldSubmodule K L := by
  intro x hx
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) (b + 1) N x).1 hx with
    ⟨y, hyN, rfl⟩
  have hby :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y ∈
        integerRingFieldSubmodule K L := by
    exact hb ((mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) b N _).2
      ⟨y, hyN, rfl⟩)
  have hby_int :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y ∈ 𝒪[L] :=
    (mem_integerRingFieldSubmodule_iff (K := K) (L := L)
      (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y)).1 hby
  let z : 𝒪[L] :=
    ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y, hby_int⟩
  let πL : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπL : πL ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    dsimp [πL]
    exact integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension
      (K := K) (L := L)
  refine (mem_maximalIdealFieldSubmodule_iff (K := K) (L := L) _).2 ?_
  refine ⟨πL * z, Ideal.mul_mem_right z _ hπL, ?_⟩
  dsimp [πL, z]
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) *
      (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y) =
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (b + 1)) * y
  simp [pow_add, map_mul, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A finitely generated submodule has a sufficiently deep uniformizer multiple
inside the maximal ideal.
@isnad1 id=ex.1h3v.s11.061d48c8999b from=translated src=- shape=a739b924 vocab=b8178b76
-/
theorem exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fg
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n N ≤ maximalIdealFieldSubmodule K L := by
  rcases exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
      (K := K) (L := L) hN with
    ⟨b, hb⟩
  exact ⟨b + 1,
    chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule
      (K := K) (L := L) hb⟩

/-- Some uniformizer-power normal-basis lattice lies inside the maximal-ideal field submodule.
@isnad1 id=ex.0h2v.s10.00887bb43ea1 from=translated src=- shape=26a05f95 vocab=145dbd1d
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L :=
  exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fg
    (K := K) (L := L) (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))

/-- A sufficiently deep normal-basis lattice lies in the maximal ideal and is
multiplicatively closed.
@isnad1 id=ex.0h2v.s12.1843100b9aa2 from=translated src=- shape=a14b1558 vocab=ca9eeb9b
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L ∧
      ∀ x : L,
        x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
        ∀ y : L,
          y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
            x * y ∈
              chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule
      (K := K) (L := L) with
    ⟨d, hd⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨max c d, ?_⟩
  intro n hmaxn
  have hcn : c ≤ n := le_trans (le_max_left c d) hmaxn
  have hdn : d ≤ n := le_trans (le_max_right c d) hmaxn
  constructor
  · exact (chosenBaseUniformizerPowSubmodule_antitone
      (K := K) (L := L) (chosenNormalBasisIntegerLattice K L) hdn).trans hd
  · exact hc n hcn

/-- The actual carrier of the classical auxiliary principal-unit lattice
`V^n = 1 + π_K^n M`, viewed as a set of units of `𝒪_L`.

This set becomes a subgroup once inverse closure is supplied by the complete
geometric-series argument.-/
def chosenNormalBasisPrincipalUnitSet (n : Nat) : Set 𝒪[L]ˣ :=
  {u | ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)}

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Characterizes membership in the principal-unit set arising from a normal-basis lattice.
@isnad1 id=iff.0h4v.s11.3e8e1835aab7 from=translated src=- shape=ea908864 vocab=268bd6a1
-/
@[simp]
theorem mem_chosenNormalBasisPrincipalUnitSet_iff (n : Nat) (u : 𝒪[L]ˣ) :
    u ∈ chosenNormalBasisPrincipalUnitSet K L n ↔
      ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
        chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  Iff.rfl

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The identity belongs to the chosen normal-basis principal-unit set.
@isnad1 id=mem.0h3v.s10.4bb003a5419c from=translated src=- shape=14c31f91 vocab=05b5b6fa
-/
theorem chosenNormalBasisPrincipalUnitSet_one_mem (n : Nat) :
    (1 : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  simp

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The chosen normal-basis principal-unit set is closed under multiplication.
@isnad1 id=mem.3h5v.s13.d10f2139b6c8 from=translated src=- shape=77575d96 vocab=840a093c
-/
theorem chosenNormalBasisPrincipalUnitSet_mul_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u v : 𝒪[L]ˣ}
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    u * v ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  let E : Submodule 𝒪[K] L :=
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  let x : L := ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  let y : L := ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hx : x ∈ E := hu
  have hy : y ∈ E := hv
  have hxy : x * y ∈ E := hmul x hx y hy
  have hsum : x * y + x + y ∈ E := by
    exact E.add_mem (E.add_mem hxy hx) hy
  have hunit :
      ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = x * y + x + y := by
    have h :=
      congrArg (fun z : 𝒪[L] => (z : L)) (unit_mul_sub_one_eq L u v)
    simpa [x, y, map_add, map_mul, mul_assoc, mul_comm, mul_left_comm,
      add_assoc, add_comm, add_left_comm] using h
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  rw [hunit]
  exact hsum

/-- Every chosen normal-basis principal unit belongs to the first principal-unit group.
@isnad1 id=mem.2h4v.s12.a8bdc49f77d1 from=translated src=- shape=2228ad43 vocab=337b53c3
-/
theorem chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    u ∈ principalUnits L 1 := by
  rw [mem_principalUnits_iff]
  have hmax :
      ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
        maximalIdealFieldSubmodule K L :=
    hle hu
  rcases (mem_maximalIdealFieldSubmodule_iff (K := K) (L := L)
      ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)).1 hmax with
    ⟨a, ha, haeq⟩
  have ha_eq : a = ((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 :=
    Subtype.ext haeq
  simpa [ha_eq] using ha

/-- There is a multiplicatively closed normal-basis principal-unit set inside
the first principal-unit group.
@isnad1 id=ex.0h2v.s12.d53d8e406c0a from=translated src=- shape=f5a0d9ab vocab=4e3111e1
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      (∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
          u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) ∧
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u ∈ principalUnits L 1 := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  rcases hc n hcn with ⟨hle, hmul⟩
  constructor
  · intro u hu v hv
    exact chosenNormalBasisPrincipalUnitSet_mul_mem (K := K) (L := L) hmul hu hv
  · intro u hu
    exact chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one
      (K := K) (L := L) hle hu

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The inverse-correction partial sums remain in the lattice underlying the principal-unit set.
@isnad1 id=mem.2h5v.s12.2afe6ffb7c67 from=translated src=- shape=43ca8e58 vocab=dc5e2273
-/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) (d : Nat) :
    inverseCorrectionPartialSum (L := L)
        ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d ∈
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  inverseCorrectionPartialSum_mem_of_mul_closed (K := K) (L := L) hmul hu d

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A suitable normal-basis principal-unit set contains every inverse-correction partial sum.
@isnad1 id=ex.0h2v.s11.10d855f99ef3 from=translated src=- shape=f488a22a vocab=ee8e5e5d
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n → ∀ d : Nat,
        inverseCorrectionPartialSum (L := L)
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d ∈
          chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn u hu d
  exact chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem
    (K := K) (L := L) (hc n hcn) hu d

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The inverse-correction product error remains in the chosen lattice.
@isnad1 id=mem.2h5v.s12.3550d469593a from=translated src=- shape=99fa2b17 vocab=735f4932
-/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialProductError_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) (d : Nat) :
    (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
        (1 + inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d) - 1 ∈
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  let E : Submodule 𝒪[K] L :=
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  let x : L := ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hx : x ∈ E := hu
  have herror :
      (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) - 1 ∈ E :=
    inverseCorrectionPartialProductError_mem_of_mul_closed
      (K := K) (L := L) hmul hx d
  have hu_eq : 1 + x = (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    simp [x]
  simpa [E, x, hu_eq] using herror

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A suitable normal-basis principal-unit set contains every inverse-correction product error.
@isnad1 id=ex.0h2v.s11.26d49a8f41ae from=translated src=- shape=359ce20b vocab=e5a44ca8
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialProductError_mem :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n → ∀ d : Nat,
        (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
            (1 + inverseCorrectionPartialSum (L := L)
              ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d) - 1 ∈
          chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn u hu d
  exact chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialProductError_mem
    (K := K) (L := L) (hc n hcn) hu d

/-- Successive powers of the negative deviation from one converge to zero.
@isnad1 id=tendsto.2h4v.s12.ba25b11c1669 from=translated src=- shape=8df37651 vocab=80affbbc
-/
theorem chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat => (-(((u : 𝒪[L]ˣ) : 𝒪[L]) - 1)) ^ (d + 1))
      atTop (nhds (0 : 𝒪[L])) := by
  have hu_one : u ∈ principalUnits L 1 :=
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one
      (K := K) (L := L) hle hu
  have hpow :
      (((u : 𝒪[L]ˣ) : 𝒪[L]) - 1) ∈ (𝓂[L] ^ 1 : Ideal 𝒪[L]) :=
    (mem_principalUnits_iff L u 1).1 hu_one
  have hmax :
      (((u : 𝒪[L]ˣ) : 𝒪[L]) - 1) ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    simpa [pow_one] using hpow
  exact tendsto_neg_pow_succ_of_mem_maximalIdeal L hmax

/-- A suitable normal-basis principal-unit set has powers of the negative
deviation converging to zero.
@isnad1 id=ex.0h2v.s11.b98188851f3e from=translated src=- shape=41aeb3c5 vocab=a525dc1a
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        Tendsto
          (fun d : Nat => (-(((u : 𝒪[L]ˣ) : 𝒪[L]) - 1)) ^ (d + 1))
          atTop (nhds (0 : 𝒪[L])) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn u hu
  have hle :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L :=
    (chosenBaseUniformizerPowSubmodule_antitone
      (K := K) (L := L) (m := c) (n := n)
      (chosenNormalBasisIntegerLattice K L) hcn).trans hc
  exact chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
    (K := K) (L := L) hle hu

/-- The inverse-correction partial products converge to one.
@isnad1 id=tendsto.2h4v.s12.6721ba1122df from=translated src=- shape=495a5e86 vocab=911f6857
-/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat =>
        (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
          (1 + inverseCorrectionPartialSum (L := L)
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d))
      atTop (nhds (1 : L)) := by
  let x𝒪 : 𝒪[L] := ((u : 𝒪[L]ˣ) : 𝒪[L]) - 1
  let x : L := (x𝒪 : L)
  have hres𝒪 :
      Tendsto (fun d : Nat => (-x𝒪) ^ (d + 1)) atTop (nhds (0 : 𝒪[L])) := by
    simpa [x𝒪] using
      chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
        (K := K) (L := L) hle hu
  have hresL :
      Tendsto (fun d : Nat => ((((-x𝒪) ^ (d + 1) : 𝒪[L]) : L)))
        atTop (nhds (0 : L)) :=
    (continuous_subtype_val.tendsto (0 : 𝒪[L])).comp hres𝒪
  have htarget :
      Tendsto (fun d : Nat => (1 : L) - ((((-x𝒪) ^ (d + 1) : 𝒪[L]) : L)))
        atTop (nhds (1 : L)) := by
    simpa using (tendsto_const_nhds (x := (1 : L))).sub hresL
  refine htarget.congr' (Eventually.of_forall ?_)
  intro d
  have hgeom :
      (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) =
        1 - (-x) ^ (d + 1) :=
    one_add_mul_one_add_inverseCorrectionPartialSum (L := L) x d
  have hu_eq : 1 + x = (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    simp [x, x𝒪]
  simpa [x, x𝒪, hu_eq] using hgeom.symm

/-- One plus the inverse correction converges to the multiplicative inverse.
@isnad1 id=tendsto.2h4v.s12.38279c143505 from=translated src=- shape=df0adf88 vocab=2ba94e77
-/
theorem chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat =>
        1 + inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
      atTop (nhds ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))) := by
  have hprod :=
    chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one
      (K := K) (L := L) hle hu
  have hmul :
      Tendsto
        (fun d : Nat =>
          (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
              (1 + inverseCorrectionPartialSum (L := L)
                ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)))
        atTop (nhds ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))) := by
    simpa using
      (tendsto_const_nhds (x := (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))).mul hprod
  refine hmul.congr' (Eventually.of_forall ?_)
  intro d
  have huinv :
      ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L)) *
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) : L)) = 1 := by
    have huinvₒ :
        (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) * ((u : 𝒪[L]ˣ) : 𝒪[L])) = 1 :=
      Units.inv_mul u
    exact congrArg (algebraMap 𝒪[L] L) huinvₒ
  rw [← mul_assoc, huinv, one_mul]

/-- The inverse correction converges to the inverse minus one.
@isnad1 id=tendsto.2h4v.s12.7886510be7aa from=translated src=- shape=e01968c3 vocab=bd625d07
-/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat =>
        inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
      atTop (nhds (((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1))) := by
  have h :=
    chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv
      (K := K) (L := L) hle hu
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    h.sub (tendsto_const_nhds (x := (1 : L)))

/-- A suitable normal-basis principal-unit set admits inverse corrections
converging to the inverse minus one.
@isnad1 id=ex.0h2v.s11.1d3b186ad4a6 from=translated src=- shape=e3c6c150 vocab=d4b55049
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        Tendsto
          (fun d : Nat =>
            inverseCorrectionPartialSum (L := L)
              ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
          atTop (nhds (((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1))) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn u hu
  have hle :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L :=
    (chosenBaseUniformizerPowSubmodule_antitone
      (K := K) (L := L) (m := c) (n := n)
      (chosenNormalBasisIntegerLattice K L) hcn).trans hc
  exact chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
    (K := K) (L := L) hle hu

/-- Closedness of the lattice puts the inverse minus one back in the lattice.
@isnad1 id=mem.4h4v.s13.259dcb873455 from=translated src=- shape=e771999d vocab=ef6e3762
-/
theorem chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  let E : Submodule 𝒪[K] L :=
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  have hlim :
      (((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1)) ∈ E := by
    exact submodule_mem_of_tendsto_of_forall_mem_of_closed
      (K := K) (L := L) (E := E) hclosed
      (chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
        (K := K) (L := L) hle hu)
      (fun d => chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem
        (K := K) (L := L) hmul hu d)
  simpa [E] using hlim

/-- A closed normal-basis principal-unit set is closed under inversion.
@isnad1 id=mem.4h4v.s13.8abbb7c0308f from=translated src=- shape=96fc34a4 vocab=177a8272
-/
theorem chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  exact chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed
    (K := K) (L := L) hclosed hle hmul hu

/-- There is a closed normal-basis principal-unit set stable under inversion.
@isnad1 id=ex.0h2v.s11.8a08875614c3 from=translated src=- shape=36880bae vocab=8a096976
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      IsClosed
        ((chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L) : Set L)) →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn hclosed u hu
  rcases hc n hcn with ⟨hle, hmul⟩
  exact chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
    (K := K) (L := L) hclosed hle hmul hu

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- The range of the integer-ring inclusion is the integer-ring field submodule.
@isnad1 id=eq.0h2v.s11.b5abd82000ad from=translated src=- shape=c45287ff vocab=bdb715cd
-/
theorem integerRingToFieldLinearMap_range_eq :
    LinearMap.range (integerRingToFieldLinearMap K L) =
      integerRingFieldSubmodule K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- If the extension valuation ring is finite over the base valuation ring, then
`𝒪_L`, viewed inside `L`, is a finitely generated `𝒪_K`-submodule.
@isnad1 id=fg.0h2v.s10.30f27a9b9c4e from=translated src=- shape=ac4a7cff vocab=845b7052
-/
theorem integerRingFieldSubmodule_fg_of_moduleFinite
    [Module.Finite 𝒪[K] 𝒪[L]] :
    (integerRingFieldSubmodule K L).FG := by
  have hfg :
      Submodule.FG
        ((⊤ : Submodule 𝒪[K] 𝒪[L]).map (integerRingToFieldLinearMap K L)) :=
    (Module.Finite.fg_top (R := 𝒪[K]) (M := 𝒪[L])).map
      (integerRingToFieldLinearMap K L)
  have hmap :
      (⊤ : Submodule 𝒪[K] 𝒪[L]).map (integerRingToFieldLinearMap K L) =
        integerRingFieldSubmodule K L := by
    rw [Submodule.map_top]
    exact integerRingToFieldLinearMap_range_eq (K := K) (L := L)
  simpa [hmap] using hfg

/-- The reverse lattice bound: if `𝒪_L` is finite over `𝒪_K`, then a
single high enough base-uniformizer power sends `𝒪_L` into the normal-basis
lattice `M`.
@isnad1 id=ex.0h2v.s11.14d54070cc6a from=translated src=- shape=7cae47df vocab=27cf3f6b
-/
theorem exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLattice
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (integerRingFieldSubmodule K L) ≤
        chosenNormalBasisIntegerLattice K L :=
  exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (N := integerRingFieldSubmodule K L)
    (integerRingFieldSubmodule_fg_of_moduleFinite (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

/-- Some uniformizer-power normal-basis lattice is a neighborhood of zero.
@isnad1 id=ex.0h2v.s10.db97f1940235 from=translated src=- shape=89ccc489 vocab=51665bba
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)) ∈ nhds (0 : L) := by
  rcases exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLattice
      (K := K) (L := L) with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro n han
  rcases Nat.exists_eq_add_of_le han with ⟨d, rfl⟩
  exact Filter.mem_of_superset
    (chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero
      (K := K) (L := L) (a + (a + d)))
    (chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
      (K := K) (L := L) (N := integerRingFieldSubmodule K L)
      (M := chosenNormalBasisIntegerLattice K L) (a := a) (n := a + d) ha)

/-- Some uniformizer-power normal-basis lattice is closed.
@isnad1 id=ex.0h2v.s10.60055cb78bf8 from=translated src=- shape=ad9063c0 vocab=7796e407
-/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      IsClosed
        ((chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L) : Set L)) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  exact submodule_isClosed_of_mem_nhds_zero
    (K := K) (L := L) (E := chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L)) (hc n hcn)

/-- There is a chosen normal-basis principal-unit set stable under inversion.
@isnad1 id=ex.0h2v.s11.31ad2ebdd917 from=translated src=- shape=5c7e85d6 vocab=923c6f58
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_inv_mem
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
      (K := K) (L := L) with
    ⟨c₁, hc₁⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed
      (K := K) (L := L) with
    ⟨c₂, hc₂⟩
  refine ⟨max c₁ c₂, ?_⟩
  intro n hmaxn u hu
  have hc₁n : c₁ ≤ n := le_trans (le_max_left c₁ c₂) hmaxn
  have hc₂n : c₂ ≤ n := le_trans (le_max_right c₁ c₂) hmaxn
  exact hc₁ n hc₁n (hc₂ n hc₂n) u hu

/-- There exists a principal-unit subgroup arising from a chosen normal-basis lattice.
@isnad1 id=ex.0h2v.s12.85f2d92dd317 from=translated src=- shape=e572d40e vocab=fd6ac5d2
-/
theorem exists_chosenNormalBasisPrincipalUnitSubgroup
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ V : Subgroup 𝒪[L]ˣ,
        (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n ∧
        V ≤ principalUnits L 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_one
      (K := K) (L := L) with
    ⟨c₁, hc₁⟩
  rcases exists_chosenNormalBasisPrincipalUnitSet_inv_mem
      (K := K) (L := L) with
    ⟨c₂, hc₂⟩
  refine ⟨max c₁ c₂, ?_⟩
  intro n hmaxn
  have hc₁n : c₁ ≤ n := le_trans (le_max_left c₁ c₂) hmaxn
  have hc₂n : c₂ ≤ n := le_trans (le_max_right c₁ c₂) hmaxn
  rcases hc₁ n hc₁n with ⟨hmul, hle_one⟩
  let V : Subgroup 𝒪[L]ˣ := {
    carrier := chosenNormalBasisPrincipalUnitSet K L n
    one_mem' := chosenNormalBasisPrincipalUnitSet_one_mem (K := K) (L := L) n
    mul_mem' := by
      intro u v hu hv
      exact hmul u hu v hv
    inv_mem' := by
      intro u hu
      exact hc₂ n hc₂n u hu }
  refine ⟨V, rfl, ?_⟩
  intro u hu
  exact hle_one u hu

end
end CyclicCohomology

universe u

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-! ### Additive quotient boundary -/

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The principal-unit lattice carriers form a descending filtration.
@isnad1 id=le.0h3v.s9.68118e005ad9 from=translated src=- shape=32893381 vocab=15abfcf7
-/
theorem chosenNormalBasisPrincipalUnitSet_succ_subset (n : Nat) :
    chosenNormalBasisPrincipalUnitSet K L (n + 1) ⊆
      chosenNormalBasisPrincipalUnitSet K L n := by
  intro u hu
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff] at hu ⊢
  exact chosenBaseUniformizerPowSubmodule_succ_le
    (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) hu

/-- The denominator submodule `π_K^(n+1)M`, viewed inside `π_K^nM`.-/
def chosenNormalBasisLatticeSuccSubmodule (n : Nat) :
    Submodule 𝒪[K]
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :=
  (chosenBaseUniformizerPowSubmodule K L (n + 1)
    (chosenNormalBasisIntegerLattice K L)).submoduleOf
      (chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L))

/-- The additive quotient `π_K^nM / π_K^(n+1)M` used in the local class-field calculation.-/
def chosenNormalBasisLatticeSuccQuot (n : Nat) : Type u :=
  (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
    chosenNormalBasisLatticeSuccSubmodule K L n

/-- A successive quotient of normal-basis lattices is an additive commutative group.-/
instance chosenNormalBasisLatticeSuccQuotAddCommGroup (n : Nat) :
    AddCommGroup (chosenNormalBasisLatticeSuccQuot K L n) := by
  change AddCommGroup
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n)
  infer_instance

/-- A successive normal-basis lattice quotient carries the natural residue-field
module structure.-/
instance chosenNormalBasisLatticeSuccQuotModule (n : Nat) :
    Module 𝒪[K] (chosenNormalBasisLatticeSuccQuot K L n) := by
  change Module 𝒪[K]
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n)
  infer_instance

/-- Explicit access to the concrete submodule quotient implementing the
chosen normal-basis lattice graded piece.-/
def chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) := by
  change
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) ≃ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n)
  exact LinearEquiv.refl 𝒪[K] _

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Characterizes membership in the next normal-basis lattice submodule.
@isnad1 id=iff.0h4v.s13.52801b8422ab from=translated src=- shape=62e03286 vocab=7c389a4c
-/
@[simp]
theorem mem_chosenNormalBasisLatticeSuccSubmodule_iff (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    x ∈ chosenNormalBasisLatticeSuccSubmodule K L n ↔
      (x : L) ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L) :=
  Iff.rfl

/-- The quotient map `π_K^nM -> π_K^nM / π_K^(n+1)M`.-/
def chosenNormalBasisLatticeSuccQuotMk (n : Nat) :
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →ₗ[𝒪[K]]
      chosenNormalBasisLatticeSuccQuot K L n := by
  change
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n)
  exact (chosenNormalBasisLatticeSuccSubmodule K L n).mkQ

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The concrete linear equivalence sends a lattice element to its canonical quotient class.
@isnad1 id=eq.0h4v.s15.4e2c5fecad12 from=translated src=- shape=f80022ca vocab=9304187e
-/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mk (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv K L n
        (chosenNormalBasisLatticeSuccQuotMk K L n x) =
      Submodule.Quotient.mk x :=
  rfl

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Eliminate a chosen normal-basis lattice quotient through arbitrary
representatives and its canonical class map.
@isnad1 id=var.0h6v.s13.0b541cfc3d32 from=translated src=- shape=a3d64745 vocab=fd7ad5e8
-/
protected theorem chosenNormalBasisLatticeSuccQuot.inductionOn
    (n : Nat)
    {motive : chosenNormalBasisLatticeSuccQuot K L n → Prop}
    (q : chosenNormalBasisLatticeSuccQuot K L n)
    (h : ∀ x :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L),
      motive (chosenNormalBasisLatticeSuccQuotMk K L n x)) :
    motive q := by
  change motive
    (show
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n from q)
  exact
    Submodule.Quotient.induction_on
      (chosenNormalBasisLatticeSuccSubmodule K L n) q h

/-- Descend a representative-level function constant modulo the next chosen
normal-basis lattice.-/
def chosenNormalBasisLatticeSuccQuotLift
    {P : Sort*} (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) → P)
    (h : ∀ x y, x - y ∈ chosenNormalBasisLatticeSuccSubmodule K L n →
      f x = f y) :
    chosenNormalBasisLatticeSuccQuot K L n → P := by
  change
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n) → P)
  refine Quotient.lift f ?_
  intro x y hxy
  have hq :
      (Submodule.Quotient.mk x :
        (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ⧸
          chosenNormalBasisLatticeSuccSubmodule K L n)) =
        Submodule.Quotient.mk y :=
    Quotient.sound hxy
  exact h x y
    ((Submodule.Quotient.eq
      (chosenNormalBasisLatticeSuccSubmodule K L n)).1 hq)

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The lifted map on a successive lattice quotient evaluates to the original
map on representatives.
@isnad1 id=eq.1h6v.s14.245da6cf5f5b from=translated src=- shape=2b65db9b vocab=c02da81f
-/
@[simp] theorem chosenNormalBasisLatticeSuccQuotLift_mk
    {P : Sort*} (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) → P)
    (h : ∀ x y, x - y ∈ chosenNormalBasisLatticeSuccSubmodule K L n →
      f x = f y)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotLift K L n f h
        (chosenNormalBasisLatticeSuccQuotMk K L n x) = f x :=
  rfl

/-- Descend a linear map vanishing on the next chosen normal-basis lattice.-/
def chosenNormalBasisLatticeSuccQuotLinearLift
    {M : Type*} [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
        →ₗ[𝒪[K]] M)
    (h : chosenNormalBasisLatticeSuccSubmodule K L n ≤ f.ker) :
    chosenNormalBasisLatticeSuccQuot K L n →ₗ[𝒪[K]] M := by
  change
    (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n) →ₗ[𝒪[K]] M
  exact (chosenNormalBasisLatticeSuccSubmodule K L n).liftQ f h

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The lifted linear map agrees with the original linear map on quotient representatives.
@isnad1 id=eq.1h6v.s15.7db4ef47acc2 from=translated src=- shape=922ca001 vocab=50a1f596
-/
@[simp] theorem chosenNormalBasisLatticeSuccQuotLinearLift_mk
    {M : Type*} [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
        →ₗ[𝒪[K]] M)
    (h : chosenNormalBasisLatticeSuccSubmodule K L n ≤ f.ker)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotLinearLift K L n f h
        (chosenNormalBasisLatticeSuccQuotMk K L n x) = f x :=
  rfl

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A lattice representative gives zero in the successive quotient exactly
when it lies at the next level.
@isnad1 id=iff.0h4v.s13.e2282a713b91 from=translated src=- shape=1c624306 vocab=a8f1b118
-/
theorem chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotMk K L n x = 0 ↔
      (x : L) ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L) := by
  change
    (Submodule.Quotient.mk x :
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Two lattice representatives agree in the successive quotient exactly when
their difference lies at the next level.
@isnad1 id=iff.0h5v.s15.3ac7ae8ae439 from=translated src=- shape=1594ed7f vocab=f29103c7
-/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotMk_eq_iff (n : Nat)
    (x y :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotMk K L n x =
        chosenNormalBasisLatticeSuccQuotMk K L n y ↔
      x - y ∈ chosenNormalBasisLatticeSuccSubmodule K L n := by
  change
    (Submodule.Quotient.mk x :
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) =
      Submodule.Quotient.mk y ↔ _
  exact Submodule.Quotient.eq (chosenNormalBasisLatticeSuccSubmodule K L n)

/-- The additive quotient class of `u - 1` for `u ∈ V^n`.-/
def chosenNormalBasisPrincipalUnitLatticeClass (n : Nat)
    (u : 𝒪[L]ˣ) (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisLatticeSuccQuot K L n :=
  chosenNormalBasisLatticeSuccQuotMk K L n
    ⟨((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L), hu⟩

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A principal unit has zero lattice class exactly when its deviation from one
lies at the next level.
@isnad1 id=iff.1h4v.s11.056ee1d65e27 from=translated src=- shape=8391faa7 vocab=3489a6f2
-/
theorem chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff {n : Nat}
    (u : 𝒪[L]ˣ) (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitLatticeClass K L n u hu = 0 ↔
      u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
  rw [chosenNormalBasisPrincipalUnitLatticeClass,
    chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff]
  rfl

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The multiplicative error term for units in `V^n` is one lattice step deeper
whenever products of elements of `π_K^nM` land in `π_K^(n+1)M`.
@isnad1 id=mem.3h5v.s13.22b72c3388a2 from=translated src=- shape=a01c9629 vocab=4663b989
-/
theorem chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ {n : Nat}
    (hmul_succ : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L))
    {u v : 𝒪[L]ˣ}
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
        (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
          ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L) := by
  let x : L := ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  let y : L := ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hx : x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) := hu
  have hy : y ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) := hv
  have hxy : x * y ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
      (chosenNormalBasisIntegerLattice K L) :=
    hmul_succ x hx y hy
  have hunit :
      ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = x * y + x + y := by
    have h :=
      congrArg (fun z : 𝒪[L] => (z : L)) (unit_mul_sub_one_eq L u v)
    simpa [x, y, map_add, map_mul, mul_assoc, mul_comm, mul_left_comm,
      add_assoc, add_comm, add_left_comm] using h
  change
    ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) - (x + y) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)
  rw [hunit]
  convert hxy using 1 ; ring

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A suitable normal-basis principal-unit set has multiplication error in the
next lattice level.
@isnad1 id=ex.0h2v.s12.43d5917bdec5 from=translated src=- shape=5dff85d9 vocab=0c6cbeb3
-/
theorem exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
          (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
              (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
                ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1)
              (chosenNormalBasisIntegerLattice K L) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succ
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn u hu v hv
  exact chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ
    (K := K) (L := L) (hc n hcn) hu hv

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The lattice class of a product of principal units is the sum of their lattice classes.
@isnad1 id=eq.4h5v.s13.279c9095cbe0 from=translated src=- shape=aa271e07 vocab=6e8123de
-/
theorem chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add {n : Nat}
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u v : 𝒪[L]ˣ)
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (huv : u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitLatticeClass K L n (u * v) huv =
      chosenNormalBasisPrincipalUnitLatticeClass K L n u hu +
        chosenNormalBasisPrincipalUnitLatticeClass K L n v hv := by
  rw [chosenNormalBasisPrincipalUnitLatticeClass, chosenNormalBasisPrincipalUnitLatticeClass,
    chosenNormalBasisPrincipalUnitLatticeClass]
  rw [← map_add, chosenNormalBasisLatticeSuccQuotMk_eq_iff,
    mem_chosenNormalBasisLatticeSuccSubmodule_iff]
  change
    (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
        (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
          ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)
  exact hmul_error u hu v hv

/-- There exists a nested pair of normal-basis principal-unit subgroups at successive levels.
@isnad1 id=ex.0h2v.s13.44f1e04385cc from=translated src=- shape=25809350 vocab=0c59a59d
-/
theorem exists_chosenNormalBasisPrincipalUnitSubgroupSuccPair
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ Vn Vsucc : Subgroup 𝒪[L]ˣ,
        (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n ∧
        (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1) ∧
        Vsucc ≤ Vn ∧
        Vn ≤ principalUnits L 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  rcases hc n hcn with ⟨Vn, hVn, hVnle⟩
  have hcsucc : c ≤ n + 1 := le_trans hcn (Nat.le_succ n)
  rcases hc (n + 1) hcsucc with ⟨Vsucc, hVsucc, _hVsuccle⟩
  refine ⟨Vn, Vsucc, hVn, hVsucc, ?_, hVnle⟩
  intro u hu
  have hu_succ : u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
    exact hVsucc ▸ hu
  have hu_n : u ∈ chosenNormalBasisPrincipalUnitSet K L n :=
    chosenNormalBasisPrincipalUnitSet_succ_subset (K := K) (L := L) n hu_succ
  change u ∈ (Vn : Set 𝒪[L]ˣ)
  exact hVn.symm ▸ hu_n

/-- The subgroup of `Vn` obtained from an included next-step subgroup
`Vsucc ≤ Vn`.  This is the denominator used for the multiplicative quotient
`V^n / V^(n+1)`.-/
def chosenNormalBasisPrincipalUnitSuccSubgroup {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (_hV : Vsucc ≤ Vn) : Subgroup Vn :=
  Vsucc.subgroupOf Vn

/-- Characterizes membership in the next normal-basis principal-unit subgroup.
@isnad1 id=iff.1h4v.s14.fd1892d168a0 from=translated src=- shape=7d9bfe47 vocab=4cdff18f
-/
theorem mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    u ∈ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ↔
      (u : 𝒪[L]ˣ) ∈ Vsucc := by
  rw [chosenNormalBasisPrincipalUnitSuccSubgroup]
  exact Subgroup.mem_subgroupOf

/-- The multiplicative successive quotient `Vn / Vsucc`, for an actual inclusion
`Vsucc ≤ Vn`.-/
def chosenNormalBasisPrincipalUnitSuccQuot
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) : Type u :=
  Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV

/-- The quotient by the next normal-basis principal-unit subgroup is a commutative group.-/
instance chosenNormalBasisPrincipalUnitSuccQuotCommGroup
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    CommGroup (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) := by
  change CommGroup
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  infer_instance

/-- Explicit access to the concrete group quotient implementing the chosen
normal-basis principal-unit graded piece.-/
def chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) := by
  change
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) ≃*
      (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact MulEquiv.refl _

/-- The quotient map `Vn -> Vn / Vsucc`.-/
def chosenNormalBasisPrincipalUnitSuccQuotMk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    Vn →* chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV := by
  change Vn →*
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact QuotientGroup.mk'
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

/-- The concrete principal-unit quotient equivalence sends an element to its canonical class.
@isnad1 id=eq.1h4v.s17.763794678cb7 from=translated src=- shape=88ccec75 vocab=99996656
-/
@[simp] theorem chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv_mk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv (L := L) hV
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
      QuotientGroup.mk u :=
  rfl

/-- Every successive principal-unit quotient class has a representative.
@isnad1 id=surjecti.1h3v.s15.5c1ae23089dd from=translated src=- shape=d3a38dea vocab=6917a5c4
-/
theorem chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    Function.Surjective
      (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV) :=
  QuotientGroup.mk'_surjective
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

/-- Eliminate a chosen normal-basis principal-unit quotient through arbitrary
representatives and its canonical class map.
@isnad1 id=var.1h6v.s15.4830c1aae755 from=translated src=- shape=75038f44 vocab=753b9ebc
-/
protected theorem chosenNormalBasisPrincipalUnitSuccQuot.inductionOn
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    {motive : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV → Prop}
    (q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
    (h : ∀ u : Vn,
      motive (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u)) :
    motive q := by
  change motive
    (show Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV from q)
  refine QuotientGroup.induction_on q ?_
  intro u
  exact h u

/-- Descend a homomorphism that kills the included next-step subgroup.-/
def chosenNormalBasisPrincipalUnitSuccQuotLift
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} {H : Type*} [Group H]
    (hV : Vsucc ≤ Vn) (f : Vn →* H)
    (h : chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ≤ f.ker) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV →* H := by
  change
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) →* H
  exact QuotientGroup.lift
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) f h

/-- A map lifted from the successive principal-unit quotient agrees on representatives.
@isnad1 id=eq.2h6v.s16.7876f494e789 from=translated src=- shape=b0eab5ca vocab=7dcb603e
-/
@[simp] theorem chosenNormalBasisPrincipalUnitSuccQuotLift_mk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} {H : Type*} [Group H]
    (hV : Vsucc ≤ Vn) (f : Vn →* H)
    (h : chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ≤ f.ker)
    (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotLift (L := L) hV f h
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) = f u :=
  rfl

/-- A principal unit represents the identity exactly when it lies in the next subgroup.
@isnad1 id=iff.1h4v.s15.d9bd6dd8a65c from=translated src=- shape=f70eca9f vocab=1a138194
-/
theorem chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u = 1 ↔
      (u : 𝒪[L]ˣ) ∈ Vsucc := by
  change
    (QuotientGroup.mk u :
      Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff (L := L) hV u

/-- Two principal units represent the same class exactly when their quotient
lies in the next subgroup.
@isnad1 id=iff.1h5v.s16.9e8dbd868865 from=translated src=- shape=c4ad375a vocab=064e3a54
-/
@[simp] theorem chosenNormalBasisPrincipalUnitSuccQuotMk_eq_iff_div_mem
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u v : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u =
        chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV v ↔
      u / v ∈ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV := by
  change
    (QuotientGroup.mk u :
      Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) =
      QuotientGroup.mk v ↔ _
  exact QuotientGroup.eq_iff_div_mem
    (N := chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

/-- The map `u ↦ u - 1` from a subgroup `Vn = V^n` to the additive
successive quotient, viewed multiplicatively on the target.-/
def chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom (n : Nat)
    {Vn : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    Vn →* Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) where
  toFun u :=
    Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
        (by
          exact hVn ▸ u.2))
  map_one' := by
    change chosenNormalBasisPrincipalUnitLatticeClass K L n
      (1 : 𝒪[L]ˣ) (by exact hVn ▸ (1 : Vn).2) = 0
    rw [chosenNormalBasisPrincipalUnitLatticeClass,
      chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff]
    simp
  map_mul' := by
    intro u v
    have hu : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ u.2
    have hv : (v : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ v.2
    have huv : ((u * v : Vn) : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ (u * v).2
    have hclass :=
      chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add
        (K := K) (L := L) hmul_error (u : 𝒪[L]ˣ) (v : 𝒪[L]ˣ) hu hv huv
    simpa using congrArg Multiplicative.ofAdd hclass

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Principal units from the next level lie in the kernel of the lattice-class homomorphism.
@isnad1 id=mem.4h6v.s15.81c051e5807f from=translated src=- shape=b4132324 vocab=f80623f5
-/
theorem chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u : Vn) (hu : (u : 𝒪[L]ˣ) ∈ Vsucc) :
    u ∈ (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom
      K L n hVn hmul_error).ker := by
  rw [MonoidHom.mem_ker]
  have hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    exact hVn ▸ u.2
  have hu_succ : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
    exact hVsucc ▸ hu
  have hzero :
      chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 :=
    (chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff
      (K := K) (L := L) (u : 𝒪[L]ˣ) hu_n).2 hu_succ
  change Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n) = 1
  simpa using congrArg Multiplicative.ofAdd hzero

/-- The induced map
`Vn/Vsucc -> π_K^nM/π_K^(n+1)M`, with the additive quotient target viewed as a
multiplicative group.-/
def chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom (n : Nat)
    {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV →*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) :=
  chosenNormalBasisPrincipalUnitSuccQuotLift (L := L) hV
    (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom K L n hVn hmul_error)
    (by
      intro u hu
      have hu_succ : (u : 𝒪[L]ˣ) ∈ Vsucc :=
        (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff (L := L) hV u).1 hu
      exact chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ
        (K := K) (L := L) hVn hVsucc hmul_error u hu_succ)

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The induced quotient homomorphism sends a principal-unit class to its lattice class.
@isnad1 id=eq.4h6v.s16.5e3477cf9d5f from=translated src=- shape=e5579f46 vocab=0a19cf93
-/
theorem chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_mk
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
      chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom K L n hVn hmul_error u :=
  rfl

end
end CyclicCohomology
