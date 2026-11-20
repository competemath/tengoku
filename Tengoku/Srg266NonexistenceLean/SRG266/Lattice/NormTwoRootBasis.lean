/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADECartanGraph
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRoots
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntLinearMap
import Tengoku.Seed.Algebra.Group.Irreducible.Indecomposable
import Tengoku.Seed.Algebra.Module.Submodule.Union
import Tengoku.Seed.LinearAlgebra.QuadraticForm.Dual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open Function Set

def simpleRootSet {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) : Set (NormTwoRoot L) :=
  IsAddIndecomposable.baseOf normTwoRootVal f

noncomputable instance simpleRootSetFintype
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) : Fintype (simpleRootSet f) :=
  Fintype.ofFinite _

/--
@isnad1 id=or.1h4v.s10.f7d3ae3ae068 from=translated src=- shape=a430148a vocab=135644cf
-/
theorem normTwoRoot_mem_or_neg_mem_simple_closure
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (r : NormTwoRoot L) :
    normTwoRootVal r ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) ∨
      -normTwoRootVal r ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) := by
  simpa [simpleRootSet] using
    (IsAddIndecomposable.mem_or_neg_mem_closure_baseOf normTwoRootVal f r (hf r) (by simp))

/--
@isnad1 id=ex.2h4v.s10.2a7d73531984 from=translated src=- shape=5d47c4db vocab=b564ed01
-/
theorem sub_mem_normTwoRoots_of_pairing_pos
    {n : ℕ} {L : PDUnimodularLattice n} {r s : NormTwoRoot L}
    (hrs : r ≠ s) (hpos : 0 < L.pairing r.1 s.1) :
    ∃ t : NormTwoRoot L, normTwoRootVal r - normTwoRootVal s = normTwoRootVal t := by
  have hne : r.1 - s.1 ≠ 0 := by
    intro h
    apply hrs
    apply Subtype.ext
    exact sub_eq_zero.mp h
  have hqpos := L.positiveDefinite (r.1 - s.1) hne
  have hsym : L.pairing s.1 r.1 = L.pairing r.1 s.1 := L.symmetric.eq _ _
  simp only [map_sub, LinearMap.sub_apply] at hqpos
  rw [r.2, s.2, hsym] at hqpos
  have hnorm : L.pairing (r.1 - s.1) (r.1 - s.1) = 2 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [r.2, s.2, hsym]
    omega
  exact ⟨⟨r.1 - s.1, hnorm⟩, rfl⟩

/--
@isnad1 id=pairwise.1h3v.s10.957aa78cc3a1 from=translated src=- shape=e160b825 vocab=6fbec4d9
-/
theorem simpleRootSet_pairwise_pairing_nonpos
    {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0) :
    (simpleRootSet f).Pairwise fun r s => L.pairing r.1 s.1 ≤ 0 := by
  have hsub := IsAddIndecomposable.pairwise_baseOf_sub_notMem
    normTwoRootVal (fun r => by simp) f hf
  intro r hr s hs hrs
  by_contra hnot
  have hpos : 0 < L.pairing r.1 s.1 := lt_of_not_ge hnot
  obtain ⟨t, ht⟩ := sub_mem_normTwoRoots_of_pairing_pos hrs hpos
  exact hsub hr hs hrs ⟨t, ht.symm⟩

/--
@isnad1 id=linearin.1h3v.s9.85d7ba832143 from=translated src=- shape=c501f479 vocab=01cefde2
-/
theorem simpleRootSet_linearIndepOn
    {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0) :
    LinearIndepOn ℤ normTwoRootVal (simpleRootSet f) := by
  change LinearIndependent ℤ (fun r : simpleRootSet f => normTwoRootVal r.1)
  apply LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero L.pairing
    L.positiveDefinite (toZLinearMap f)
  · rintro ⟨r, hr⟩
    change IsAddIndecomposable normTwoRootVal
      {i | 0 < f (normTwoRootVal i)} r at hr
    exact hr.1
  · rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs
    exact simpleRootSet_pairwise_pairing_nonpos f hf hr hs (by simpa using hrs)

noncomputable def simpleRootGraph
    {n : ℕ} {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ) :
    SimpleGraph (simpleRootSet f) :=
  SimpleGraph.fromRel fun r s => L.pairing r.1.1 s.1.1 = -1

/--
@isnad1 id=iff.0h5v.s10.d9dc68f66ee0 from=translated src=- shape=5a9d7738 vocab=58ff8fd4
-/
theorem simpleRootGraph_adj_iff
    {n : ℕ} {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    (r s : simpleRootSet f) :
    (simpleRootGraph f).Adj r s ↔
      r ≠ s ∧ L.pairing r.1.1 s.1.1 = -1 := by
  rw [simpleRootGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hrs, h | h⟩
    · exact ⟨hrs, h⟩
    · exact ⟨hrs, L.symmetric.eq _ _ ▸ h⟩
  · rintro ⟨hrs, h⟩
    exact ⟨hrs, Or.inl h⟩

/--
@isnad1 id=ne.0h5v.s10.eed909bd894e from=translated src=- shape=b6601a4f vocab=754877b9
-/
theorem simpleRoot_add_ne_zero
    {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) {r s : simpleRootSet f} :
    r.1.1 + s.1.1 ≠ 0 := by
  intro hrs
  have hrpos : 0 < f r.1.1 := by
    have hr := r.2
    change IsAddIndecomposable normTwoRootVal
      {i | 0 < f (normTwoRootVal i)} r.1 at hr
    exact hr.1
  have hspos : 0 < f s.1.1 := by
    have hs := s.2
    change IsAddIndecomposable normTwoRootVal
      {i | 0 < f (normTwoRootVal i)} s.1 at hs
    exact hs.1
  have := congrArg f hrs
  simp only [map_add, map_zero] at this
  omega

/--
@isnad1 id=or.2h5v.s11.d35b184aaa0c from=translated src=- shape=e03ffef0 vocab=74ecdac3
-/
theorem simpleRoot_pairing_eq_zero_or_neg_one
    {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    {r s : simpleRootSet f} (hrs : r ≠ s) :
    L.pairing r.1.1 s.1.1 = 0 ∨ L.pairing r.1.1 s.1.1 = -1 := by
  have hrs' : r.1 ≠ s.1 := fun h => hrs (Subtype.ext h)
  have hnonpos := simpleRootSet_pairwise_pairing_nonpos f hf r.2 s.2
    hrs'
  have hpos := L.positiveDefinite (r.1.1 + s.1.1) (simpleRoot_add_ne_zero f)
  have hsym : L.pairing s.1.1 r.1.1 = L.pairing r.1.1 s.1.1 := L.symmetric.eq _ _
  simp only [map_add, LinearMap.add_apply] at hpos
  rw [r.1.2, s.1.2, hsym] at hpos
  omega

/--
@isnad1 id=eq.1h5v.s10.762ae8dd2f4d from=translated src=- shape=791ade7a vocab=10023500
-/
theorem graphCartanMatrix_simpleRootGraph
    {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (r s : simpleRootSet f) :
    graphCartanMatrix (simpleRootGraph f) r s = L.pairing r.1.1 s.1.1 := by
  classical
  by_cases hrs : r = s
  · subst s
    rw [graphCartanMatrix_apply_same, r.1.2]
  · rcases simpleRoot_pairing_eq_zero_or_neg_one f hf hrs with hzero | hneg
    · rw [graphCartanMatrix_apply_of_not_adj hrs]
      · exact hzero.symm
      · rw [simpleRootGraph_adj_iff]
        simp [hrs, hzero]
    · rw [graphCartanMatrix_apply_of_adj]
      · exact hneg.symm
      · rw [simpleRootGraph_adj_iff]
        exact ⟨hrs, hneg⟩

noncomputable def simpleRootCombination
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) : (simpleRootSet f → ℤ) →ₗ[ℤ] L.carrier :=
  Fintype.linearCombination ℤ fun r : simpleRootSet f => (r.1.1 : L.carrier)

/--
@isnad1 id=injectiv.1h3v.s9.870a03d13fcf from=translated src=- shape=b18e2f3e vocab=a8fba213
-/
theorem simpleRootCombination_injective
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0) :
    Function.Injective (simpleRootCombination f) := by
  intro x y hxy
  have hli := simpleRootSet_linearIndepOn f hf
  change LinearIndependent ℤ (fun r : simpleRootSet f => normTwoRootVal r.1) at hli
  change (Fintype.linearCombination ℤ
    (fun r : simpleRootSet f => normTwoRootVal r.1)) x =
      (Fintype.linearCombination ℤ
        (fun r : simpleRootSet f => normTwoRootVal r.1)) y at hxy
  exact hli.fintypeLinearCombination_injective hxy

/--
@isnad1 id=eq.0h6v.s9.1c2c56484bfe from=translated src=- shape=1a574a40 vocab=53691e75
-/
theorem bilinForm_fintypeLinearCombination
    {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) (v : ι → M) (x y : ι → ℤ) :
    B (Fintype.linearCombination ℤ v x) (Fintype.linearCombination ℤ v y) =
      ∑ i, ∑ j, x i * B (v i) (v j) * y j := by
  simp only [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply,
    map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.smul_apply]
  ring

/--
@isnad1 id=eq.1h5v.s12.90d7cbd44e71 from=translated src=- shape=fe34da32 vocab=2e0cb8bf
-/
theorem graphCartanBilin_simpleRootGraph
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) [DecidableEq (simpleRootSet f)]
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (x y : simpleRootSet f → ℤ) :
    Matrix.toBilin' (graphCartanMatrix (simpleRootGraph f)) x y =
      L.pairing (simpleRootCombination f x) (simpleRootCombination f y) := by
  classical
  rw [Matrix.toBilin'_apply]
  simp_rw [graphCartanMatrix_simpleRootGraph f hf]
  symm
  exact bilinForm_fintypeLinearCombination L.pairing
    (fun r : simpleRootSet f => (r.1.1 : L.carrier)) x y

/--
@isnad1 id=eq.1h4v.s10.12c96b321d92 from=translated src=- shape=b24836ca vocab=f9b781b0
-/
theorem graphCartanEnergy_simpleRootGraph
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) [DecidableEq (simpleRootSet f)]
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (x : simpleRootSet f → ℤ) :
    graphCartanEnergy (simpleRootGraph f) x =
      L.pairing (simpleRootCombination f x) (simpleRootCombination f x) := by
  exact graphCartanBilin_simpleRootGraph f hf x x

/--
@isnad1 id=ispositi.1h3v.s9.559ccaf9f0db from=translated src=- shape=ce7d4154 vocab=b1e8e645
-/
theorem simpleRootGraph_isPositiveCartan
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) [DecidableEq (simpleRootSet f)]
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0) :
    IsPositiveCartan (simpleRootGraph f) := by
  intro x hx
  rw [graphCartanEnergy_simpleRootGraph f hf]
  apply L.positiveDefinite
  intro hcomb
  have hxeq : x = 0 := simpleRootCombination_injective f hf (by simpa using hcomb)
  exact hx hxeq

def normTwoRootSpan {n : ℕ} (L : PDUnimodularLattice n) :
    Submodule ℤ L.carrier :=
  Submodule.span ℤ (Set.range (@normTwoRootVal n L))

/--
@isnad1 id=eq.1h3v.s9.ba1c7caea683 from=translated src=- shape=e06339c4 vocab=eea6b177
-/
theorem span_simpleRoots_eq_normTwoRootSpan
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0) :
    Submodule.span ℤ (Set.range fun r : simpleRootSet f => normTwoRootVal r.1) =
      normTwoRootSpan L := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨r, rfl⟩
    exact ⟨r.1, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    let S := Submodule.span ℤ
      (Set.range fun s : simpleRootSet f => normTwoRootVal s.1)
    have hgenerator : normTwoRootVal '' simpleRootSet f ⊆ S := by
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
    have hclosure : AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) ≤
        S.toAddSubmonoid :=
      AddSubmonoid.closure_le.mpr hgenerator
    rcases normTwoRoot_mem_or_neg_mem_simple_closure f hf r with hr | hr
    · exact hclosure hr
    · exact neg_mem_iff.mp (hclosure hr)

/--
@isnad1 id=eq.2h3v.s9.cb8925fe4f98 from=translated src=- shape=f61ac9c8 vocab=74d0cbfe
-/
theorem card_simpleRootSet_eq_of_fullRank
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (hrank : Set.finrank ℤ (Set.range (@normTwoRootVal n L)) = n) :
    Fintype.card (simpleRootSet f) = n := by
  have hli := simpleRootSet_linearIndepOn f hf
  change LinearIndependent ℤ
    (fun r : simpleRootSet f => normTwoRootVal r.1) at hli
  calc
    Fintype.card (simpleRootSet f) =
        Set.finrank ℤ (Set.range fun r : simpleRootSet f => normTwoRootVal r.1) :=
      (finrank_span_eq_card hli).symm
    _ = Set.finrank ℤ (Set.range (@normTwoRootVal n L)) := by
      unfold Set.finrank
      rw [span_simpleRoots_eq_normTwoRootSpan f hf]
      rfl
    _ = n := hrank

end Lattice
end SRG266
