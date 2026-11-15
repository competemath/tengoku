import Tengoku.FltAnthropic.Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Tengoku.FltAnthropic.Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

def fixedSubmodule {G : Type*} [Group G] (U : Subgroup G) (V : Type*) [AddCommGroup V]
    [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, g • v = v}
  add_mem' := by
    intro v w hv hw g hg
    rw [smul_add, hv g hg, hw g hg]
  zero_mem' := by
    intro g _
    exact smul_zero g
  smul_mem' := by
    intro c v hv g hg
    rw [smul_comm, hv g hg]

/--
@isnad1 id=iff.0h4v.s7.a0952027b574 from=translated src=- shape=66c666e3 vocab=f494ab92
-/
theorem mem_fixedSubmodule_iff {G : Type*} [Group G] {U : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] {v : V} :
    v ∈ fixedSubmodule U V ↔ ∀ g ∈ U, g • v = v :=
  Iff.rfl

section IntegralSubgroupSeam

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/--
@isnad1 id=eq.0h3v.s7.c5e131536a22 from=translated src=- shape=2eecf090 vocab=a80bc826
-/
theorem congruenceK0_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK0 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK0_zero ϖ

/--
@isnad1 id=eq.0h3v.s7.a8144934cac4 from=translated src=- shape=2eecf090 vocab=6233b4e4
-/
theorem congruenceK1_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK1 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK1_zero ϖ

/--
@isnad1 id=le.0h4v.s8.e02da371344e from=translated src=- shape=c1593c85 vocab=87954376
-/
theorem congruenceK0_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK0 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K := by
  rintro x ⟨y, rfl, _⟩
  exact ⟨y, rfl⟩

/--
@isnad1 id=le.0h4v.s8.4df4319d6eec from=translated src=- shape=c1593c85 vocab=3af6c708
-/
theorem congruenceK1_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK1 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K :=
  (congruenceK1_le_congruenceK0 _ _).trans (congruenceK0_le_integralSubgroup ϖ n)

end IntegralSubgroupSeam

section Padic

variable (p : ℕ) [Fact p.Prime]

/--
@isnad1 id=eq.0h1v.s7.b7ec7ac7ff4b from=translated src=- shape=c3392215 vocab=26654a24
-/
theorem padicK0_zero_eq_integralSubgroup :
    padicK0 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK0_zero_eq_integralSubgroup (p : ℤ_[p])

/--
@isnad1 id=eq.0h1v.s7.97f02daff9f6 from=translated src=- shape=c3392215 vocab=e71cef2b
-/
theorem padicK1_zero_eq_integralSubgroup :
    padicK1 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK1_zero_eq_integralSubgroup (p : ℤ_[p])

def centralGL : ℚ_[p]ˣ →* GL (Fin 2) ℚ_[p] :=
  Units.map (algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p])).toMonoidHom

def IsCentralCharacterRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (ω : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ (u : ℚ_[p]ˣ) (v : V), centralGL p u • v = (ω u : ℂ) • v

/--
@isnad1 id=eq.3h4v.s8.7084010e7d16 from=translated src=- shape=8db7c23b vocab=9667e3c7
-/
theorem centralCharacterRep_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (hV : ∃ v : V, v ≠ 0)
    {ω ω' : ℚ_[p]ˣ →* ℂˣ} (hω : IsCentralCharacterRep p V ω)
    (hω' : IsCentralCharacterRep p V ω') : ω = ω' := by
  obtain ⟨v, hv0⟩ := hV
  have key : ∀ u : ℚ_[p]ˣ, (ω u : ℂ) = (ω' u : ℂ) := by
    intro u
    by_contra hne
    have hcne : (ω u : ℂ) - (ω' u : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h3 : ((ω u : ℂ) - (ω' u : ℂ)) • v = 0 := by
      rw [sub_smul, ← hω u v, ← hω' u v, sub_self]
    exact hv0 (by
      calc v = ((ω u : ℂ) - (ω' u : ℂ))⁻¹ • (((ω u : ℂ) - (ω' u : ℂ)) • v) := by
            rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
        _ = 0 := by rw [h3, smul_zero])
  exact MonoidHom.ext fun u => Units.ext (key u)

def HasNewvectorConductor (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    (c : ℕ) : Prop :=
  fixedSubmodule (padicK1 p c) V ≠ ⊥ ∧ ∀ m < c, fixedSubmodule (padicK1 p m) V = ⊥

/--
@isnad1 id=eq.2h4v.s8.035f325c3eae from=translated src=- shape=e2006b0d vocab=ea6f7482
-/
theorem hasNewvectorConductor_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    {c c' : ℕ} (h : HasNewvectorConductor p V c) (h' : HasNewvectorConductor p V c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd (h'.2 c hlt) h.1
  · exact heq
  · exact absurd (h.2 c' hgt) h'.1

def IsIrreducibleGLRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] : Prop :=
  (∃ v : V, v ≠ 0) ∧
  ∀ W : Submodule ℂ V,
    (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤

def HasFiniteLevelFixed (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V] : Prop :=
  ∀ n : ℕ, Module.Finite ℂ (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup p n) V)

end Padic

end LocalNewvector
