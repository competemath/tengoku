import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff

set_option autoImplicit false

open AlgebraicCurve

namespace CuspTransportAux

variable {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]

def L (B : Subalgebra A T) (y : Ideal ↥B) : Set T := {f | ∃ g h : ↥B, h ∉ y ∧ f * (h : T) = (g : T)}

def M (B : Subalgebra A T) (y : Ideal ↥B) : Set T := {f | ∃ g h : ↥B, h ∉ y ∧ g ∈ y ∧ f * (h : T) = (g : T)}

section Basic

variable (B : Subalgebra A T) (y : Ideal ↥B) [hy : y.IsPrime]

theorem one_notMem : (1 : ↥B) ∉ y := (Ideal.ne_top_iff_one y).mp hy.ne_top

theorem zero_mem_M : (0 : T) ∈ M B y := ⟨0, 1, one_notMem B y, y.zero_mem, by simp⟩

theorem coe_mem_M_iff (b : ↥B) : (b : T) ∈ M B y ↔ b ∈ y := by
  constructor
  · rintro ⟨g, h, hh, hg, e⟩
    have : b * h = g := Subtype.ext (by simpa using e)
    have hbh : b * h ∈ y := this ▸ hg
    exact (hy.mem_or_mem hbh).resolve_right hh
  · intro hb; exact ⟨b, 1, one_notMem B y, hb, by simp⟩

theorem mul_mem_M {f₁ f₂ : T} (h₁ : f₁ ∈ L B y) (h₂ : f₂ ∈ M B y) : f₁ * f₂ ∈ M B y := by
  obtain ⟨g₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨g₂, k₂, hk₂, hg₂, e₂⟩ := h₂
  refine ⟨g₁ * g₂, k₁ * k₂, fun hk => (hy.mem_or_mem hk).elim hk₁ hk₂, y.mul_mem_left _ hg₂, ?_⟩
  simp only [Subalgebra.coe_mul]
  calc f₁ * f₂ * ((k₁ : T) * k₂) = (f₁ * k₁) * (f₂ * k₂) := by ring
    _ = g₁ * g₂ := by rw [e₁, e₂]

theorem add_mem_M {f₁ f₂ : T} (h₁ : f₁ ∈ M B y) (h₂ : f₂ ∈ M B y) : f₁ + f₂ ∈ M B y := by
  obtain ⟨g₁, k₁, hk₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, k₂, hk₂, hg₂, e₂⟩ := h₂
  refine ⟨g₁ * k₂ + g₂ * k₁, k₁ * k₂, fun hk => (hy.mem_or_mem hk).elim hk₁ hk₂,
    y.add_mem (y.mul_mem_right _ hg₁) (y.mul_mem_right _ hg₂), ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
  calc (f₁ + f₂) * ((k₁ : T) * k₂) = (f₁ * k₁) * k₂ + (f₂ * k₂) * k₁ := by ring
    _ = g₁ * k₂ + g₂ * k₁ := by rw [e₁, e₂]

theorem inv_mem_L_of_notMem_M {f : T} (hf : f ∈ L B y) (hfM : f ∉ M B y) : f⁻¹ ∈ L B y := by
  obtain ⟨g, k, hk, e⟩ := hf
  have hg : g ∉ y := fun hg => hfM ⟨g, k, hk, hg, e⟩
  refine ⟨k, g, hg, ?_⟩
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hg
    rw [show g = 0 from Subtype.ext (by simpa using e.symm)]; exact y.zero_mem
  rw [← e]; field_simp

theorem one_notMem_M : (1 : T) ∉ M B y := by
  intro h
  have := (coe_mem_M_iff B y 1).mp (by simpa using h)
  exact one_notMem B y this

end Basic

section Order

variable (B : Subalgebra A T)

end Order

end CuspTransportAux

namespace CuspTransportAux

variable {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]

section Contract

variable (B B' : Subalgebra A T) (y : Ideal ↥B) [hy : y.IsPrime] (hB' : ∀ b' : ↥B', (b' : T) ∈ L B y)

def contract : Ideal ↥B' where
  carrier := {b' | (b' : T) ∈ M B y}
  zero_mem' := by simpa using zero_mem_M B y
  add_mem' := fun {a b} ha hb => by simpa using add_mem_M B y ha hb
  smul_mem' := fun c {x} hx => by
    simp only [smul_eq_mul, Set.mem_ofPred_eq, Subalgebra.coe_mul] at hx ⊢
    exact mul_mem_M B y (hB' c) hx

theorem mem_contract_iff (b' : ↥B') : b' ∈ contract B B' y hB' ↔ (b' : T) ∈ M B y := Iff.rfl

scoped instance contract_isPrime : (contract B B' y hB').IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_contract_iff]
    simpa using one_notMem_M B y
  · intro a b hab
    rw [mem_contract_iff, Subalgebra.coe_mul] at hab
    by_cases ha : (a : T) ∈ M B y
    · exact Or.inl ha
    · right
      have hainv := inv_mem_L_of_notMem_M B y (hB' a) ha
      have ha0 : (a : T) ≠ 0 := fun h0 => ha (by rw [h0]; exact zero_mem_M B y)
      have : (b : T) = (a : T)⁻¹ * ((a : T) * b) := by field_simp
      show (b : T) ∈ M B y
      rw [this]; exact mul_mem_M B y hainv hab

end Contract

section MfromL

variable (B₁ B₂ : Subalgebra A T) (y₁ : Ideal ↥B₁) (y₂ : Ideal ↥B₂) [y₁.IsPrime] [y₂.IsPrime]

end MfromL

section Transport

variable (B : Subalgebra A T) (σ : T ≃ₐ[A] T) (hσ' : ∀ b : ↥B, σ.symm b ∈ B)

def resInv : ↥B →+* ↥B where
  toFun b := ⟨σ.symm b, hσ' b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

def transport (𝔶 : Ideal ↥B) : Ideal ↥B := 𝔶.comap (resInv B σ hσ')

theorem mem_transport_iff (𝔶 : Ideal ↥B) (b : ↥B) :
    b ∈ transport B σ hσ' 𝔶 ↔ (⟨σ.symm b, hσ' b⟩ : ↥B) ∈ 𝔶 := Iff.rfl

scoped instance transport_isPrime (𝔶 : Ideal ↥B) [𝔶.IsPrime] : (transport B σ hσ' 𝔶).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_L_transport_iff (hσ : ∀ b : ↥B, σ b ∈ B) (𝔶 : Ideal ↥B) (f : T) :
    f ∈ L B (transport B σ hσ' 𝔶) ↔ σ.symm f ∈ L B 𝔶 := by
  constructor
  · rintro ⟨g, k, hk, e⟩
    refine ⟨⟨σ.symm g, hσ' g⟩, ⟨σ.symm k, hσ' k⟩, hk, ?_⟩
    show σ.symm f * σ.symm (k : T) = σ.symm (g : T)
    rw [← map_mul, e]
  · rintro ⟨g, k, hk, e⟩
    refine ⟨⟨σ g, hσ g⟩, ⟨σ k, hσ k⟩, ?_, ?_⟩
    · rw [mem_transport_iff]
      have : (⟨σ.symm (σ (k : T)), hσ' ⟨σ k, hσ k⟩⟩ : ↥B) = k := Subtype.ext (by simp)
      rw [this]; exact hk
    · show f * σ (k : T) = σ (g : T)
      rw [← e, map_mul, AlgEquiv.apply_symm_apply]

theorem mem_M_transport_iff (hσ : ∀ b : ↥B, σ b ∈ B) (𝔶 : Ideal ↥B) (f : T) :
    f ∈ M B (transport B σ hσ' 𝔶) ↔ σ.symm f ∈ M B 𝔶 := by
  constructor
  · rintro ⟨g, k, hk, hg, e⟩
    refine ⟨⟨σ.symm g, hσ' g⟩, ⟨σ.symm k, hσ' k⟩, hk, hg, ?_⟩
    show σ.symm f * σ.symm (k : T) = σ.symm (g : T)
    rw [← map_mul, e]
  · rintro ⟨g, k, hk, hg, e⟩
    refine ⟨⟨σ g, hσ g⟩, ⟨σ k, hσ k⟩, ?_, ?_, ?_⟩
    · rw [mem_transport_iff]
      have : (⟨σ.symm (σ (k : T)), hσ' ⟨σ k, hσ k⟩⟩ : ↥B) = k := Subtype.ext (by simp)
      rw [this]; exact hk
    · rw [mem_transport_iff]
      have : (⟨σ.symm (σ (g : T)), hσ' ⟨σ g, hσ g⟩⟩ : ↥B) = g := Subtype.ext (by simp)
      rw [this]; exact hg
    · show f * σ (k : T) = σ (g : T)
      rw [← e, map_mul, AlgEquiv.apply_symm_apply]

end Transport

end CuspTransportAux
open scoped _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff.CuspTransportAux

open CuspTransportAux AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 6400000 in
theorem solution
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T] (j : T)
    (σ : T ≃ₐ[A] T)
    (hσ : ∀ b : T, b ∈ TwoChartIntegralModel.chartAlgFin A T j ↔ σ b ∈ TwoChartIntegralModel.chartAlgFin A T j) :
    ∃ Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} →
            {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
      Function.Bijective Φ ∧
      (∀ y₁ y₂ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
        y₁.1 ≤ y₂.1 ↔ (Φ y₁).1 ≤ (Φ y₂).1) ∧
      (∀ (y : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime})
        (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)),
        b ∈ (Φ y).1 ↔ (⟨σ.symm b, (hσ (σ.symm b)).2 (by rw [AlgEquiv.apply_symm_apply]; exact b.2)⟩ :
          ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ σ.symm f * (h : T) = (g : T))) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ g ∈ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ g ∈ y.1 ∧ σ.symm f * (h : T) = (g : T))) := by
  classical
  have hσB : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A T j), σ (b : T) ∈ (TwoChartIntegralModel.chartAlgFin A T j) := fun b => (hσ b).mp b.2
  have hσB' : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A T j), σ.symm (b : T) ∈ (TwoChartIntegralModel.chartAlgFin A T j) := fun b =>
    (hσ (σ.symm b)).mpr (by rw [AlgEquiv.apply_symm_apply]; exact b.2)
  have hσsB' : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A T j), σ.symm.symm (b : T) ∈ (TwoChartIntegralModel.chartAlgFin A T j) := fun b => by simpa using hσB b
  let Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} → {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} := fun y =>
    ⟨transport (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' y.1, by haveI := y.2; exact transport_isPrime (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' y.1⟩
  let Ψ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} → {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} := fun y =>
    ⟨transport (TwoChartIntegralModel.chartAlgFin A T j) σ.symm hσsB' y.1, by haveI := y.2; exact transport_isPrime (TwoChartIntegralModel.chartAlgFin A T j) σ.symm hσsB' y.1⟩
  have hΦ : ∀ y (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)), b ∈ (Φ y).1 ↔ (⟨σ.symm b, hσB' b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1 := fun y b => Iff.rfl
  have hΨ : ∀ y (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)), b ∈ (Ψ y).1 ↔ (⟨σ b, by simpa using hσsB' b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1 := by
    intro y b
    show (⟨σ.symm.symm b, hσsB' b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1 ↔ _
    simp only [AlgEquiv.symm_symm]
  have hΨΦ : ∀ y, Ψ (Φ y) = y := by
    intro y; apply Subtype.ext; ext b
    rw [hΨ, hΦ]
    simp
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y; apply Subtype.ext; ext b
    rw [hΦ, hΨ]
    simp
  refine ⟨Φ, Function.bijective_iff_has_inverse.mpr ⟨Ψ, hΨΦ, hΦΨ⟩, ?_, ?_, ?_, ?_⟩
  · intro y₁ y₂
    constructor
    · intro h b hb
      rw [hΦ] at hb ⊢
      exact h hb
    · intro h b hb
      have e : (⟨σ.symm ((⟨σ b, hσB b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) : T), hσB' ⟨σ b, hσB b⟩⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) = b := Subtype.ext (by simp)
      have hmem : (⟨σ b, hσB b⟩ : ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ (Φ y₁).1 := by rw [hΦ, e]; exact hb
      have h2 := h hmem
      rw [hΦ, e] at h2
      exact h2
  · intro y b
    exact hΦ y b
  · intro y f
    exact mem_L_transport_iff (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' hσB y.1 f
  · intro y f
    exact mem_M_transport_iff (TwoChartIntegralModel.chartAlgFin A T j) σ hσB' hσB y.1 f
