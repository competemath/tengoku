import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits

set_option autoImplicit false

open scoped Pointwise

/--
@isnad1 id=iff.5h7v.s10.ee8623286291 from=translated src=- shape=a7fc272f vocab=85efe57c
-/
theorem solution
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) :
    g ∈ 𝔶.inertia G ↔ (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) := by

  have hnu : ∀ (h : G) (x : F), x ∈ (h • P).nonunits ↔ h⁻¹ • x ∈ P.nonunits := by
    intro h x
    simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      smul_inv'', smul_eq_zero_iff_eq]

  have hmem : ∀ {h : G}, h ∈ 𝔶.inertia G → ∀ b : B, h • b ∈ 𝔶 ↔ b ∈ 𝔶 := by
    intro h hh b
    have hb := hh b
    constructor
    · intro h1; simpa using 𝔶.sub_mem h1 hb
    · intro h1; simpa using 𝔶.add_mem hb h1
  constructor
  · intro hg

    have hstab : g • P = P := by
      apply huniq
      · intro b
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hρ]
        exact hP _
      · intro b
        rw [hnu, hρ, hPy]
        exact hmem (inv_mem hg) b
    refine ⟨hstab, fun e => ?_⟩

    obtain ⟨b, hb⟩ := hres e
    have h1 : g • ((e : F) - ρ b) ∈ P.nonunits := by
      have : g • ((e : F) - ρ b) ∈ (g • P).nonunits := by
        rw [hnu, inv_smul_smul]; exact hb
      rwa [hstab] at this
    have h2 : g • ρ b - ρ b ∈ P.nonunits := by
      rw [hρ, ← map_sub]; exact (hPy _).mpr (hg b)
    have h3 : ρ b - (e : F) ∈ P.nonunits := by
      have := P.nonunits.neg_mem hb
      rwa [neg_sub] at this
    have : g • (e : F) - e = g • ((e : F) - ρ b) + (g • ρ b - ρ b) + (ρ b - e) := by
      rw [smul_sub]; ring
    rw [this]
    exact P.nonunits.add_mem (P.nonunits.add_mem h1 h2) h3
  · rintro ⟨-, hres'⟩ b
    have h := hres' ⟨ρ b, hP b⟩
    change g • ρ b - ρ b ∈ P.nonunits at h
    rw [hρ, ← map_sub] at h
    exact (hPy _).mp h
