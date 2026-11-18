import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_AtPPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates

open ModularCurve

theorem solution
    {S : Finset Nat.Primes} {Φ : Type*} [AddCommGroup Φ] [Module HeckeAlg Φ]
    (hΦ : EisensteinAnnihilates S Φ)
    {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal) {ℓ : Nat.Primes} (hℓ : ℓ ∉ S)
    (hne : heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪) :
    heckeTorsion Φ 𝔪 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hne
  calc x = (1 : HeckeAlg) • x := (one_smul _ x).symm
    _ = (y * (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) + i) • x := by rw [hyi]
    _ = y • ((heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x) + i • x := by
        rw [add_smul, mul_smul]
    _ = 0 := by
        rw [hΦ ℓ hℓ x, smul_zero, zero_add,
          (mem_heckeTorsion_iff Φ 𝔪 x).mp hx i hi]
