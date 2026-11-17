import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild
import Tengoku.Seed.LinearAlgebra.Eigenspace.Charpoly
import Tengoku.Seed.LinearAlgebra.Charpoly.BaseChange
import Tengoku.Seed.Algebra.Module.Torsion.Free
import Tengoku.Seed.Data.Int.GCD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq

set_option autoImplicit false
open Polynomial

open scoped TensorProduct

/--
@isnad1 id=eq.10h10v.s11.e2f89f33f864 from=translated src=- shape=c73a933f vocab=3c0ce793
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    {B : Type} [CommRing B] [IsDomain B] (j : A →+* B) (hj : Function.Injective j)
    (a : Bˣ) (ha : (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a : Bˣ) : B)) * (X - C (((a⁻¹ : Bˣ) : B))))
    {n : ℕ} (hn : n.Coprime q) (han : a ^ n = 1) :
    a = 1 := by
  classical
  obtain ⟨k, hk⟩ := GaloisRepAdic.exists_pow_prime_pow_eq_one_of_wild ρ hp hpA hq hqp P hP hwild
  letI : Algebra A B := j.toAlgebra

  have hchar : ((ρ.ρ σ).baseChange B).charpoly = (X - C ((a : Bˣ) : B)) * (X - C (((a⁻¹ : Bˣ) : B))) := by
    rw [LinearMap.charpoly_baseChange]
    exact ha
  have hroot : ((ρ.ρ σ).baseChange B).charpoly.IsRoot ((a : Bˣ) : B) := by
    rw [hchar, IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hev : Module.End.HasEigenvalue ((ρ.ρ σ).baseChange B) ((a : Bˣ) : B) :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly ((ρ.ρ σ).baseChange B) _).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hfpow : ((ρ.ρ σ).baseChange B) ^ q ^ k = 1 := by
    rw [← LinearMap.baseChange_pow, hk, LinearMap.baseChange_one]
  have h1 : (((a : Bˣ) : B) ^ q ^ k) • v = v := by
    rw [← hv.pow_apply, hfpow, Module.End.one_apply]
  have hak : ((a : Bˣ) : B) ^ q ^ k = 1 := by
    have h2 := sub_smul (((a : Bˣ) : B) ^ q ^ k) (1 : B) v
    rw [h1, one_smul, sub_self] at h2
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  have haku : a ^ q ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hak, Units.val_one])
  have hg : n.gcd (q ^ k) = 1 := Nat.Coprime.pow_right k hn
  have h := (pow_gcd_eq_one (a := a) (m := n) (n := q ^ k)).mpr ⟨han, haku⟩
  rwa [hg, pow_one] at h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
