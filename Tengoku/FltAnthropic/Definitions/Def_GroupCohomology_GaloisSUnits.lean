import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

/--
@isnad1 id=iff.0h3v.s8.075919b9b8a0 from=translated src=- shape=fe6ffd64 vocab=d5c53788
-/
lemma liesOverPrime_comap_algEquiv_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (q : ℕ) :
    (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime q ↔ A.LiesOverPrime q := by
  simp only [LiesOverPrime, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_natCast]

end ValuationSubring

namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

def galoisSUnits : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
    ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A}
  one_mem' A _ := by simp
  mul_mem' {x y} hx hy A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    obtain ⟨hy₁, hy₂⟩ := hy A hA
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact A.mul_mem _ _ hx₁ hy₁
    · rw [mul_inv_rev, Units.val_mul]; exact A.mul_mem _ _ hy₂ hx₂
  inv_mem' {x} hx A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    exact ⟨hx₂, by rwa [inv_inv]⟩

variable {S} in
/--
@isnad1 id=iff.0h2v.s8.756061752e26 from=translated src=- shape=c6f5aad3 vocab=899a3e51
-/
lemma mem_galoisSUnits_iff (x : (AlgebraicClosure ℚ)ˣ) :
    x ∈ galoisSUnits S ↔ ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
      ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A :=
  Iff.rfl

variable {S} in

/--
@isnad1 id=mem.1h3v.s10.818deeb4ea88 from=translated src=- shape=4f691d91 vocab=a28c4755
-/
lemma smul_mem_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : (AlgebraicClosure ℚ)ˣ}
    (hx : x ∈ galoisSUnits S) : σ • x ∈ galoisSUnits S := by
  intro A hA
  have hA' : ∀ q ∈ S, ¬ (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime ((q : Nat.Primes) : ℕ) :=
    fun q hq h => hA q hq ((A.liesOverPrime_comap_algEquiv_iff σ q).1 h)
  obtain ⟨h₁, h₂⟩ := hx _ hA'
  rw [ValuationSubring.mem_comap] at h₁ h₂
  refine ⟨h₁, ?_⟩
  rw [← smul_inv']
  exact h₂

instance instMulDistribMulActionGaloisSUnits :
    MulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S) where
  smul σ x := ⟨σ • (x : (AlgebraicClosure ℚ)ˣ), smul_mem_galoisSUnits σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : (AlgebraicClosure ℚ)ˣ))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : (AlgebraicClosure ℚ)ˣ))
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : (AlgebraicClosure ℚ)ˣ) (y : (AlgebraicClosure ℚ)ˣ))
  smul_one σ := Subtype.ext (smul_one σ)

/--
@isnad1 id=eq.0h3v.s12.7621cfbe9bd7 from=translated src=- shape=ccd8f593 vocab=cf8d81c4
-/
@[simp] lemma coe_smul_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(galoisSUnits S)) :
    ((σ • x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) = σ • (x : (AlgebraicClosure ℚ)ˣ) := rfl

/--
@isnad1 id=eq.0h3v.s11.c31fb4338d5d from=translated src=- shape=b120c55c vocab=cddff337
-/
lemma coe_coe_smul_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(galoisSUnits S)) :
    (((σ • x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = σ ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) :=
  rfl

abbrev galoisSUnitsRep : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Rep.ofMulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S)

def galoisSUnitsToUnits : galoisSUnitsRep S →ₗ[ℤ] Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ) :=
  (MonoidHom.toAdditive (galoisSUnits S).subtype).toIntLinearMap

/--
@isnad1 id=eq.0h2v.s13.9eddd81592c9 from=translated src=- shape=487d9cfe vocab=e8df5710
-/
@[simp] lemma galoisSUnitsToUnits_apply (x : galoisSUnitsRep S) :
    galoisSUnitsToUnits S x = Additive.ofMul ((Additive.toMul x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) := rfl

/--
@isnad1 id=injectiv.0h1v.s12.fc037f38c68c from=translated src=- shape=8f0e055a vocab=a73f5ad9
-/
lemma galoisSUnitsToUnits_injective : Function.Injective (galoisSUnitsToUnits S) :=
  fun _ _ h => Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

end groupCohomology

end
