import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Residual
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom

set_option autoImplicit false

namespace EisensteinGaloisRep

open scoped MatrixGroups

local notation "Gℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Cyclo

variable (n : ℕ) [NeZero n]

/--
@isnad1 id=ex.0h1v.s4.712ff696c087 from=translated src=- shape=fa363b41 vocab=ac71112a
-/
theorem exists_isPrimitiveRoot : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.prim

noncomputable def zeta : AlgebraicClosure ℚ := (exists_isPrimitiveRoot n).choose

/--
@isnad1 id=isprimit.0h1v.s4.2a7a594e3b8c from=translated src=- shape=a1a5f7d2 vocab=1970797c
-/
theorem zeta_spec : IsPrimitiveRoot (zeta n) n := (exists_isPrimitiveRoot n).choose_spec

noncomputable def cyclo : Gℚ →* (ZMod n)ˣ := (zeta_spec n).autToPow ℚ

/--
@isnad1 id=eq.0h2v.s10.713b252dffed from=translated src=- shape=bd545539 vocab=56f52829
-/
theorem cyclo_spec (σ : Gℚ) : σ (zeta n) = zeta n ^ ((cyclo n σ : (ZMod n)ˣ) : ZMod n).val :=
  ((zeta_spec n).autToPow_spec ℚ σ).symm

/--
@isnad1 id=eq.1h3v.s6.d5c4b6bb3917 from=translated src=- shape=8feb4181 vocab=888d7aeb
-/
theorem zmod_eq_of_pow_eq {c d : ZMod n} (h : zeta n ^ c.val = zeta n ^ d.val) : c = d :=
  ZMod.val_injective n ((zeta_spec n).pow_inj (ZMod.val_lt c) (ZMod.val_lt d) h)

/--
@isnad1 id=eq.0h2v.s6.35fab79c072e from=translated src=- shape=dc0cd100 vocab=c3e88637
-/
theorem pow_val_natCast (m : ℕ) : zeta n ^ ((m : ZMod n)).val = zeta n ^ m := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [pow_add, pow_mul, (zeta_spec n).pow_eq_one, one_pow, mul_one]

/--
@isnad1 id=eq.1h3v.s10.f8cba381c279 from=translated src=- shape=86514f56 vocab=92f7c2f8
-/
theorem coe_cyclo_eq_natCast_of_apply_eq_pow {σ : Gℚ} {m : ℕ} (h : σ (zeta n) = zeta n ^ m) :
    ((cyclo n σ : (ZMod n)ˣ) : ZMod n) = (m : ZMod n) := by
  apply zmod_eq_of_pow_eq n
  rw [← cyclo_spec, h, pow_val_natCast]

/--
@isnad1 id=eq.1h2v.s10.17696e7b75fd from=translated src=- shape=59ad8517 vocab=eb6d9ce0
-/
theorem cyclo_eq_one_of_apply_eq_self {σ : Gℚ} (h : σ (zeta n) = zeta n) : cyclo n σ = 1 := by
  apply Units.ext
  rw [Units.val_one]
  have h1 : σ (zeta n) = zeta n ^ (1 : ℕ) := by rw [pow_one]; exact h
  have := coe_cyclo_eq_natCast_of_apply_eq_pow n h1
  rw [this, Nat.cast_one]

/--
@isnad1 id=eq.4h4v.s10.1e6f6f632d76 from=translated src=- shape=754aab21 vocab=fb088119
-/
theorem coe_cyclo_of_isFrobeniusAt {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ¬ ℓ ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : A.IsFrobeniusAt σ ℓ) :
    ((cyclo n σ : (ZMod n)ˣ) : ZMod n) = (ℓ : ZMod n) :=
  coe_cyclo_eq_natCast_of_apply_eq_pow n
    (ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one A hℓ hA hσ hℓn
      (zeta_spec n).pow_eq_one)

/--
@isnad1 id=eq.4h4v.s10.285a83bfee53 from=translated src=- shape=be76f977 vocab=ecd6dbb2
-/
theorem cyclo_of_isFrobeniusAt {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ¬ ℓ ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : A.IsFrobeniusAt σ ℓ) :
    cyclo n σ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓn) := by
  apply Units.ext
  rw [coe_cyclo_of_isFrobeniusAt n hℓ hℓn A hA hσ, ZMod.coe_unitOfCoprime]

/--
@isnad1 id=eq.4h4v.s10.803159314daa from=translated src=- shape=4d5627ab vocab=1c6025aa
-/
theorem cyclo_eq_one_of_mem_inertiaSubgroupIn {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ¬ ℓ ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : cyclo n σ = 1 :=
  cyclo_eq_one_of_apply_eq_self n
    (ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one A hℓ hA hσ hℓn
      (zeta_spec n).pow_eq_one)

noncomputable def level : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {zeta n}

/--
@isnad1 id=finitedi.0h1v.s8.3e5e87b0b634 from=translated src=- shape=72d9161d vocab=0ed62c9d
-/
scoped instance finiteDimensional_level : FiniteDimensional ℚ (level n) :=
  IntermediateField.adjoin.finiteDimensional
    (((zeta_spec n).isIntegral (Nat.pos_of_ne_zero (NeZero.ne n))).tower_top)

/--
@isnad1 id=eq.1h2v.s10.043fd15465bc from=translated src=- shape=afff9a1c vocab=adf6f50b
-/
theorem cyclo_eq_one_of_fix {σ : Gℚ} (hσ : ∀ x ∈ level n, σ x = x) : cyclo n σ = 1 :=
  cyclo_eq_one_of_apply_eq_self n (hσ _ (IntermediateField.mem_adjoin_simple_self ℚ (zeta n)))

end Cyclo

section Push

variable (n : ℕ) [NeZero n] {κ : Type} [Field κ]

noncomputable def push (ψ : (ZMod n)ˣ →* κˣ) : Gℚ →* κˣ := ψ.comp (cyclo n)

/--
@isnad1 id=eq.0h4v.s11.3703d9347bca from=translated src=- shape=e46914ef vocab=ba356e6e
-/
theorem push_apply (ψ : (ZMod n)ˣ →* κˣ) (σ : Gℚ) : push n ψ σ = ψ (cyclo n σ) := rfl

/--
@isnad1 id=eq.4h6v.s10.8dbd0f10b7d6 from=translated src=- shape=e7f24b39 vocab=dbd71c1b
-/
theorem push_of_isFrobeniusAt (ψ : (ZMod n)ˣ →* κˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ¬ ℓ ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : A.IsFrobeniusAt σ ℓ) :
    push n ψ σ = ψ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓn)) := by
  rw [push_apply, cyclo_of_isFrobeniusAt n hℓ hℓn A hA hσ]

/--
@isnad1 id=eq.4h6v.s10.dffe52793892 from=translated src=- shape=509c284c vocab=5d869ce8
-/
theorem push_eq_one_of_mem_inertiaSubgroupIn (ψ : (ZMod n)ˣ →* κˣ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓn : ¬ ℓ ∣ n) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : push n ψ σ = 1 := by
  rw [push_apply, cyclo_eq_one_of_mem_inertiaSubgroupIn n hℓ hℓn A hA hσ, map_one]

/--
@isnad1 id=eq.1h4v.s10.6f6d848f72f7 from=translated src=- shape=3b940c24 vocab=80dd853e
-/
theorem push_eq_one_of_fix (ψ : (ZMod n)ˣ →* κˣ) {σ : Gℚ} (hσ : ∀ x ∈ level n, σ x = x) :
    push n ψ σ = 1 := by
  rw [push_apply, cyclo_eq_one_of_fix n hσ, map_one]

end Push

section CycloP

variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]

noncomputable def cycloK : Gℚ →* κˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  push p (Units.map ((ZMod.castHom (dvd_refl p) κ).toMonoidHom))

/--
@isnad1 id=eq.4h5v.s10.449fcd325b4d from=translated src=- shape=fbbf0fe5 vocab=a5a4d07c
-/
theorem coe_cycloK_of_isFrobeniusAt {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : A.IsFrobeniusAt σ ℓ) : ((cycloK p κ σ : κˣ) : κ) = (ℓ : κ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hℓp' : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
  change (((push p (Units.map ((ZMod.castHom (dvd_refl p) κ).toMonoidHom)) σ) : κˣ) : κ) = _
  rw [push_of_isFrobeniusAt p _ hℓ hℓp' A hA hσ, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, map_natCast]

/--
@isnad1 id=eq.4h5v.s10.cf6ab0c9add4 from=translated src=- shape=b49c440a vocab=3d55b3a9
-/
theorem cycloK_eq_one_of_mem_inertiaSubgroupIn {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {σ : Gℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : cycloK p κ σ = 1 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hℓp' : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
  exact push_eq_one_of_mem_inertiaSubgroupIn p _ hℓ hℓp' A hA hσ

/--
@isnad1 id=eq.1h3v.s10.32a32addbdfa from=translated src=- shape=e81f6006 vocab=1fab917e
-/
theorem cycloK_eq_one_of_fix {σ : Gℚ}
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ∀ x ∈ level p, σ x = x) :
    cycloK p κ σ = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact push_eq_one_of_fix p _ hσ

end CycloP

section Diag

variable {G : Type*} [Group G] {κ : Type} [Field κ]

noncomputable def pairUnits (a b : G →* κˣ) : G →* (Fin 2 → κ)ˣ :=
  (MulEquiv.piUnits (M := fun _ : Fin 2 => κ)).symm.toMonoidHom.comp
    (MonoidHom.pi (fun i : Fin 2 => Fin.cases a (fun _ => b) i))

noncomputable def diag (a b : G →* κˣ) : G →* GL (Fin 2) κ :=
  (Units.map (Matrix.diagonalRingHom (Fin 2) κ).toMonoidHom).comp (pairUnits a b)

def entries (a b : G →* κˣ) (σ : G) : Fin 2 → κ := fun i => Fin.cases ((a σ : κˣ) : κ) (fun _ => ((b σ : κˣ) : κ)) i

/--
@isnad1 id=eq.0h5v.s8.e4638caf6607 from=translated src=- shape=90e68efd vocab=988954f7
-/
theorem val_pairUnits (a b : G →* κˣ) (σ : G) :
    ((pairUnits a b σ : (Fin 2 → κ)ˣ) : Fin 2 → κ) = entries a b σ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/--
@isnad1 id=eq.0h5v.s8.6280f141bda9 from=translated src=- shape=850c6b0f vocab=6ad066bf
-/
theorem val_diag (a b : G →* κˣ) (σ : G) :
    ((diag a b σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) = Matrix.diagonal (entries a b σ) := by
  change (Matrix.diagonalRingHom (Fin 2) κ) ((pairUnits a b σ : (Fin 2 → κ)ˣ) : Fin 2 → κ) = _
  rw [val_pairUnits]
  rfl

/--
@isnad1 id=eq.0h5v.s9.d289dbc63b42 from=translated src=- shape=75baf78e vocab=90f5737b
-/
theorem trace_diag (a b : G →* κˣ) (σ : G) :
    Matrix.trace (diag a b σ).val = ((a σ : κˣ) : κ) + ((b σ : κˣ) : κ) := by
  rw [val_diag, Matrix.trace_diagonal, Fin.sum_univ_two]
  rfl

/--
@isnad1 id=eq.0h5v.s9.fa2d081bce2c from=translated src=- shape=75baf78e vocab=1710a82a
-/
theorem det_diag (a b : G →* κˣ) (σ : G) :
    Matrix.det (diag a b σ).val = ((a σ : κˣ) : κ) * ((b σ : κˣ) : κ) := by
  rw [val_diag, Matrix.det_diagonal, Fin.prod_univ_two]
  rfl

/--
@isnad1 id=eq.2h5v.s9.0a641b4afc2c from=translated src=- shape=535f2e29 vocab=ba74f2e2
-/
theorem diag_eq_one {a b : G →* κˣ} {σ : G} (ha : a σ = 1) (hb : b σ = 1) : diag a b σ = 1 := by
  apply Units.ext
  rw [val_diag, Units.val_one]
  have : entries a b σ = 1 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((a σ : κˣ) : κ) = 1; rw [ha, Units.val_one]
    · change ((b σ : κˣ) : κ) = 1; rw [hb, Units.val_one]
  rw [this]
  exact Matrix.diagonal_one

end Diag

end EisensteinGaloisRep
open scoped _root_.P2MW.S_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom.EisensteinGaloisRep

open EisensteinGaloisRep in
/--
@isnad1 id=ex.0h5v.s12.3e810e916058 from=translated src=- shape=6115b46f vocab=6e1cbf88
-/
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (κ : Type) [Field κ] [CharP κ p]
    (ψ₁ ψ₂ : (ZMod N)ˣ →* κˣ) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
                (ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) +
                  (ℓ : κ) * (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) ∧
            Matrix.det (ρ σ).val =
                (ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) *
                  (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) * (ℓ : κ)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  set a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* κˣ := push N ψ₁ with ha
  set b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* κˣ := (cycloK p κ) * push N ψ₂ with hb
  refine ⟨diag a b, ?_, ?_, ?_⟩
  ·
    refine ⟨level N ⊔ level p, IntermediateField.finiteDimensional_sup (level N) (level p), fun σ hσ => ?_⟩
    have hN : ∀ x ∈ level N, σ x = x := fun x hx => hσ x ((le_sup_left : level N ≤ level N ⊔ level p) hx)
    have hP : ∀ x ∈ level p, σ x = x := fun x hx => hσ x ((le_sup_right : level p ≤ level N ⊔ level p) hx)
    refine diag_eq_one ?_ ?_
    · rw [ha]; exact push_eq_one_of_fix N ψ₁ hN
    · rw [hb, MonoidHom.mul_apply, cycloK_eq_one_of_fix p κ hP, push_eq_one_of_fix N ψ₂ hN, one_mul]
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    have h1 : a σ = ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) := by
      rw [ha]; exact push_of_isFrobeniusAt N ψ₁ hℓ hℓN A hA hσ
    have h2 : ((b σ : κˣ) : κ) = (ℓ : κ) * (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) := by
      rw [hb, MonoidHom.mul_apply, Units.val_mul, coe_cycloK_of_isFrobeniusAt p κ hℓ hℓp A hA hσ,
        push_of_isFrobeniusAt N ψ₂ hℓ hℓN A hA hσ]
    refine ⟨?_, ?_⟩
    · rw [trace_diag, h1, h2]
    · rw [det_diag, h1, h2]; ring
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    refine diag_eq_one ?_ ?_
    · rw [ha]; exact push_eq_one_of_mem_inertiaSubgroupIn N ψ₁ hℓ hℓN A hA hσ
    · rw [hb, MonoidHom.mul_apply, cycloK_eq_one_of_mem_inertiaSubgroupIn p κ hℓ hℓp A hA hσ,
        push_eq_one_of_mem_inertiaSubgroupIn N ψ₂ hℓ hℓN A hA hσ, one_mul]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
