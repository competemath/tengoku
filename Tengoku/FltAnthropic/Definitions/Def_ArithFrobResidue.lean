import Tengoku.Seed.RingTheory.Frobenius
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.NumberTheory.RamificationInertia.Galois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Pointwise

namespace ArithFrobResidue

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
  [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]

/--
@isnad1 id=eq.1h5v.s11.556e1f4a497f from=translated src=- shape=6c42f2e9 vocab=81a8300b
-/
theorem stabilizerHom_eq_frobenius
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    Ideal.Quotient.stabilizerHom P (P.under A) G σ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P) := by
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hL : Ideal.Quotient.stabilizerHom P (P.under A) G σ (Ideal.Quotient.mk P b)
      = (Ideal.Quotient.mk P b) ^ Nat.card (A ⧸ P.under A) := by
    rw [Ideal.Quotient.stabilizerHom_apply, MulAction.subgroup_smul_def]
    exact hσ.mk_apply b
  have hR : FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P)
        (Ideal.Quotient.mk P b)
      = (Ideal.Quotient.mk P b) ^ Fintype.card (A ⧸ P.under A) :=
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) _
  rw [hL, hR, Nat.card_eq_fintype_card]

/--
@isnad1 id=eq.1h6v.s11.dcb270f96458 from=translated src=- shape=556f66ab vocab=8dea4d63
-/
theorem stabilizerHom_apply_pow
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) (y : B ⧸ P) :
    Ideal.Quotient.stabilizerHom P (P.under A) G σ y = y ^ Fintype.card (A ⧸ P.under A) := by
  rw [stabilizerHom_eq_frobenius σ hσ]
  exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) y

/--
@isnad1 id=ex.0h4v.s11.7d551801883a from=translated src=- shape=e07453c9 vocab=b8ac3caa
-/
theorem exists_stabilizerHom_eq_frobenius [Finite G] [Algebra.IsInvariant A B G] :
    ∃ σ : MulAction.stabilizer G P,
      Ideal.Quotient.stabilizerHom P (P.under A) G σ =
        FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant A G P
  exact ⟨⟨σ, hσ.mem_stabilizer⟩, stabilizerHom_eq_frobenius _ hσ⟩

/--
@isnad1 id=eq.1h5v.s11.4b3935f91b8e from=translated src=- shape=062bf6ad vocab=1d3a1f33
-/
theorem orderOf_stabilizerHom_eq_finrank
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (Ideal.Quotient.stabilizerHom P (P.under A) G σ) =
      Module.finrank (A ⧸ P.under A) (B ⧸ P) := by
  rw [stabilizerHom_eq_frobenius σ hσ]
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P)

/--
@isnad1 id=ex.1h6v.s12.cc14ada89c6f from=translated src=- shape=98966731 vocab=c3dc6938
-/
theorem exists_pow_stabilizerHom_eq
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P)
    (τ : (B ⧸ P) ≃ₐ[A ⧸ P.under A] (B ⧸ P)) :
    ∃ n : ℕ, (Ideal.Quotient.stabilizerHom P (P.under A) G σ) ^ n = τ := by
  rw [stabilizerHom_eq_frobenius σ hσ]
  obtain ⟨m, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ P.under A) (B ⧸ P)).surjective τ
  exact ⟨m.1, hn⟩

omit [P.IsMaximal] [(P.under A).IsMaximal] [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)] in

/--
@isnad1 id=injectiv.1h4v.s11.9ffd463ef4df from=translated src=- shape=410b4baf vocab=6c51c865
-/
theorem stabilizerHom_injective_of_inertia_eq_bot (hP : P.inertia G = ⊥) :
    Function.Injective (Ideal.Quotient.stabilizerHom P (P.under A) G) := by
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom, Ideal.inertia,
    ← AddSubgroup.subgroupOf_inertia, ← Ideal.inertia, hP, Subgroup.bot_subgroupOf]

/--
@isnad1 id=eq.2h5v.s9.51883832b52a from=translated src=- shape=1ad258cf vocab=a2fa66ce
-/
theorem orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
    (hP : P.inertia G = ⊥)
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) := by
  have hinj := stabilizerHom_injective_of_inertia_eq_bot (A := A) (P := P) (G := G) hP
  rw [Subgroup.orderOf_coe σ,
    ← orderOf_injective (Ideal.Quotient.stabilizerHom P (P.under A) G) hinj σ,
    orderOf_stabilizerHom_eq_finrank σ hσ]

end ArithFrobResidue
