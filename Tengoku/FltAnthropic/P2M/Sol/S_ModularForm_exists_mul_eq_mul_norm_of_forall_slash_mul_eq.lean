import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq

open UpperHalfPlane SlashInvariantForm

open scoped ModularForm Manifold

set_option autoImplicit false

noncomputable section

namespace R4NormTrick

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

variable (𝒢 ℋ) in

def one𝒬 : 𝒬 := ((1 : ℋ) : 𝒬)

/--
@isnad1 id=eq.0h4v.s13.8a32c2759658 from=translated src=- shape=646cdb76 vocab=d5c3b42b
-/
theorem smul_mk (h r : ℋ) : h • ((r : ℋ) : 𝒬) = ((h * r : ℋ) : 𝒬) := rfl

/--
@isnad1 id=iff.0h3v.s11.aab9ae9b283b from=translated src=- shape=574b637d vocab=1eccb34b
-/
theorem mk_eq_one𝒬_iff (r : ℋ) : ((r : ℋ) : 𝒬) = one𝒬 𝒢 ℋ ↔ (r : GL (Fin 2) ℝ) ∈ 𝒢 := by
  rw [one𝒬, QuotientGroup.eq, mul_one, Subgroup.mem_subgroupOf]
  simp

/--
@isnad1 id=eq.0h3v.s13.a5fba2e0b34b from=translated src=- shape=01b41ed4 vocab=8866c571
-/
theorem smul_one𝒬 (h : ℋ) : h • one𝒬 𝒢 ℋ = ((h : ℋ) : 𝒬) := by
  rw [one𝒬, smul_mk, mul_one]

/--
@isnad1 id=iff.1h4v.s13.2e0b25c0746e from=translated src=- shape=0927af07 vocab=d95448f4
-/
theorem smul_eq_one𝒬_iff_of_mem {h : ℋ} (hmem : (h : GL (Fin 2) ℝ) ∈ 𝒢) (d : 𝒬) :
    h • d = one𝒬 𝒢 ℋ ↔ d = one𝒬 𝒢 ℋ := by
  induction d using QuotientGroup.induction_on with
  | H r =>
    rw [smul_mk, mk_eq_one𝒬_iff, mk_eq_one𝒬_iff]
    change (h : GL (Fin 2) ℝ) * (r : GL (Fin 2) ℝ) ∈ 𝒢 ↔ (r : GL (Fin 2) ℝ) ∈ 𝒢
    exact ⟨fun hr => by simpa using 𝒢.mul_mem (𝒢.inv_mem hmem) hr, fun hr => 𝒢.mul_mem hmem hr⟩

def X (F G : ModularForm 𝒢 k) (c : 𝒬) : ModularForm 𝒢 k :=
  haveI := Classical.dec (c = one𝒬 𝒢 ℋ)
  if c = one𝒬 𝒢 ℋ then F else G

/--
@isnad1 id=eq.0h5v.s7.e0fd3aba58c4 from=translated src=- shape=436c9b44 vocab=4837eb7d
-/
theorem X_one (F G : ModularForm 𝒢 k) : X F G (one𝒬 𝒢 ℋ) = F := by
  simp [X]

/--
@isnad1 id=eq.1h6v.s11.cb679d522d44 from=translated src=- shape=8879aa8b vocab=4353d58a
-/
theorem X_of_ne (F G : ModularForm 𝒢 k) {c : 𝒬} (hc : c ≠ one𝒬 𝒢 ℋ) : X F G c = G := by
  simp [X, hc]

def Θ (F G : ModularForm 𝒢 k) (c : 𝒬) : ℍ → ℂ := quotientFunc (X F G c) c

/--
@isnad1 id=eq.0h4v.s7.5f582902ee74 from=translated src=- shape=e90100c0 vocab=bf32a60d
-/
theorem quotientFunc_one𝒬 (G : ModularForm 𝒢 k) : quotientFunc G (one𝒬 𝒢 ℋ) = ⇑G := by
  change (⇑G : ℍ → ℂ) ∣[k] (((1 : ℋ) : GL (Fin 2) ℝ))⁻¹ = ⇑G
  simp

/--
@isnad1 id=eq.0h5v.s7.cfa424fb6904 from=translated src=- shape=0e2693e7 vocab=b0611ee9
-/
theorem Θ_one (F G : ModularForm 𝒢 k) : Θ F G (one𝒬 𝒢 ℋ) = ⇑F := by
  rw [Θ, X_one, quotientFunc_one𝒬]

/--
@isnad1 id=eq.1h6v.s11.8120c9369e83 from=translated src=- shape=5050aaa2 vocab=1d59575a
-/
theorem Θ_of_ne (F G : ModularForm 𝒢 k) {c : 𝒬} (hc : c ≠ one𝒬 𝒢 ℋ) : Θ F G c = quotientFunc G c := by
  rw [Θ, X_of_ne F G hc]

/--
@isnad1 id=eq.0h5v.s10.e568b4d14e61 from=translated src=- shape=b6cc2b90 vocab=a5dd5299
-/
theorem quotientFunc_mk' (G : ModularForm 𝒢 k) (r : ℋ) :
    quotientFunc G ((r : ℋ) : 𝒬) = (⇑G : ℍ → ℂ) ∣[k] ((r : GL (Fin 2) ℝ))⁻¹ := rfl

/--
@isnad1 id=eq.1h6v.s14.1e8b9968cd0a from=translated src=- shape=6f21e0db vocab=d0d3860c
-/
theorem prod_smul_eq [Fintype 𝒬] (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h))
    (h' : ℋ) :
    ∏ d : 𝒬, quotientFunc (X F G (h' • d)) d = ∏ d : 𝒬, Θ F G d := by
  classical
  by_cases hmem : (h' : GL (Fin 2) ℝ) ∈ 𝒢
  ·
    refine Finset.prod_congr rfl fun d _ => ?_
    by_cases hd : d = one𝒬 𝒢 ℋ
    · have e : h' • d = one𝒬 𝒢 ℋ := (smul_eq_one𝒬_iff_of_mem hmem d).mpr hd
      rw [Θ, e, hd, X_one]
    · have e : h' • d ≠ one𝒬 𝒢 ℋ := fun e => hd ((smul_eq_one𝒬_iff_of_mem hmem d).mp e)
      rw [Θ, X_of_ne F G hd, X_of_ne F G e]
  ·
    have hb1 : h'⁻¹ • one𝒬 𝒢 ℋ ≠ one𝒬 𝒢 ℋ := by
      rw [Ne, smul_one𝒬, mk_eq_one𝒬_iff]
      intro hi
      exact hmem (by simpa using 𝒢.inv_mem hi)
    have hb2 : h' • (h'⁻¹ • one𝒬 𝒢 ℋ) = one𝒬 𝒢 ℋ := smul_inv_smul _ _
    have hne : h' • one𝒬 𝒢 ℋ ≠ one𝒬 𝒢 ℋ := by
      rw [Ne, smul_one𝒬, mk_eq_one𝒬_iff]; exact hmem

    have v1 : quotientFunc (X F G (h' • one𝒬 𝒢 ℋ)) (one𝒬 𝒢 ℋ) = ⇑G := by
      rw [X_of_ne F G hne, quotientFunc_one𝒬]
    have v2 : quotientFunc (X F G (h' • (h'⁻¹ • one𝒬 𝒢 ℋ))) (h'⁻¹ • one𝒬 𝒢 ℋ) =
        (⇑F : ℍ → ℂ) ∣[k] (h' : GL (Fin 2) ℝ) := by
      rw [hb2, X_one, smul_one𝒬, quotientFunc_mk']
      simp
    have w1 : Θ F G (one𝒬 𝒢 ℋ) = ⇑F := Θ_one F G
    have w2 : Θ F G (h'⁻¹ • one𝒬 𝒢 ℋ) = (⇑G : ℍ → ℂ) ∣[k] (h' : GL (Fin 2) ℝ) := by
      rw [Θ_of_ne F G hb1, smul_one𝒬, quotientFunc_mk']
      simp

    have hoff : ∀ d : 𝒬, d ≠ one𝒬 𝒢 ℋ → d ≠ h'⁻¹ • one𝒬 𝒢 ℋ →
        quotientFunc (X F G (h' • d)) d = Θ F G d := by
      intro d hd1 hdb
      have : h' • d ≠ one𝒬 𝒢 ℋ := by
        intro e
        apply hdb
        rw [← e, inv_smul_smul]
      rw [X_of_ne F G this, Θ_of_ne F G hd1]

    have hmemb : h'⁻¹ • one𝒬 𝒢 ℋ ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ) :=
      Finset.mem_erase.mpr ⟨hb1, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (one𝒬 𝒢 ℋ)), ← Finset.mul_prod_erase _ _ hmemb,
      ← Finset.mul_prod_erase _ (Θ F G) (Finset.mem_univ (one𝒬 𝒢 ℋ)),
      ← Finset.mul_prod_erase _ (Θ F G) hmemb, v1, v2, w1, w2]
    have hrest : ∏ d ∈ ((Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ)).erase (h'⁻¹ • one𝒬 𝒢 ℋ),
          quotientFunc (X F G (h' • d)) d =
        ∏ d ∈ ((Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ)).erase (h'⁻¹ • one𝒬 𝒢 ℋ), Θ F G d := by
      refine Finset.prod_congr rfl fun d hd => ?_
      rw [Finset.mem_erase, Finset.mem_erase] at hd
      exact hoff d hd.2.1 hd.1
    rw [hrest, ← mul_assoc, ← mul_assoc, mul_comm (⇑G : ℍ → ℂ) ((⇑F : ℍ → ℂ) ∣[k] (h' : GL (Fin 2) ℝ)),
      hFG _ h'.2]

variable [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne]

def ΦSIF (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := letI := Fintype.ofFinite 𝒬; ∏ c : 𝒬, Θ F G c
  slash_action_eq' h hh := by
    letI := Fintype.ofFinite 𝒬

    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash,
      Subgroup.HasDetPlusMinusOne.abs_det hh, one_zpow, one_smul]

    have hfac : ∀ c : 𝒬, (Θ F G c) ∣[k] h = quotientFunc (X F G c) ((⟨h, hh⟩ : ℋ)⁻¹ • c) := fun c =>
      quotientFunc_smul (X F G c) hh c
    simp_rw [hfac]

    have hperm : ∏ c : 𝒬, quotientFunc (X F G c) ((⟨h, hh⟩ : ℋ)⁻¹ • c) =
        ∏ d : 𝒬, quotientFunc (X F G ((⟨h, hh⟩ : ℋ) • d)) d := by
      rw [← Equiv.prod_comp (MulAction.toPerm ((⟨h, hh⟩ : ℋ)))
        (fun c : 𝒬 => quotientFunc (X F G c) ((⟨h, hh⟩ : ℋ)⁻¹ • c))]
      refine Finset.prod_congr rfl fun d _ => ?_
      simp only [MulAction.toPerm_apply, inv_smul_smul]
    rw [hperm]
    exact prod_smul_eq F G hFG ⟨h, hh⟩

/--
@isnad1 id=eq.1h5v.s12.a6f04bc2208b from=translated src=- shape=29023cd1 vocab=ae57e484
-/
theorem ΦSIF_coe (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    (⇑(ΦSIF F G hFG) : ℍ → ℂ) = letI := Fintype.ofFinite 𝒬; ∏ c : 𝒬, Θ F G c := rfl

def ΦMF (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    ModularForm ℋ (k * Nat.card 𝒬) where
  __ := ΦSIF F G hFG
  holo' := by
    letI := Fintype.ofFinite 𝒬
    show MDiff (⇑(ΦSIF F G hFG) : ℍ → ℂ)
    rw [ΦSIF_coe]
    refine MDifferentiable.prod (fun c _ => ?_)
    induction c using Quotient.inductionOn with
    | h r => exact (ModularForm.translate (X F G ⟦r⟧) (r : GL (Fin 2) ℝ)⁻¹).holo'
  bdd_at_cusps' hc γ := by
    rintro rfl
    letI := Fintype.ofFinite 𝒬
    show IsBoundedAtImInfty ((⇑(ΦSIF F G hFG) : ℍ → ℂ) ∣[k * Nat.card 𝒬] γ)
    rw [ΦSIF_coe]
    simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter]
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = (fun x ↦ ∏ (i : 𝒬), 1) by ext; simp, Finset.prod_fn]
    refine .finsetProd (fun c _ => ?_)
    induction c using Quotient.inductionOn with
    | h r =>
      refine (ModularForm.translate (X F G ⟦r⟧) (r : GL (Fin 2) ℝ)⁻¹).bdd_at_cusps' ?_ γ rfl
      simpa using hc.of_isFiniteRelIndex_conj r.2

/--
@isnad1 id=eq.1h5v.s12.2f6dd9a564a8 from=translated src=- shape=5da5fdf1 vocab=48915fd5
-/
theorem ΦMF_coe (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    (⇑(ΦMF F G hFG) : ℍ → ℂ) = letI := Fintype.ofFinite 𝒬; ∏ c : 𝒬, Θ F G c := rfl

/--
@isnad1 id=eq.1h5v.s12.6fdd65e02494 from=translated src=- shape=e8134be4 vocab=31ce8f59
-/
theorem ΦMF_mul (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    (⇑(ΦMF F G hFG) : ℍ → ℂ) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * (⇑(ModularForm.norm ℋ G) : ℍ → ℂ) := by
  letI := Fintype.ofFinite 𝒬
  classical
  rw [ΦMF_coe, ModularForm.coe_norm]
  have e1 : (∏ c : 𝒬, Θ F G c) = Θ F G (one𝒬 𝒢 ℋ) * ∏ c ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), Θ F G c :=
    (Finset.mul_prod_erase _ (Θ F G) (Finset.mem_univ (one𝒬 𝒢 ℋ))).symm
  have e2 : (∏ c : 𝒬, quotientFunc G c) =
      quotientFunc G (one𝒬 𝒢 ℋ) * ∏ c ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), quotientFunc G c := by
    rw [Finset.mul_prod_erase _ (fun c : 𝒬 => quotientFunc G c) (Finset.mem_univ (one𝒬 𝒢 ℋ))]
  have e3 : ∏ d ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), Θ F G d =
      ∏ d ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), quotientFunc G d :=
    Finset.prod_congr rfl fun d hd => Θ_of_ne F G (Finset.mem_erase.mp hd).1
  rw [e1, e2, e3, Θ_one, quotientFunc_one𝒬]
  ring

end R4NormTrick

end

open scoped ModularForm in
/--
@isnad1 id=ex.1h5v.s12.f5d645552a7c from=translated src=- shape=c4040d1b vocab=70f731e0
-/
theorem solution
    (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] {k : ℤ}
    (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : UpperHalfPlane → ℂ) ∣[k] h) * (⇑G : UpperHalfPlane → ℂ) =
      (⇑F : UpperHalfPlane → ℂ) * ((⇑G : UpperHalfPlane → ℂ) ∣[k] h)) :
    ∃ Φ : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)),
      (⇑Φ : UpperHalfPlane → ℂ) * (⇑G : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) * (⇑(ModularForm.norm ℋ G) : UpperHalfPlane → ℂ) :=
  ⟨R4NormTrick.ΦMF F G hFG, R4NormTrick.ΦMF_mul F G hFG⟩
