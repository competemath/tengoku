import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center
import Tengoku.FltAnthropic.Theorems.Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero

set_option autoImplicit false

open Matrix MatrixGroups Subgroup MulAction

noncomputable section

namespace BassSerreCuspSL2

abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))
abbrev Gp : Type := Monoid.CoprodI G23
abbrev PSL : Type := SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ)

def τ : Gp := Monoid.CoprodI.of (M := G23) (i := 0) (Multiplicative.ofAdd 1) *
  Monoid.CoprodI.of (M := G23) (i := 1) (Multiplicative.ofAdd 1)

def e : Gp ≃* PSL := ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose

/--
@isnad1 id=iff.0h1v.s8.6cb1097c3385 from=translated src=- shape=9cbf6426 vocab=c43682b3
-/
theorem mem_center_iff_eq (A : SL(2, ℤ)) : A ∈ Subgroup.center SL(2, ℤ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by rw [← pow_two]; simpa using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hA, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

/--
@isnad1 id=eq.0h0v.s11.062d835741fd from=translated src=- shape=6b86c439 vocab=65271c3f
-/
theorem e_of_zero : e (Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.1

/--
@isnad1 id=eq.0h0v.s11.3295113f03d0 from=translated src=- shape=488fc1e7 vocab=76fe962a
-/
theorem e_of_one : e (Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd 1))
    = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.2

/--
@isnad1 id=eq.0h0v.s9.3aa59097465b from=translated src=- shape=300acfa4 vocab=565b60a7
-/
theorem e_τ : e τ = QuotientGroup.mk ModularGroup.T := by
  have hSS : ModularGroup.S * ModularGroup.S = -1 := by decide
  have h1 : (QuotientGroup.mk (-1 : SL(2, ℤ)) : PSL) = 1 :=
    (QuotientGroup.eq_one_iff (-1 : SL(2, ℤ))).mpr ((mem_center_iff_eq _).mpr (Or.inr rfl))
  rw [τ, map_mul, e_of_zero, e_of_one, ← QuotientGroup.mk_mul, ← mul_assoc, hSS, QuotientGroup.mk_mul,
    h1, one_mul]

def π : SL(2, ℤ) →* Gp := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/--
@isnad1 id=eq.0h1v.s10.6d563049d313 from=translated src=- shape=dc5416c3 vocab=8f4d52f1
-/
theorem π_apply (g : SL(2, ℤ)) : π g = e.symm (QuotientGroup.mk g) := rfl

/--
@isnad1 id=eq.0h0v.s9.6fd250037eb5 from=translated src=- shape=adc20cb9 vocab=c5c947e8
-/
theorem π_T : π ModularGroup.T = τ := by
  rw [π_apply, ← e_τ, MulEquiv.symm_apply_apply]

/--
@isnad1 id=surjecti.0h0v.s9.7117323c5d97 from=translated src=- shape=7172efbb vocab=123bc72d
-/
theorem π_surjective : Function.Surjective π :=
  e.symm.surjective.comp (QuotientGroup.mk'_surjective _)

/--
@isnad1 id=le.1h1v.s9.e8542ba772d2 from=translated src=- shape=d8b2339c vocab=68bb6c25
-/
theorem π_ker_le (Γ : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : π.ker ≤ Γ := by
  intro z hz
  rw [MonoidHom.mem_ker, π_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hz
  rcases (mem_center_iff_eq z).mp hz with rfl | rfl
  · exact one_mem Γ
  · exact hneg

section Main

variable (Γ : Subgroup SL(2, ℤ))

abbrev Hm : Subgroup Gp := Γ.map π

/--
@isnad1 id=eq.1h1v.s9.ad031e671b6f from=translated src=- shape=f6d46e41 vocab=b74fff6c
-/
theorem comap_Hm (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : (Hm Γ).comap π = Γ := Subgroup.comap_map_eq_self (π_ker_le Γ hneg)

/--
@isnad1 id=iff.1h2v.s10.54c0c60ab9cb from=translated src=- shape=6ac991fc vocab=98842878
-/
theorem mem_Γ_iff (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (g : SL(2, ℤ)) : g ∈ Γ ↔ π g ∈ Hm Γ := by
  conv_lhs => rw [← comap_Hm Γ hneg]
  rfl

/--
@isnad1 id=eq.1h1v.s8.702923e14ce4 from=translated src=- shape=a586f1fa vocab=eb340e1c
-/
theorem index_Hm (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : (Hm Γ).index = Γ.index := Subgroup.index_map_eq _ π_surjective (π_ker_le Γ hneg)

def θ : SL(2, ℤ) ⧸ Γ → Gp ⧸ Hm Γ :=
  Quotient.map' π fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem π h

/--
@isnad1 id=eq.0h2v.s9.1c04dda83b42 from=translated src=- shape=7fd9ddb9 vocab=49367ba0
-/
@[scoped simp] theorem θ_mk (g : SL(2, ℤ)) : θ Γ (g : SL(2, ℤ) ⧸ Γ) = ((π g : Gp) : Gp ⧸ Hm Γ) := rfl

/--
@isnad1 id=injectiv.1h1v.s9.54fb19623191 from=translated src=- shape=11e46166 vocab=54b6bb4d
-/
theorem θ_injective (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : Function.Injective (θ Γ) := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [θ_mk, θ_mk, QuotientGroup.eq, ← map_inv, ← map_mul, ← mem_Γ_iff Γ hneg] at h
  exact QuotientGroup.eq.mpr h

/--
@isnad1 id=eq.0h3v.s11.6a67c46f74b5 from=translated src=- shape=2fc58c75 vocab=80e23345
-/
theorem θ_smul (g : SL(2, ℤ)) (x : SL(2, ℤ) ⧸ Γ) : θ Γ (g • x) = π g • θ Γ x := by
  induction x using QuotientGroup.induction_on with | H a =>
  show θ Γ ((g * a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = ((π g * π a : Gp) : Gp ⧸ Hm Γ)
  rw [θ_mk, map_mul]

/--
@isnad1 id=eq.0h3v.s11.70426694d856 from=translated src=- shape=080447b7 vocab=db797b49
-/
theorem θ_T_zpow_smul (n : ℤ) (x : SL(2, ℤ) ⧸ Γ) :
    θ Γ (ModularGroup.T ^ n • x) = τ ^ n • θ Γ x := by
  rw [θ_smul, map_zpow, π_T]

/--
@isnad1 id=eq.1h2v.s11.4b2243c3155f from=translated src=- shape=029bf4d1 vocab=504c3832
-/
theorem minimalPeriod_eq (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (x : SL(2, ℤ) ⧸ Γ) :
    Function.minimalPeriod (fun y => ModularGroup.T • y) x
      = Function.minimalPeriod (fun y => τ • y) (θ Γ x) := by
  apply Nat.dvd_antisymm
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
    apply θ_injective Γ hneg
    rw [← zpow_natCast, θ_T_zpow_smul Γ, zpow_natCast]
    exact (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, ← zpow_natCast, ← θ_T_zpow_smul Γ,
      zpow_natCast]
    congr 1
    exact (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl

/--
@isnad1 id=iff.1h3v.s13.41caafe48e81 from=translated src=- shape=0d0b37ea vocab=3b1b5483
-/
theorem mem_orbit_iff_θ (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (x y : SL(2, ℤ) ⧸ Γ) :
    x ∈ orbit (zpowers ModularGroup.T) y ↔ θ Γ x ∈ orbit (zpowers τ) (θ Γ y) := by
  constructor
  · rintro ⟨⟨_, n, rfl⟩, rfl⟩
    exact ⟨⟨τ ^ n, n, rfl⟩, (θ_T_zpow_smul Γ n y).symm⟩
  · rintro ⟨⟨_, n, rfl⟩, h⟩
    refine ⟨⟨ModularGroup.T ^ n, n, rfl⟩, θ_injective Γ hneg ?_⟩
    rw [← h]
    exact θ_T_zpow_smul Γ n y

def Θ (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : orbitRel.Quotient (zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ)
    ≃ orbitRel.Quotient (zpowers τ) (Gp ⧸ Hm Γ) :=
  Quotient.congr (Equiv.ofBijective (θ Γ)
      ⟨θ_injective Γ hneg, fun y => by
        induction y using QuotientGroup.induction_on with | H k =>
        obtain ⟨g, rfl⟩ := π_surjective k
        exact ⟨(g : SL(2, ℤ) ⧸ Γ), rfl⟩⟩)
    (fun x y => mem_orbit_iff_θ Γ hneg x y)

end Main

end BassSerreCuspSL2
open scoped _root_.P2MW.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.BassSerreCuspSL2

open BassSerreCuspSL2 in
/--
@isnad1 id=ex.2h3v.s13.d13a00f3b7a2 from=translated src=- shape=e52c5e22 vocab=f7acb9e9
-/
theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive Γ →+ R,
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (hg : g⁻¹ * ModularGroup.T ^ Function.minimalPeriod (fun x => ModularGroup.T • x)
                (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) * g ∈ Γ),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) _)
              (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ)) := by
  haveI : (Hm Γ).FiniteIndex := ⟨by rw [index_Hm Γ hneg]; exact Subgroup.FiniteIndex.index_ne_zero⟩

  set a' : MulAction.orbitRel.Quotient (Subgroup.zpowers τ) (Gp ⧸ Hm Γ) → R :=
    fun c => a ((Θ Γ hneg).symm c) with ha'def
  have ha' : ∑ᶠ c, a' c = 0 := by
    rw [← ha]
    exact finsum_eq_of_bijective (Θ Γ hneg).symm (Θ Γ hneg).symm.bijective fun c => rfl
  obtain ⟨φH, hφH⟩ :=
    Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero τ rfl (Hm Γ) R a' ha'
  refine ⟨φH.comp (MonoidHom.toAdditive (π.subgroupMap Γ)), fun g hg => ?_⟩
  have hk : (π g)⁻¹ * τ ^ Function.minimalPeriod (fun x => τ • x) ((π g : Gp) : Gp ⧸ Hm Γ) * π g
      ∈ Hm Γ := by
    rw [← θ_mk Γ, ← minimalPeriod_eq Γ hneg, ← π_T, ← map_pow, ← map_inv, ← map_mul,
      ← map_mul, ← mem_Γ_iff Γ hneg]
    exact hg
  have key := hφH (π g) hk
  rw [AddMonoidHom.comp_apply]
  have hmap : (MonoidHom.toAdditive (π.subgroupMap Γ)) (Additive.ofMul ⟨_, hg⟩)
      = Additive.ofMul ⟨_, hk⟩ := by
    show Additive.ofMul (π.subgroupMap Γ ⟨_, hg⟩) = _
    congr 1
    apply Subtype.ext
    show π (g⁻¹ * ModularGroup.T ^ _ * g) = _
    rw [map_mul, map_mul, map_inv, map_pow, π_T, minimalPeriod_eq Γ hneg, θ_mk]
  rw [hmap, key, ha'def]
  show a ((Θ Γ hneg).symm (Θ Γ hneg (Quotient.mk _ (g : SL(2, ℤ) ⧸ Γ)))) = _
  rw [Equiv.symm_apply_apply]

