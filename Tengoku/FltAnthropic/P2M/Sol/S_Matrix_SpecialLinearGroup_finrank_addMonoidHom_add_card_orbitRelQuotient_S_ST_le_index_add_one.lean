import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center
import Tengoku.FltAnthropic.Theorems.Thm_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one

set_option autoImplicit false

open Matrix MatrixGroups Subgroup MulAction

noncomputable section

namespace OrbifoldSL2

abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))
abbrev Gp : Type := Monoid.CoprodI G23
abbrev PSL : Type := SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ)

def σ : Gp := Monoid.CoprodI.of (M := G23) (i := 0) (Multiplicative.ofAdd 1)
def υ : Gp := Monoid.CoprodI.of (M := G23) (i := 1) (Multiplicative.ofAdd 1)

theorem eq_ofAdd_one_pow' {n : ℕ} [NeZero n] (x : Multiplicative (ZMod n)) :
    x = (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd x).val := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rfl

/--
@isnad1 id=eq.0h0v.s8.505f87c8feb9 from=translated src=- shape=5813c3b9 vocab=428ea3fd
-/
theorem closure_σ_υ : Subgroup.closure {σ, υ} = (⊤ : Subgroup Gp) := by
  rw [eq_top_iff]
  intro g _
  induction g using Monoid.CoprodI.induction_left with
  | one => exact one_mem _
  | @mul i a x ih =>
    refine mul_mem ?_ (ih (Subgroup.mem_top x))
    have hmem : Monoid.CoprodI.of (M := G23) (i := i) (Multiplicative.ofAdd 1) ∈ Subgroup.closure {σ, υ} := by
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    haveI : NeZero (i.val + 2) := ⟨by omega⟩
    rw [eq_ofAdd_one_pow' a, map_pow]
    exact Subgroup.pow_mem _ hmem _

/--
@isnad1 id=fg.0h0v.s6.3ec9de5bc144 from=translated src=- shape=49959d42 vocab=560d9de1
-/
theorem fg_Gp : Group.FG Gp := by
  classical
  exact ⟨⟨{σ, υ}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact closure_σ_υ⟩⟩

/--
@isnad1 id=eq.0h1v.s11.392f83ca8904 from=translated src=- shape=66919d0d vocab=650f8354
-/
theorem range_of_eq_zpowers (i : Fin 2) :
    (Monoid.CoprodI.of (M := G23) (i := i)).range
      = Subgroup.zpowers (Monoid.CoprodI.of (M := G23) (i := i) (Multiplicative.ofAdd 1)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    haveI : NeZero (i.val + 2) := ⟨by omega⟩
    rw [eq_ofAdd_one_pow' x, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    exact ⟨_, rfl⟩

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
@isnad1 id=eq.0h0v.s9.0471bfdd8229 from=translated src=- shape=300acfa4 vocab=7078feda
-/
theorem e_σ : e σ = QuotientGroup.mk ModularGroup.S :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.1

/--
@isnad1 id=eq.0h0v.s9.a5813c6bd981 from=translated src=- shape=32326c03 vocab=37454379
-/
theorem e_υ : e υ = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.2

def π : SL(2, ℤ) →* Gp := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/--
@isnad1 id=eq.0h1v.s10.92970d4a1f19 from=translated src=- shape=dc5416c3 vocab=cc5e11ac
-/
theorem π_apply (g : SL(2, ℤ)) : π g = e.symm (QuotientGroup.mk g) := rfl

/--
@isnad1 id=eq.0h0v.s9.21403d39d5e3 from=translated src=- shape=adc20cb9 vocab=a7680780
-/
theorem π_S : π ModularGroup.S = σ := by
  rw [π_apply, ← e_σ, MulEquiv.symm_apply_apply]

/--
@isnad1 id=eq.0h0v.s9.a61d2a12da0c from=translated src=- shape=814c0512 vocab=3d8653c5
-/
theorem π_ST : π (ModularGroup.S * ModularGroup.T) = υ := by
  rw [π_apply, ← e_υ, MulEquiv.symm_apply_apply]

/--
@isnad1 id=surjecti.0h0v.s9.a003415e6468 from=translated src=- shape=7172efbb vocab=2c59ce4a
-/
theorem π_surjective : Function.Surjective π :=
  e.symm.surjective.comp (QuotientGroup.mk'_surjective _)

/--
@isnad1 id=iff.0h1v.s9.dcbe4449b89f from=translated src=- shape=330ac93f vocab=8fb75a41
-/
theorem mem_ker_π_iff (z : SL(2, ℤ)) : z ∈ π.ker ↔ z = 1 ∨ z = -1 := by
  rw [MonoidHom.mem_ker, π_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, mem_center_iff_eq]

/--
@isnad1 id=le.1h1v.s9.dc8999979ad0 from=translated src=- shape=d8b2339c vocab=567bb193
-/
theorem π_ker_le (Γ : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : π.ker ≤ Γ := by
  intro z hz
  rcases (mem_ker_π_iff z).mp hz with rfl | rfl
  · exact one_mem Γ
  · exact hneg

/--
@isnad1 id=eq.0h0v.s9.91513a4f528c from=translated src=- shape=80901ffb vocab=d6759304
-/
theorem map_zpowers_S : (Subgroup.zpowers ModularGroup.S).map π = (Monoid.CoprodI.of (M := G23) (i := 0)).range := by
  rw [MonoidHom.map_zpowers, π_S, range_of_eq_zpowers]; rfl

/--
@isnad1 id=eq.0h0v.s10.d0ad406c2774 from=translated src=- shape=343255d4 vocab=24b7d154
-/
theorem map_zpowers_ST : (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)).map π
    = (Monoid.CoprodI.of (M := G23) (i := 1)).range := by
  rw [MonoidHom.map_zpowers, π_ST, range_of_eq_zpowers]; rfl

section DoubleCoset

variable {M : Type*} [Group M] (A B : Subgroup M)

def dcFlipAux (g : M) : orbitRel.Quotient B (M ⧸ A) :=
  Quotient.mk _ ((g⁻¹ : M) : M ⧸ A)

/--
@isnad1 id=eq.0h6v.s7.3ca3a42b4d0c from=translated src=- shape=15bc31f1 vocab=46bc24d3
-/
theorem dcFlipAux_eq (g : M) (a : A) (b : B) :
    dcFlipAux A B ((a : M) * g * (b : M)) = dcFlipAux A B g := by
  apply Quotient.sound
  refine ⟨b⁻¹, ?_⟩
  show ((b⁻¹ : B) : M) • ((g⁻¹ : M) : M ⧸ A) = (((a : M) * g * b)⁻¹ : M)
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  show (((b : M)⁻¹ * g⁻¹ : M) : M ⧸ A) = (((b : M)⁻¹ * (g⁻¹ * (a : M)⁻¹) : M) : M ⧸ A)
  rw [QuotientGroup.eq]
  have : ((b : M)⁻¹ * g⁻¹)⁻¹ * ((b : M)⁻¹ * (g⁻¹ * (a : M)⁻¹)) = (a : M)⁻¹ := by group
  rw [this]
  exact A.inv_mem a.2

def dcFlip : orbitRel.Quotient A (M ⧸ B) → orbitRel.Quotient B (M ⧸ A) :=
  Quotient.lift
    (Quotient.lift (dcFlipAux A B) (fun g g' (h : QuotientGroup.leftRel B g g') => by
      rw [QuotientGroup.leftRel_apply] at h
      have : g' = (((1 : A) : M) * g * ((⟨g⁻¹ * g', h⟩ : B) : M)) := by simp
      rw [this, dcFlipAux_eq]))
    (fun x y (hxy : x ∈ orbit A y) => by
      obtain ⟨a, rfl⟩ := hxy
      induction y using QuotientGroup.induction_on with | H g =>
      show dcFlipAux A B ((a : M) * g) = dcFlipAux A B g
      have : (a : M) * g = (a : M) * g * ((1 : B) : M) := by simp
      rw [this, dcFlipAux_eq])

/--
@isnad1 id=eq.0h4v.s7.6456f98cd841 from=translated src=- shape=0baa2a07 vocab=f3572bf2
-/
theorem dcFlip_mk (g : M) :
    dcFlip A B (Quotient.mk _ (g : M ⧸ B)) = Quotient.mk _ ((g⁻¹ : M) : M ⧸ A) := rfl

/--
@isnad1 id=eq.0h4v.s6.c39ecc87eaf2 from=translated src=- shape=0cc47c59 vocab=a42712de
-/
theorem dcFlip_dcFlip (x : orbitRel.Quotient A (M ⧸ B)) : dcFlip B A (dcFlip A B x) = x := by
  induction x using Quotient.inductionOn with | h y =>
  induction y using QuotientGroup.induction_on with | H g =>
  rw [dcFlip_mk, dcFlip_mk, inv_inv]

def dcEquiv : orbitRel.Quotient A (M ⧸ B) ≃ orbitRel.Quotient B (M ⧸ A) where
  toFun := dcFlip A B
  invFun := dcFlip B A
  left_inv := dcFlip_dcFlip A B
  right_inv := dcFlip_dcFlip B A

end DoubleCoset

section Main

variable (Γ : Subgroup SL(2, ℤ))

abbrev Hm : Subgroup Gp := Γ.map π

/--
@isnad1 id=iff.1h2v.s10.904f74f47293 from=translated src=- shape=6ac991fc vocab=07b388a6
-/
theorem mem_Γ_iff (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (g : SL(2, ℤ)) : g ∈ Γ ↔ π g ∈ Hm Γ := by
  conv_lhs => rw [← Subgroup.comap_map_eq_self (π_ker_le Γ hneg)]
  rfl

/--
@isnad1 id=eq.1h1v.s8.e020fdf0fc2c from=translated src=- shape=a586f1fa vocab=9cd5d2b4
-/
theorem index_Hm (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : (Hm Γ).index = Γ.index := Subgroup.index_map_eq _ π_surjective (π_ker_le Γ hneg)

def θ : SL(2, ℤ) ⧸ Γ → Gp ⧸ Hm Γ :=
  Quotient.map' π fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem π h

/--
@isnad1 id=eq.0h2v.s9.492952e1bb95 from=translated src=- shape=7fd9ddb9 vocab=bde33bd4
-/
@[scoped simp] theorem θ_mk (g : SL(2, ℤ)) : θ Γ (g : SL(2, ℤ) ⧸ Γ) = ((π g : Gp) : Gp ⧸ Hm Γ) := rfl

/--
@isnad1 id=injectiv.1h1v.s9.52b831cc36e4 from=translated src=- shape=11e46166 vocab=cb4318fd
-/
theorem θ_injective (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : Function.Injective (θ Γ) := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [θ_mk, θ_mk, QuotientGroup.eq, ← map_inv, ← map_mul, ← mem_Γ_iff Γ hneg] at h
  exact QuotientGroup.eq.mpr h

/--
@isnad1 id=surjecti.0h1v.s8.786d96d68e09 from=translated src=- shape=d3c2bf6c vocab=7aaf5861
-/
theorem θ_surjective : Function.Surjective (θ Γ) := by
  intro y
  induction y using QuotientGroup.induction_on with | H k =>
  obtain ⟨g, rfl⟩ := π_surjective k
  exact ⟨(g : SL(2, ℤ) ⧸ Γ), rfl⟩

/--
@isnad1 id=eq.0h3v.s11.94dabb88b0af from=translated src=- shape=2fc58c75 vocab=83541495
-/
theorem θ_smul (g : SL(2, ℤ)) (x : SL(2, ℤ) ⧸ Γ) : θ Γ (g • x) = π g • θ Γ x := by
  induction x using QuotientGroup.induction_on with | H a =>
  show θ Γ ((g * a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = ((π g * π a : Gp) : Gp ⧸ Hm Γ)
  rw [θ_mk, map_mul]

def orbitEquiv (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (A : Subgroup SL(2, ℤ)) :
    orbitRel.Quotient A (SL(2, ℤ) ⧸ Γ) ≃ orbitRel.Quotient (A.map π) (Gp ⧸ Hm Γ) :=
  Quotient.congr (Equiv.ofBijective (θ Γ) ⟨θ_injective Γ hneg, θ_surjective Γ⟩) (fun x y => by
    show x ∈ orbit A y ↔ θ Γ x ∈ orbit (A.map π) (θ Γ y)
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨π a, Subgroup.mem_map_of_mem π a.2⟩, ?_⟩
      show π (a : SL(2, ℤ)) • θ Γ y = θ Γ ((a : SL(2, ℤ)) • y)
      rw [θ_smul]
    · rintro ⟨⟨_, a, ha, rfl⟩, h⟩
      refine ⟨⟨a, ha⟩, θ_injective Γ hneg ?_⟩
      show θ Γ (a • y) = θ Γ x
      rw [θ_smul]
      exact h)

variable (K : Type) [Field K]

abbrev f : Γ →* Hm Γ := π.subgroupMap Γ

/--
@isnad1 id=surjecti.0h1v.s12.c4a15d0b6597 from=translated src=- shape=0b4e88d8 vocab=e7ecc229
-/
theorem f_surjective : Function.Surjective (f Γ) := π.subgroupMap_surjective Γ

/--
@isnad1 id=eq.2h4v.s13.f7ce36cea994 from=translated src=- shape=06d613d7 vocab=76db975a
-/
theorem apply_eq_zero_of_mem_ker (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) {x : Γ} (hx : x ∈ (f Γ).ker) :
    φ (Additive.ofMul x) = 0 := by
  have hx' : (x : SL(2, ℤ)) ∈ π.ker := by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  rcases (mem_ker_π_iff _).mp hx' with h1 | h1
  · have : x = 1 := Subtype.ext h1
    rw [this, ofMul_one, map_zero]
  · have hsq : x * x = 1 := Subtype.ext (by rw [Subgroup.coe_mul, h1]; simp)
    have h3 : (2 : K) * φ (Additive.ofMul x) = 0 := by
      rw [two_mul, ← map_add, ← ofMul_mul, hsq, ofMul_one, map_zero]
    exact (mul_eq_zero.mp h3).resolve_left h2

/--
@isnad1 id=eq.2h5v.s14.36a2452e1a72 from=translated src=- shape=e97d91ea vocab=d7e1ad09
-/
theorem apply_eq_of_f_eq (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) {γ γ' : Γ} (h : f Γ γ = f Γ γ') :
    φ (Additive.ofMul γ) = φ (Additive.ofMul γ') := by
  have hker : γ⁻¹ * γ' ∈ (f Γ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h0 := apply_eq_zero_of_mem_ker Γ K h2 φ hker
  rw [ofMul_mul, ofMul_inv, map_add, map_neg, neg_add_eq_zero] at h0
  exact h0

def descFun (φ : Additive Γ →+ K) (x : Additive (Hm Γ)) : K :=
  φ (Additive.ofMul (Classical.choose (f_surjective Γ (Additive.toMul x))))

/--
@isnad1 id=eq.1h4v.s14.3c3d49c9911c from=translated src=- shape=50f4b560 vocab=4cbaf09f
-/
theorem descFun_apply (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) (γ : Γ) :
    descFun Γ K φ (Additive.ofMul (f Γ γ)) = φ (Additive.ofMul γ) :=
  apply_eq_of_f_eq Γ K h2 φ (Classical.choose_spec (f_surjective Γ (Additive.toMul (Additive.ofMul (f Γ γ)))))

def desc (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) : Additive (Hm Γ) →+ K where
  toFun := descFun Γ K φ
  map_zero' := by
    have h := descFun_apply Γ K h2 φ 1
    rw [map_one, ofMul_one, ofMul_one, map_zero] at h
    exact h
  map_add' x y := by
    obtain ⟨γ, hγ⟩ := f_surjective Γ (Additive.toMul x)
    obtain ⟨δ, hδ⟩ := f_surjective Γ (Additive.toMul y)
    have hx : x = Additive.ofMul (f Γ γ) := by rw [hγ]; rfl
    have hy : y = Additive.ofMul (f Γ δ) := by rw [hδ]; rfl
    rw [hx, hy, ← ofMul_mul, ← map_mul, descFun_apply Γ K h2, descFun_apply Γ K h2,
      descFun_apply Γ K h2, ofMul_mul, map_add]

/--
@isnad1 id=eq.1h4v.s14.58b53c485830 from=translated src=- shape=6b2dc38d vocab=27f5fa08
-/
theorem desc_apply (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) (γ : Γ) :
    desc Γ K h2 φ (Additive.ofMul (f Γ γ)) = φ (Additive.ofMul γ) :=
  descFun_apply Γ K h2 φ γ

def descL (h2 : (2 : K) ≠ 0) : (Additive Γ →+ K) →ₗ[K] (Additive (Hm Γ) →+ K) where
  toFun := desc Γ K h2
  map_add' φ ψ := by
    ext x
    obtain ⟨γ, rfl⟩ := f_surjective Γ (Additive.toMul x)
    show desc Γ K h2 (φ + ψ) (Additive.ofMul (f Γ γ)) = desc Γ K h2 φ (Additive.ofMul (f Γ γ))
      + desc Γ K h2 ψ (Additive.ofMul (f Γ γ))
    rw [desc_apply, desc_apply, desc_apply]; rfl
  map_smul' c φ := by
    ext x
    obtain ⟨γ, rfl⟩ := f_surjective Γ (Additive.toMul x)
    show desc Γ K h2 (c • φ) (Additive.ofMul (f Γ γ)) = c • desc Γ K h2 φ (Additive.ofMul (f Γ γ))
    rw [desc_apply, desc_apply]; rfl

/--
@isnad1 id=finite.0h2v.s12.1c9eebc47476 from=translated src=- shape=54ea4b68 vocab=3039b4d5
-/
theorem moduleFinite_hom [(Hm Γ).FiniteIndex] : Module.Finite K (Additive (Hm Γ) →+ K) := by
  classical
  haveI : Group.FG Gp := fg_Gp
  haveI hΓ : Group.FG (Hm Γ) := Subgroup.fg_of_index_ne_zero _
  obtain ⟨s, hs⟩ := hΓ.out
  let ev : (Additive (Hm Γ) →+ K) →ₗ[K] (s → K) :=
    { toFun := fun φ i => φ (Additive.ofMul (i : Hm Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev ?_
  intro φ ψ h
  have key : ∀ γ : Hm Γ, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (s : Set (Hm Γ)) := by rw [hs]; exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact congrFun h ⟨x, hx⟩
    | one => rw [ofMul_one, map_zero, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
    | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
  exact AddMonoidHom.ext fun x => key (Additive.toMul x)

/--
@isnad1 id=injectiv.1h2v.s14.6d25d1b4d9b4 from=translated src=- shape=02f02b1a vocab=49d5f827
-/
theorem descL_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (descL Γ K h2) := by
  intro φ ψ h
  apply AddMonoidHom.ext
  intro x
  have := congrArg (fun χ : Additive (Hm Γ) →+ K => χ (Additive.ofMul (f Γ (Additive.toMul x)))) h
  change desc Γ K h2 φ (Additive.ofMul (f Γ (Additive.toMul x)))
    = desc Γ K h2 ψ (Additive.ofMul (f Γ (Additive.toMul x))) at this
  rwa [desc_apply, desc_apply] at this

end Main

end OrbifoldSL2
open scoped _root_.P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.OrbifoldSL2

open OrbifoldSL2 in
/--
@isnad1 id=le.3h2v.s12.a7e17a919b6a from=translated src=- shape=c2841537 vocab=6fdaa9a0
-/
theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Module.finrank K (Additive Γ →+ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Γ.index + 1 := by
  haveI : (Hm Γ).FiniteIndex := ⟨by rw [index_Hm Γ hneg]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  have hK : ∀ i : Fin 2, (Nat.card (G23 i) : K) ≠ 0 := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    fin_cases i
    · exact h2
    · exact h3
  have hmain : Module.finrank K (Additive (Hm Γ) →+ K)
      + Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 0)).range))
      + Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 1)).range))
      ≤ Γ.index + 1 := by
    have h := Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
      (G := G23) (Hm Γ) K hK
    rw [index_Hm Γ hneg] at h
    exact h
  haveI := moduleFinite_hom Γ K
  have hhom : Module.finrank K (Additive Γ →+ K) ≤ Module.finrank K (Additive (Hm Γ) →+ K) :=
    LinearMap.finrank_le_finrank_of_injective (descL_injective Γ K h2)
  have hS : Nat.card (orbitRel.Quotient (Subgroup.zpowers ModularGroup.S) (SL(2, ℤ) ⧸ Γ))
      = Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 0)).range)) := by
    rw [Nat.card_congr (orbitEquiv Γ hneg (Subgroup.zpowers ModularGroup.S)), map_zpowers_S,
      Nat.card_congr (dcEquiv _ _)]
  have hST : Nat.card (orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) (SL(2, ℤ) ⧸ Γ))
      = Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 1)).range)) := by
    rw [Nat.card_congr (orbitEquiv Γ hneg (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))),
      map_zpowers_ST, Nat.card_congr (dcEquiv _ _)]
  rw [hS, hST]
  omega

