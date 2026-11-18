import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Compat_Mathlib430

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero

set_option autoImplicit false

open Subgroup Monoid Monoid.CoprodI MulAction

noncomputable section

namespace BassSerreCusp

section EdgeChain

variable {G : Fin 2 → Type*} [∀ i, Group (G i)]

def lTransl (g : CoprodI G) : (CoprodI G →₀ ℤ) →+ (CoprodI G →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (g * ·)

/--
@isnad1 id=eq.0h4v.s9.9ea5f1a2b6c1 from=translated src=- shape=87cf7d45 vocab=a0015e5b
-/
@[scoped simp] theorem lTransl_single (g x : CoprodI G) (n : ℤ) :
    lTransl g (Finsupp.single x n) = Finsupp.single (g * x) n :=
  Finsupp.mapDomain_single

/--
@isnad1 id=eq.0h2v.s9.a2254cf60cf1 from=translated src=- shape=a07ebe57 vocab=95da835f
-/
@[scoped simp] theorem lTransl_one_apply (f : CoprodI G →₀ ℤ) : lTransl 1 f = f := by
  show Finsupp.mapDomain (1 * ·) f = f
  rw [show ((1 : CoprodI G) * ·) = id from funext fun x => one_mul x]
  exact Finsupp.mapDomain_id

/--
@isnad1 id=eq.0h4v.s10.3b6f17fabc93 from=translated src=- shape=6cc21c40 vocab=d144a235
-/
theorem lTransl_mul_apply (g₁ g₂ : CoprodI G) (f : CoprodI G →₀ ℤ) :
    lTransl (g₁ * g₂) f = lTransl g₁ (lTransl g₂ f) := by
  show Finsupp.mapDomain (g₁ * g₂ * ·) f
      = Finsupp.mapDomain (g₁ * ·) (Finsupp.mapDomain (g₂ * ·) f)
  rw [← Finsupp.mapDomain_comp]
  simp only [Function.comp_def, mul_assoc]

def lTranslAddAut (g : CoprodI G) : AddAut (CoprodI G →₀ ℤ) where
  toFun := lTransl g
  invFun := lTransl g⁻¹
  left_inv f := by rw [← lTransl_mul_apply, inv_mul_cancel, lTransl_one_apply]
  right_inv f := by rw [← lTransl_mul_apply, mul_inv_cancel, lTransl_one_apply]
  map_add' := (lTransl g).map_add

def lTranslMulAut : CoprodI G →* MulAut (Multiplicative (CoprodI G →₀ ℤ)) where
  toFun g := AddEquiv.toMultiplicative (lTranslAddAut g)
  map_one' := MulEquiv.ext fun f => Multiplicative.toAdd.injective
    (lTransl_one_apply (Multiplicative.toAdd f))
  map_mul' g₁ g₂ := MulEquiv.ext fun f => Multiplicative.toAdd.injective
    (lTransl_mul_apply g₁ g₂ (Multiplicative.toAdd f))

/--
@isnad1 id=eq.0h3v.s11.a2fc1b57c4c8 from=translated src=- shape=694f6e2a vocab=379efce6
-/
@[scoped simp] theorem toAdd_lTranslMulAut (g : CoprodI G)
    (f : Multiplicative (CoprodI G →₀ ℤ)) :
    Multiplicative.toAdd (lTranslMulAut g f) = lTransl g (Multiplicative.toAdd f) := rfl

abbrev ChainCarrier (G : Fin 2 → Type*) [∀ i, Group (G i)] : Type _ :=
  SemidirectProduct (Multiplicative (CoprodI G →₀ ℤ)) (CoprodI G) lTranslMulAut

def factorOneSect : G 1 →* ChainCarrier G where
  toFun a := ⟨Multiplicative.ofAdd
      (Finsupp.single 1 1 - Finsupp.single (CoprodI.of a) 1 : CoprodI G →₀ ℤ),
    CoprodI.of a⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ ?_
    · show Multiplicative.ofAdd (Finsupp.single 1 1 - Finsupp.single (of (1 : G 1)) 1) = 1
      rw [map_one, sub_self]; rfl
    · exact map_one _
  map_mul' a b := by
    refine SemidirectProduct.ext ?_ (map_mul CoprodI.of a b)
    show Multiplicative.ofAdd
        (Finsupp.single 1 1 - Finsupp.single (of (a * b)) 1 : CoprodI G →₀ ℤ) =
      Multiplicative.ofAdd (Finsupp.single 1 1 - Finsupp.single (of a) 1) *
        lTranslMulAut (of a)
          (Multiplicative.ofAdd (Finsupp.single 1 1 - Finsupp.single (of b) 1))
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_lTranslMulAut, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd,
      map_sub, lTransl_single, lTransl_single, mul_one, map_mul,
      sub_add_sub_cancel]

def chainSect : CoprodI G →* ChainCarrier G :=
  CoprodI.lift fun i =>
    match i with
    | 0 => SemidirectProduct.inr.comp CoprodI.of
    | 1 => factorOneSect

/--
@isnad1 id=eq.0h2v.s9.6da160be85ca from=translated src=- shape=6d8cd1a1 vocab=02ac5f6d
-/
@[scoped simp] theorem chainSect_right (g : CoprodI G) : (chainSect g).right = g := by
  have h : SemidirectProduct.rightHom.comp chainSect = MonoidHom.id (CoprodI G) := by
    refine CoprodI.ext_hom _ _ fun i => ?_
    match i with
    | 0 => ext a; rfl
    | 1 => ext a; rfl
  exact DFunLike.congr_fun h g

def edgeChain (g : CoprodI G) : CoprodI G →₀ ℤ :=
  Multiplicative.toAdd (chainSect g).left

/--
@isnad1 id=eq.0h1v.s8.682d3c8cf5af from=translated src=- shape=6c49b3bd vocab=9a6a20ce
-/
@[scoped simp] theorem edgeChain_one : edgeChain (1 : CoprodI G) = 0 := by
  unfold edgeChain; rw [map_one]; rfl

/--
@isnad1 id=eq.0h3v.s9.075a94e5df09 from=translated src=- shape=8442a534 vocab=bd986f57
-/
theorem edgeChain_mul (g₁ g₂ : CoprodI G) :
    edgeChain (g₁ * g₂) = edgeChain g₁ + lTransl g₁ (edgeChain g₂) := by
  unfold edgeChain
  rw [map_mul, SemidirectProduct.mul_left, chainSect_right, toAdd_mul, toAdd_lTranslMulAut]

/--
@isnad1 id=eq.0h2v.s9.52fdb3d6f47e from=translated src=- shape=7e81b49a vocab=f539f12c
-/
@[scoped simp] theorem edgeChain_of_zero (a : G 0) :
    edgeChain (CoprodI.of a : CoprodI G) = 0 := by
  unfold edgeChain chainSect
  rw [CoprodI.lift_of]
  rfl

/--
@isnad1 id=eq.0h2v.s10.592d991afe43 from=translated src=- shape=b4f89525 vocab=5787654d
-/
@[scoped simp] theorem edgeChain_of_one (a : G 1) :
    edgeChain (CoprodI.of a : CoprodI G)
      = Finsupp.single 1 1 - Finsupp.single (CoprodI.of a) 1 := by
  unfold edgeChain chainSect
  rw [CoprodI.lift_of]
  rfl

/--
@isnad1 id=eq.0h2v.s9.85ebe699878d from=translated src=- shape=167b6401 vocab=e1a23924
-/
theorem edgeChain_inv (g : CoprodI G) :
    edgeChain g⁻¹ = -lTransl g⁻¹ (edgeChain g) := by
  have h := edgeChain_mul g⁻¹ g
  rw [inv_mul_cancel, edgeChain_one, eq_comm, add_eq_zero_iff_eq_neg] at h
  exact h

/--
@isnad1 id=eq.0h3v.s11.d683964a22da from=translated src=- shape=7f2cf1d4 vocab=3f55050c
-/
theorem edgeChain_of_zero_mul_of_one (a : G 0) (b : G 1) :
    edgeChain (CoprodI.of a * CoprodI.of b : CoprodI G)
      = Finsupp.single (CoprodI.of a) 1 - Finsupp.single (CoprodI.of a * CoprodI.of b) 1 := by
  rw [edgeChain_mul, edgeChain_of_zero, edgeChain_of_one, zero_add, map_sub,
    lTransl_single, lTransl_single, mul_one]

variable (H : Subgroup (CoprodI G))

def projChain : (CoprodI G →₀ ℤ) →+ (CoprodI G ⧸ H →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (fun g => (QuotientGroup.mk g⁻¹ : CoprodI G ⧸ H))

/--
@isnad1 id=eq.0h4v.s10.82706fa86683 from=translated src=- shape=7e3c8f4c vocab=cb40790a
-/
@[scoped simp] theorem projChain_single (g : CoprodI G) (n : ℤ) :
    projChain H (Finsupp.single g n) = Finsupp.single (QuotientGroup.mk g⁻¹) n :=
  Finsupp.mapDomain_single

/--
@isnad1 id=eq.1h4v.s11.d487c12f194d from=translated src=- shape=adebb483 vocab=c6475be6
-/
theorem projChain_lTransl_of_mem (h : CoprodI G) (hh : h ∈ H) (f : CoprodI G →₀ ℤ) :
    projChain H (lTransl h f) = projChain H f := by
  show Finsupp.mapDomain _ (Finsupp.mapDomain _ f) = Finsupp.mapDomain _ f
  rw [← Finsupp.mapDomain_comp]
  congr 1
  ext x
  show (QuotientGroup.mk (h * x)⁻¹ : CoprodI G ⧸ H) = QuotientGroup.mk x⁻¹
  rw [eq_comm, QuotientGroup.eq, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  exact inv_mem hh

def edgeChainHom : Additive H →+ (CoprodI G ⧸ H →₀ ℤ) where
  toFun h := projChain H (edgeChain ((Additive.toMul h : H) : CoprodI G))
  map_zero' := by
    show projChain H (edgeChain ((1 : H) : CoprodI G)) = 0
    rw [OneMemClass.coe_one, edgeChain_one, map_zero]
  map_add' h₁ h₂ := by
    show projChain H (edgeChain ((Additive.toMul h₁ * Additive.toMul h₂ : H) : CoprodI G)) = _
    rw [Subgroup.coe_mul, edgeChain_mul, map_add,
      projChain_lTransl_of_mem H _ (Additive.toMul h₁).2]

/--
@isnad1 id=eq.0h3v.s12.0f5716f6aa1c from=translated src=- shape=3ac2717b vocab=434ffaf0
-/
theorem edgeChainHom_apply (h : H) :
    edgeChainHom H (Additive.ofMul h) = projChain H (edgeChain (h : CoprodI G)) := rfl

/--
@isnad1 id=eq.0h3v.s11.0c6aa99129d4 from=translated src=- shape=00e81928 vocab=21eafc16
-/
theorem edgeChain_conj_expand (σ η : CoprodI G) :
    edgeChain (σ * η * σ⁻¹)
      = edgeChain σ + lTransl σ (edgeChain η)
        - lTransl (σ * η * σ⁻¹) (edgeChain σ) := by
  rw [edgeChain_mul (σ * η) σ⁻¹, edgeChain_mul σ η, edgeChain_inv, map_neg,
    ← lTransl_mul_apply, sub_eq_add_neg, add_assoc]

/--
@isnad1 id=eq.1h4v.s13.d35ae9a13de4 from=translated src=- shape=2104690e vocab=66c58885
-/
theorem edgeChainHom_conj (σ η : CoprodI G) (hmem : σ * η * σ⁻¹ ∈ H) :
    edgeChainHom H (Additive.ofMul ⟨σ * η * σ⁻¹, hmem⟩)
      = projChain H (lTransl σ (edgeChain η)) := by
  rw [edgeChainHom_apply]
  show projChain H (edgeChain (σ * η * σ⁻¹)) = projChain H (lTransl σ (edgeChain η))
  rw [edgeChain_conj_expand, map_sub, map_add,
    projChain_lTransl_of_mem H _ hmem, add_sub_cancel_left]

end EdgeChain

abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))

abbrev Gp : Type := CoprodI G23

def sA : G23 0 := Multiplicative.ofAdd 1

def uA : G23 1 := Multiplicative.ofAdd 1

/--
@isnad1 id=eq.0h0v.s9.bf9ec7f4a326 from=translated src=- shape=29117943 vocab=132d0b5d
-/
theorem sA_mul_sA : sA * sA = 1 := by decide

theorem eq_ofAdd_one_pow {n : ℕ} [NeZero n] (x : Multiplicative (ZMod n)) :
    x = (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd x).val := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rfl

def τ : Gp := CoprodI.of sA * CoprodI.of uA

/--
@isnad1 id=eq.0h0v.s12.3612640065e8 from=translated src=- shape=d435c8e5 vocab=8b61ba76
-/
theorem of_sA_mul_of_sA : (CoprodI.of sA : Gp) * CoprodI.of sA = 1 := by
  rw [← map_mul, sA_mul_sA, map_one]

/--
@isnad1 id=eq.0h0v.s12.7df0d0304e5a from=translated src=- shape=ceb8b1b4 vocab=51db1384
-/
theorem of_sA_inv : (CoprodI.of sA : Gp)⁻¹ = CoprodI.of sA :=
  inv_eq_of_mul_eq_one_right of_sA_mul_of_sA

/--
@isnad1 id=eq.0h0v.s12.0c4829c0f683 from=translated src=- shape=4427535a vocab=bfb023c9
-/
theorem of_sA_mul_τ : (CoprodI.of sA : Gp) * τ = CoprodI.of uA := by
  rw [τ, ← mul_assoc, of_sA_mul_of_sA, one_mul]

/--
@isnad1 id=eq.0h0v.s11.9dd674807694 from=translated src=- shape=61de1987 vocab=1a8c8313
-/
theorem closure_sA_τ :
    Subgroup.closure {(CoprodI.of sA : Gp), τ} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  induction g using CoprodI.induction_left with
  | one => exact one_mem _
  | @mul i a x ih =>
    refine mul_mem ?_ (ih (mem_top x))
    have hs : (CoprodI.of sA : Gp) ∈ Subgroup.closure {(CoprodI.of sA : Gp), τ} :=
      subset_closure (Set.mem_insert _ _)
    have hu : (CoprodI.of uA : Gp) ∈ Subgroup.closure {(CoprodI.of sA : Gp), τ} := by
      rw [← of_sA_mul_τ]; exact mul_mem hs (subset_closure (Set.mem_insert_of_mem _ rfl))
    fin_cases i
    · rw [eq_ofAdd_one_pow a, map_pow]
      exact pow_mem hs _
    · rw [eq_ofAdd_one_pow a, map_pow]
      exact pow_mem hu _

/--
@isnad1 id=eq.0h0v.s11.7ae45d5a50b4 from=translated src=- shape=f5be2659 vocab=8e1603fc
-/
theorem edgeChain_τ :
    edgeChain τ = Finsupp.single (CoprodI.of sA) 1 - Finsupp.single τ 1 := by
  unfold τ
  rw [edgeChain_of_zero_mul_of_one]

/--
@isnad1 id=eq.0h1v.s11.559b1de59d1d from=translated src=- shape=67292487 vocab=37bd214f
-/
theorem edgeChain_τ_pow (w : ℕ) :
    edgeChain (τ ^ w)
      = ∑ j ∈ Finset.range w,
          (Finsupp.single (τ ^ j * CoprodI.of sA) 1 - Finsupp.single (τ ^ (j + 1)) 1) := by
  induction w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, edgeChain_mul, ih, edgeChain_τ, map_sub, lTransl_single, lTransl_single,
      Finset.sum_range_succ, ← pow_succ]

section Cosets

variable (H : Subgroup Gp)

abbrev X : Type := Gp ⧸ H

abbrev Cu : Type := orbitRel.Quotient (zpowers τ) (X H)

def cusp (x : X H) : Cu H := Quotient.mk (orbitRel (zpowers τ) (X H)) x

/--
@isnad1 id=surjecti.0h1v.s7.47e1423d650c from=translated src=- shape=d074c16c vocab=e2452aab
-/
theorem cusp_surjective : Function.Surjective (cusp H) := Quotient.mk_surjective

/--
@isnad1 id=iff.0h3v.s12.79bc11dc0c0f from=translated src=- shape=958051f9 vocab=20f35044
-/
theorem cusp_eq_iff {x y : X H} : cusp H x = cusp H y ↔ x ∈ orbit (zpowers τ) y := by
  unfold cusp; rw [Quotient.eq]; rfl

/--
@isnad1 id=eq.0h3v.s12.fe330d040c02 from=translated src=- shape=32b0b5e8 vocab=aab6437c
-/
theorem cusp_smul (t : zpowers τ) (x : X H) : cusp H (t • x) = cusp H x :=
  (cusp_eq_iff H).mpr (mem_orbit x t)

/--
@isnad1 id=eq.0h2v.s9.72bae9f7b516 from=translated src=- shape=fef3d3ab vocab=c1ec0fbe
-/
@[scoped simp] theorem cusp_τ_smul (x : X H) : cusp H (τ • x) = cusp H x :=
  cusp_smul H ⟨τ, mem_zpowers τ⟩ x

/--
@isnad1 id=eq.0h3v.s9.1752f6735b86 from=translated src=- shape=94163582 vocab=207dde84
-/
@[scoped simp] theorem cusp_τ_zpow_smul (n : ℤ) (x : X H) : cusp H (τ ^ n • x) = cusp H x :=
  cusp_smul H ⟨τ ^ n, zpow_mem (mem_zpowers τ) n⟩ x

def flip (x : X H) : X H := (CoprodI.of sA : Gp) • x

/--
@isnad1 id=eq.0h2v.s11.6bd7cfcf7574 from=translated src=- shape=094a66fd vocab=c920328d
-/
@[scoped simp] theorem flip_mk (g : Gp) : flip H (g : X H) = ((CoprodI.of sA * g : Gp) : X H) := rfl

/--
@isnad1 id=eq.0h2v.s7.8a7dba8c1564 from=translated src=- shape=5d018461 vocab=a7054e70
-/
theorem flip_flip (x : X H) : flip H (flip H x) = x := by
  rw [flip, flip, ← mul_smul, of_sA_mul_of_sA, one_smul]

def wd (x : X H) : ℕ := Function.minimalPeriod (fun y => τ • y) x

variable [H.FiniteIndex]

/--
@isnad1 id=lt.0h2v.s8.bdd28bedf10f from=translated src=- shape=efd9a9d5 vocab=27ffd59e
-/
theorem wd_pos (x : X H) : 0 < wd H x :=
  Nat.pos_of_ne_zero (MulAction.minimalPeriod_pos τ x).ne

/--
@isnad1 id=eq.0h2v.s10.72c60a682855 from=translated src=- shape=e43fe270 vocab=388febcb
-/
theorem τ_pow_wd_smul (x : X H) : τ ^ wd H x • x = x :=
  (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl

/--
@isnad1 id=iff.0h3v.s10.1857b5805c2e from=translated src=- shape=dab834c4 vocab=fb9c4fd0
-/
theorem τ_zpow_smul_eq_iff (x : X H) (n : ℤ) : τ ^ n • x = x ↔ (wd H x : ℤ) ∣ n :=
  MulAction.zpow_smul_eq_iff_minimalPeriod_dvd

/--
@isnad1 id=mem.0h2v.s10.10e6c50fef5c from=translated src=- shape=8c7c013e vocab=7971011d
-/
theorem gen_mem (g : Gp) : g⁻¹ * τ ^ wd H (g : X H) * g ∈ H := by
  have h1 : ((τ ^ wd H (g : X H) * g : Gp) : X H) = (g : X H) := τ_pow_wd_smul H (g : X H)
  rw [QuotientGroup.eq] at h1
  have h2 := H.inv_mem h1
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h2

def genAt (g : Gp) : H := ⟨g⁻¹ * τ ^ wd H (g : X H) * g, gen_mem H g⟩

def enum (g : Gp) (j : ℕ) : X H := (((τ ^ j)⁻¹ * g : Gp) : X H)

/--
@isnad1 id=eq.0h3v.s11.b431e06ab80d from=translated src=- shape=9e17dd85 vocab=3f9d5363
-/
theorem enum_eq_zpow_smul (g : Gp) (j : ℕ) : enum H g j = τ ^ (-(j : ℤ)) • (g : X H) := by
  rw [enum, zpow_neg, zpow_natCast]; rfl

/--
@isnad1 id=eq.0h3v.s8.f66daf093af7 from=translated src=- shape=607ed7ad vocab=ab78186a
-/
@[scoped simp] theorem cusp_enum (g : Gp) (j : ℕ) : cusp H (enum H g j) = cusp H (g : X H) := by
  rw [enum_eq_zpow_smul, cusp_τ_zpow_smul]

/--
@isnad1 id=eq.0h2v.s8.8211c3d9bf5d from=translated src=- shape=dceff161 vocab=f6d2408c
-/
theorem enum_zero (g : Gp) : enum H g 0 = (g : X H) := by
  rw [enum, pow_zero, inv_one, one_mul]

/--
@isnad1 id=eq.0h2v.s15.e93730b226b2 from=translated src=- shape=8bbc73bd vocab=a89c8dcf
-/
theorem edgeChainHom_genAt_raw (g : Gp) :
    edgeChainHom H (Additive.ofMul (genAt H g))
      = ∑ j ∈ Finset.range (wd H (g : X H)),
          (Finsupp.single (flip H (enum H g j)) (1 : ℤ)
            - Finsupp.single (enum H g (j + 1)) 1) := by
  have hmem' : g⁻¹ * τ ^ wd H (g : X H) * g⁻¹⁻¹ ∈ H := by
    rw [inv_inv]; exact gen_mem H g
  have hconj := edgeChainHom_conj H g⁻¹ (τ ^ wd H (g : X H)) hmem'
  have hgen : genAt H g = ⟨_, hmem'⟩ :=
    Subtype.ext (show _ = _ * _ * g⁻¹⁻¹ by rw [inv_inv]; rfl)
  rw [hgen, hconj, edgeChain_τ_pow, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, map_sub, lTransl_single, lTransl_single, projChain_single, projChain_single,
    enum, enum, flip_mk]
  congr 2
  · rw [mul_inv_rev, mul_inv_rev, inv_inv, of_sA_inv, mul_assoc]
  · rw [mul_inv_rev, inv_inv]

/--
@isnad1 id=injon.0h2v.s8.8704168141bd from=translated src=- shape=016f55ec vocab=3c98e3ca
-/
theorem enum_injOn_range (g : Gp) :
    Set.InjOn (enum H g) (Finset.range (wd H (g : X H))) := by
  intro j hj k hk heq
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  rw [enum_eq_zpow_smul, enum_eq_zpow_smul] at heq
  have hstab : τ ^ ((k : ℤ) - j) • (g : X H) = (g : X H) := by
    have h2 : (τ ^ (-(k : ℤ)))⁻¹ • (τ ^ (-(j : ℤ)) • (g : X H)) = (g : X H) := by
      rw [heq, inv_smul_smul]
    rwa [← mul_smul, ← zpow_neg, neg_neg, ← zpow_add, ← sub_eq_add_neg] at h2
  have hdvd := (τ_zpow_smul_eq_iff H _ _).mp hstab
  have hw := wd_pos H (g : X H)
  rcases hdvd with ⟨m, hm⟩
  have hbound : |(k : ℤ) - j| < wd H (g : X H) := by
    rw [abs_sub_lt_iff]; constructor <;> · push_cast; omega
  rw [hm, abs_mul, Nat.abs_cast] at hbound
  have hm0 : m = 0 := by
    by_contra hm0
    have : (wd H (g : X H) : ℤ) * 1 ≤ (wd H (g : X H) : ℤ) * |m| :=
      mul_le_mul_of_nonneg_left (Int.one_le_abs hm0) (Nat.cast_nonneg _)
    omega
  rw [hm0, mul_zero, sub_eq_zero] at hm
  exact_mod_cast hm.symm

/--
@isnad1 id=eq.0h2v.s8.f9f58b24e249 from=translated src=- shape=cb34948a vocab=7f6e98d2
-/
theorem enum_width (g : Gp) : enum H g (wd H (g : X H)) = enum H g 0 := by
  rw [enum_eq_zpow_smul, enum_zero]
  exact (τ_zpow_smul_eq_iff H _ _).mpr (by simp)

/--
@isnad1 id=eq.0h4v.s9.9755e3312dcd from=translated src=- shape=a692f47f vocab=a9f3b2b8
-/
theorem sum_enum_succ {M : Type*} [AddCommGroup M] (g : Gp) (f : X H → M) :
    ∑ j ∈ Finset.range (wd H (g : X H)), f (enum H g (j + 1))
      = ∑ j ∈ Finset.range (wd H (g : X H)), f (enum H g j) := by
  have h1 := Finset.sum_range_succ (fun j => f (enum H g j)) (wd H (g : X H))
  have h2 := Finset.sum_range_succ' (fun j => f (enum H g j)) (wd H (g : X H))
  rw [enum_width] at h1
  exact (add_right_cancel (h1.symm.trans h2)).symm

/--
@isnad1 id=ex.1h3v.s9.1e2ab80a1782 from=translated src=- shape=85d2f937 vocab=244cb279
-/
theorem exists_enum_eq_of_cusp_eq (g : Gp) {y : X H} (hy : cusp H y = cusp H (g : X H)) :
    ∃ j ∈ Finset.range (wd H (g : X H)), enum H g j = y := by
  rw [cusp_eq_iff] at hy
  obtain ⟨⟨_, n, rfl⟩, rfl⟩ := hy
  set w : ℕ := wd H (g : X H) with hw
  have hwpos : (0 : ℤ) < w := by exact_mod_cast wd_pos H (g : X H)
  refine ⟨((-n) % (w : ℤ)).toNat, ?_, ?_⟩
  · rw [Finset.mem_range]
    have h0 : 0 ≤ (-n) % (w : ℤ) := Int.emod_nonneg _ hwpos.ne'
    have h1 : (-n) % (w : ℤ) < w := Int.emod_lt_of_pos _ hwpos
    omega
  · rw [enum_eq_zpow_smul]
    show τ ^ (-((((-n) % (w : ℤ)).toNat : ℕ) : ℤ)) • (g : X H) = τ ^ n • (g : X H)
    have h0 : 0 ≤ (-n) % (w : ℤ) := Int.emod_nonneg _ hwpos.ne'
    rw [Int.toNat_of_nonneg h0, ← MulAction.zpow_smul_mod_minimalPeriod τ (g : X H) n,
      ← MulAction.zpow_smul_mod_minimalPeriod τ (g : X H) (-((-n) % (w : ℤ)))]
    congr 2
    show -(-n % (w : ℤ)) % (w : ℤ) = n % (w : ℤ)
    exact (Int.mod_modEq (-n) (w : ℤ)).neg.trans (by rw [neg_neg])

end Cosets

section Eval

variable (H : Subgroup Gp) [H.FiniteIndex]

open scoped Classical

/--
@isnad1 id=eq.0h3v.s11.0fadc7e19771 from=translated src=- shape=e9e5606d vocab=a48820a9
-/
theorem sum_ite_enum_eq (g : Gp) (y : X H) :
    (∑ j ∈ Finset.range (wd H (g : X H)), if enum H g j = y then (1 : ℤ) else 0)
      = if cusp H y = cusp H (g : X H) then 1 else 0 := by
  by_cases h : cusp H y = cusp H (g : X H)
  · rw [ite_eq_left h]
    obtain ⟨j, hj, hjy⟩ := exists_enum_eq_of_cusp_eq H g h
    have hfilt : (Finset.range (wd H (g : X H))).filter (fun k => enum H g k = y) = {j} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hj, hjy⟩, ?_⟩
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      exact enum_injOn_range H g hk1 hj (hk2.trans hjy.symm)
    rw [← Finset.sum_filter, hfilt, Finset.sum_singleton]
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun j _ => ite_eq_right fun hjy => h ?_
    rw [← hjy, cusp_enum]

/--
@isnad1 id=eq.0h3v.s15.6e4dc23e1a37 from=translated src=- shape=a6500168 vocab=776e972c
-/
theorem edgeChainHom_genAt_apply (g : Gp) (e : X H) :
    edgeChainHom H (Additive.ofMul (genAt H g)) e
      = (if cusp H (flip H e) = cusp H (g : X H) then 1 else 0)
        - (if cusp H e = cusp H (g : X H) then 1 else 0) := by
  rw [edgeChainHom_genAt_raw]
  simp only [Finsupp.coe_sub, Finsupp.finsetSum_apply, Pi.sub_apply,
    Finsupp.single_apply, Finset.sum_sub_distrib]
  rw [sum_enum_succ H g (fun x => if x = e then (1 : ℤ) else 0), sum_ite_enum_eq]
  congr 1
  calc ∑ j ∈ Finset.range (wd H (g : X H)),
          (if flip H (enum H g j) = e then (1 : ℤ) else 0)
      = ∑ j ∈ Finset.range (wd H (g : X H)),
          (if enum H g j = flip H e then (1 : ℤ) else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact propext ⟨fun h => by rw [← h, flip_flip], fun h => by rw [h, flip_flip]⟩
    _ = if cusp H (flip H e) = cusp H (g : X H) then 1 else 0 := sum_ite_enum_eq H g (flip H e)

def cuspDiffAt (e : X H) : Cu H → ℤ :=
  Pi.single (cusp H (flip H e)) 1 - Pi.single (cusp H e) 1

def edgeChar (e : X H) : Additive H →+ ℤ := (Finsupp.applyAddHom e).comp (edgeChainHom H)

/--
@isnad1 id=eq.0h3v.s13.b65104a273e6 from=translated src=- shape=76b92cdc vocab=9308677f
-/
theorem edgeChar_genAt (e : X H) (g : Gp) :
    edgeChar H e (Additive.ofMul (genAt H g)) = cuspDiffAt H e (cusp H (g : X H)) := by
  show edgeChainHom H (Additive.ofMul (genAt H g)) e = _
  rw [edgeChainHom_genAt_apply, cuspDiffAt, Pi.sub_apply, Pi.single_apply, Pi.single_apply]
  simp only [@eq_comm _ (cusp H (g : X H))]

/--
@isnad1 id=mem.0h3v.s12.4a0102b84e34 from=translated src=- shape=78cf268a vocab=f69ccab7
-/
theorem single_sub_single_mem_span_of_smul (k : Gp) (e : X H) :
    (Pi.single (cusp H (k • e)) 1 - Pi.single (cusp H e) 1 : Cu H → ℤ)
      ∈ Submodule.span ℤ (Set.range (cuspDiffAt H)) := by
  have htop : k ∈ (⊤ : Subgroup Gp) := mem_top k
  rw [← closure_sA_τ] at htop
  have key : ∀ e', (Pi.single (cusp H (k • e')) 1
        - Pi.single (cusp H e') 1 : Cu H → ℤ)
      ∈ Submodule.span ℤ (Set.range (cuspDiffAt H)) := by
    induction htop using Subgroup.closure_induction with
    | one => intro e'; rw [one_smul, sub_self]; exact Submodule.zero_mem _
    | mul x y _ _ hx hy =>
      intro e'
      rw [mul_smul]
      have := Submodule.add_mem _ (hx (y • e')) (hy e')
      rwa [sub_add_sub_cancel] at this
    | inv x _ hx =>
      intro e'
      have h1 := Submodule.neg_mem _ (hx (x⁻¹ • e'))
      rw [smul_inv_smul, neg_sub] at h1
      exact h1
    | mem x hx =>
      intro e'
      rcases hx with rfl | rfl
      · exact Submodule.subset_span ⟨e', rfl⟩
      · rw [cusp_τ_smul, sub_self]; exact Submodule.zero_mem _
  exact key e

/--
@isnad1 id=mem.0h3v.s12.cbecb720a40b from=translated src=- shape=e04359af vocab=47269afc
-/
theorem single_sub_single_mem_span_cuspDiffAt (c c' : Cu H) :
    (Pi.single c' 1 - Pi.single c 1 : Cu H → ℤ)
      ∈ Submodule.span ℤ (Set.range (cuspDiffAt H)) := by
  obtain ⟨e, rfl⟩ := cusp_surjective H c
  obtain ⟨e', rfl⟩ := cusp_surjective H c'
  induction e using QuotientGroup.induction_on with | H k =>
  induction e' using QuotientGroup.induction_on with | H k' =>
  have heq : ((k' : Gp) : X H) = (k' * k⁻¹) • ((k : Gp) : X H) := by
    show QuotientGroup.mk k' = QuotientGroup.mk ((k' * k⁻¹) * k)
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [heq]
  exact single_sub_single_mem_span_of_smul H (k' * k⁻¹) _

/--
@isnad1 id=ex.1h2v.s13.b6982a10e5c1 from=translated src=- shape=31735766 vocab=30d23d73
-/
theorem exists_addChar_of_mem_span {v : Cu H → ℤ}
    (hv : v ∈ Submodule.span ℤ (Set.range (cuspDiffAt H))) :
    ∃ φ : Additive H →+ ℤ, ∀ g : Gp, φ (Additive.ofMul (genAt H g)) = v (cusp H (g : X H)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨edgeChar H e, fun g => edgeChar_genAt H e g⟩
  | zero => exact ⟨0, fun g => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, hφ⟩ := hx
    obtain ⟨ψ, hψ⟩ := hy
    exact ⟨φ + ψ, fun g => by rw [AddMonoidHom.add_apply, hφ, hψ, Pi.add_apply]⟩
  | smul n x _ hx =>
    obtain ⟨φ, hφ⟩ := hx
    exact ⟨n • φ, fun g => by rw [AddMonoidHom.smul_apply, hφ, Pi.smul_apply]⟩

end Eval

/--
@isnad1 id=ex.1h3v.s13.364f88d97b67 from=translated src=- shape=fbad3508 vocab=1eacdaa7
-/
theorem engine (H : Subgroup Gp) [H.FiniteIndex] (R : Type*) [AddCommGroup R]
    (a : Cu H → R) (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive H →+ R, ∀ g : Gp, φ (Additive.ofMul (genAt H g)) = a (cusp H (g : X H)) := by
  classical
  haveI : Fintype (Cu H) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at ha
  have c₀ : Cu H := cusp H ((1 : Gp) : X H)

  have hreal : ∀ c : Cu H, ∃ φ : Additive H →+ ℤ,
      ∀ g : Gp, φ (Additive.ofMul (genAt H g))
        = (Pi.single c 1 - Pi.single c₀ 1 : Cu H → ℤ) (cusp H (g : X H)) :=
    fun c => exists_addChar_of_mem_span H (single_sub_single_mem_span_cuspDiffAt H c₀ c)
  choose φ hφ using hreal
  refine ⟨∑ c, (zmultiplesHom R (a c)).comp (φ c), fun g => ?_⟩
  rw [AddMonoidHom.finsetSum_apply]
  have hterm : ∀ c, ((zmultiplesHom R (a c)).comp (φ c)) (Additive.ofMul (genAt H g))
      = (if cusp H (g : X H) = c then a c else 0)
        - (if cusp H (g : X H) = c₀ then a c else 0) := by
    intro c
    rw [AddMonoidHom.comp_apply, hφ, zmultiplesHom_apply, Pi.sub_apply, Pi.single_apply,
      Pi.single_apply, sub_smul, ite_smul, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    ite_eq_left (Finset.mem_univ _)]
  by_cases h : cusp H (g : X H) = c₀
  · have h2 : (∑ c, if cusp H (g : X H) = c₀ then a c else 0) = ∑ c, a c :=
      Finset.sum_congr rfl fun c _ => ite_eq_left h
    rw [h2, ha, sub_zero]
  · have h2 : (∑ c, if cusp H (g : X H) = c₀ then a c else 0) = 0 :=
      Finset.sum_eq_zero fun c _ => ite_eq_right h
    rw [h2, sub_zero]

end BassSerreCusp
open scoped _root_.P2MW.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.BassSerreCusp

/--
@isnad1 id=ex.2h4v.s16.2f882e420f70 from=translated src=- shape=6c28ea4d vocab=efd54f0e
-/
theorem solution
    (t : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
    (ht : t = Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
                (Multiplicative.ofAdd 1) *
              Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
                (Multiplicative.ofAdd 1))
    (H : Subgroup (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))))
    [H.FiniteIndex] (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers t)
          (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive H →+ R,
      ∀ (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
        (hg : g⁻¹ * t ^ Function.minimalPeriod (fun x => t • x)
                (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) * g ∈ H),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers t) _)
              (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H)) := by
  subst ht
  obtain ⟨φ, hφ⟩ := BassSerreCusp.engine H R a ha
  exact ⟨φ, fun g hg => hφ g⟩

