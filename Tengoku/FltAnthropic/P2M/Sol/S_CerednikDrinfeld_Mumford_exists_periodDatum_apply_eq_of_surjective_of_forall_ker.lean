import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker

set_option autoImplicit false

namespace CerednikDrinfeld
export _root_.CerednikDrinfeld (Mumford.PeriodDatum DegeneracyData ribbonKernel ribbonGram_apply)
namespace Mumford
export _root_.CerednikDrinfeld.Mumford (PeriodDatum)
namespace PeriodDatumOfSurjection
open _root_.CerednikDrinfeld.Mumford open _root_.CerednikDrinfeld

open _root_.CerednikDrinfeld open _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld

theorem of_surjective {G : Type} [Group G] :
    Function.Surjective (Abelianization.of : G → Abelianization G) :=
  QuotientGroup.mk_surjective

noncomputable def liftPairing {G : Type} [Group G] {A : Type} [CommGroup A] (Qh : G →* G →* A) :
    Abelianization G →* Abelianization G →* A :=
  Abelianization.lift ((Abelianization.lift Qh.flip).flip)

@[scoped simp] theorem liftPairing_of_of {G : Type} [Group G] {A : Type} [CommGroup A] (Qh : G →* G →* A)
    (α β : G) : liftPairing Qh (Abelianization.of α) (Abelianization.of β) = Qh α β := by
  simp [liftPairing, MonoidHom.flip_apply]

theorem liftPairing_symm {G : Type} [Group G] {A : Type} [CommGroup A] (Qh : G →* G →* A)
    (hsymm : ∀ α β : G, Qh α β = Qh β α) (a b : Abelianization G) :
    liftPairing Qh a b = liftPairing Qh b a := by
  obtain ⟨α, rfl⟩ := of_surjective a
  obtain ⟨β, rfl⟩ := of_surjective b
  simp [hsymm α β]

section Descend

variable {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
  {G : Type} [Group G] (Φ : Additive (Abelianization G) →+ ↥(ribbonKernel D)) (hΦ : Function.Surjective Φ)
  {A : Type} [CommGroup A] (Qh : G →* G →* A) (hsymm : ∀ α β : G, Qh α β = Qh β α)
  (hker : ∀ α : G, Φ (Additive.ofMul (Abelianization.of α)) = 0 → ∀ β : G, Qh α β = 1)

noncomputable def sec (x : ↥(ribbonKernel D)) : Abelianization G := Additive.toMul (Function.surjInv hΦ x)

theorem Φ_sec (x : ↥(ribbonKernel D)) : Φ (Additive.ofMul (sec D Φ hΦ x)) = x := by
  rw [sec, ofMul_toMul]; exact Function.surjInv_eq hΦ x

include hker in

theorem liftPairing_eq_one_of_ker (a : Abelianization G) (ha : Φ (Additive.ofMul a) = 0) (b : Abelianization G) :
    liftPairing Qh a b = 1 := by
  obtain ⟨α, rfl⟩ := of_surjective a
  obtain ⟨β, rfl⟩ := of_surjective b
  rw [liftPairing_of_of]
  exact hker α ha β

include hker in

theorem liftPairing_congr_left (a a' b : Abelianization G) (h : Φ (Additive.ofMul a) = Φ (Additive.ofMul a')) :
    liftPairing Qh a b = liftPairing Qh a' b := by
  have hk : Φ (Additive.ofMul (a * a'⁻¹)) = 0 := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, h, add_neg_cancel]
  have h1 := liftPairing_eq_one_of_ker D Φ Qh hker (a * a'⁻¹) hk b
  rw [map_mul, MonoidHom.mul_apply, map_inv, MonoidHom.inv_apply, mul_inv_eq_one] at h1
  exact h1

include hker hsymm in

theorem liftPairing_congr_right (a b b' : Abelianization G) (h : Φ (Additive.ofMul b) = Φ (Additive.ofMul b')) :
    liftPairing Qh a b = liftPairing Qh a b' := by
  rw [liftPairing_symm Qh hsymm a b, liftPairing_symm Qh hsymm a b', liftPairing_congr_left D Φ Qh hker b b' a h]

noncomputable def pairFun (x y : ↥(ribbonKernel D)) : Additive A :=
  Additive.ofMul (liftPairing Qh (sec D Φ hΦ x) (sec D Φ hΦ y))

include hker in
theorem pairFun_apply_of_left (α : G) (y : ↥(ribbonKernel D)) :
    pairFun D Φ hΦ Qh (Φ (Additive.ofMul (Abelianization.of α))) y =
      Additive.ofMul (liftPairing Qh (Abelianization.of α) (sec D Φ hΦ y)) := by
  rw [pairFun]
  congr 1
  exact liftPairing_congr_left D Φ Qh hker _ _ _ (Φ_sec D Φ hΦ _)

include hker hsymm in
theorem pairFun_apply_of_of (α β : G) :
    pairFun D Φ hΦ Qh (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))) =
      Additive.ofMul (Qh α β) := by
  rw [pairFun_apply_of_left D Φ hΦ Qh hker, liftPairing_congr_right D Φ Qh hsymm hker _ _ (Abelianization.of β)
    (Φ_sec D Φ hΦ _), liftPairing_of_of]

include hΦ in

theorem exists_eq_apply_of (x : ↥(ribbonKernel D)) : ∃ α : G, x = Φ (Additive.ofMul (Abelianization.of α)) := by
  obtain ⟨a, ha⟩ := hΦ x
  obtain ⟨α, hα⟩ := of_surjective (Additive.toMul a)
  refine ⟨α, ?_⟩
  rw [hα, ofMul_toMul, ha]

include hker hsymm in
theorem pairFun_add_left (x x' y : ↥(ribbonKernel D)) :
    pairFun D Φ hΦ Qh (x + x') y = pairFun D Φ hΦ Qh x y + pairFun D Φ hΦ Qh x' y := by
  obtain ⟨α, rfl⟩ := exists_eq_apply_of D Φ hΦ x
  obtain ⟨α', rfl⟩ := exists_eq_apply_of D Φ hΦ x'
  obtain ⟨β, rfl⟩ := exists_eq_apply_of D Φ hΦ y
  have : Φ (Additive.ofMul (Abelianization.of α)) + Φ (Additive.ofMul (Abelianization.of α')) =
      Φ (Additive.ofMul (Abelianization.of (α * α'))) := by
    rw [← map_add, ← ofMul_mul, ← map_mul]
  rw [this, pairFun_apply_of_of D Φ hΦ Qh hsymm hker, pairFun_apply_of_of D Φ hΦ Qh hsymm hker,
    pairFun_apply_of_of D Φ hΦ Qh hsymm hker, map_mul, MonoidHom.mul_apply, ofMul_mul]

include hker hsymm in
theorem pairFun_symm (x y : ↥(ribbonKernel D)) : pairFun D Φ hΦ Qh x y = pairFun D Φ hΦ Qh y x := by
  rw [pairFun, pairFun, liftPairing_symm Qh hsymm]

include hker hsymm in
theorem pairFun_add_right (x y y' : ↥(ribbonKernel D)) :
    pairFun D Φ hΦ Qh x (y + y') = pairFun D Φ hΦ Qh x y + pairFun D Φ hΦ Qh x y' := by
  rw [pairFun_symm D Φ hΦ Qh hsymm hker, pairFun_add_left D Φ hΦ Qh hsymm hker,
    pairFun_symm D Φ hΦ Qh hsymm hker y, pairFun_symm D Φ hΦ Qh hsymm hker y']

noncomputable def pairing : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D) →ₗ[ℤ] Additive A :=
  LinearMap.mk₂ ℤ (pairFun D Φ hΦ Qh)
    (pairFun_add_left D Φ hΦ Qh hsymm hker)
    (fun c m n => by
      simpa using map_zsmul (AddMonoidHom.mk' (fun m => pairFun D Φ hΦ Qh m n)
        (fun a b => pairFun_add_left D Φ hΦ Qh hsymm hker a b n)) c m)
    (pairFun_add_right D Φ hΦ Qh hsymm hker)
    (fun c m n => by
      simpa using map_zsmul (AddMonoidHom.mk' (fun n => pairFun D Φ hΦ Qh m n)
        (fun a b => pairFun_add_right D Φ hΦ Qh hsymm hker m a b)) c n)

theorem pairing_apply (x y : ↥(ribbonKernel D)) :
    pairing D Φ hΦ Qh hsymm hker x y = pairFun D Φ hΦ Qh x y := rfl

end Descend

theorem main
    {E V : Type} [Fintype E] [DecidableEq V] (D : CerednikDrinfeld.DegeneracyData E V)
    {G : Type} [Group G] (Φ : Additive (Abelianization G) →+ ↥(CerednikDrinfeld.ribbonKernel D))
    (hΦ : Function.Surjective Φ)
    (F L : Type) [Field F] [Field L] [Algebra F L] (ord : Additive Fˣ →+ ℤ)
    (Qh : G →* G →* Fˣ) (hsymm : ∀ α β : G, Qh α β = Qh β α)
    (hker : ∀ α : G, Φ (Additive.ofMul (Abelianization.of α)) = 0 → ∀ β : G, Qh α β = 1)
    (hord : ∀ α β : G, ord (Additive.ofMul (Qh α β)) =
      ∑ e : E, (D.w e : ℤ) * ((Φ (Additive.ofMul (Abelianization.of α)) : E → ℤ) e *
                              (Φ (Additive.ofMul (Abelianization.of β)) : E → ℤ) e)) :
    ∃ P : CerednikDrinfeld.Mumford.PeriodDatum D F L ord,
      ∀ α β : G, P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))) =
        Additive.ofMul (Qh α β) := by
  refine ⟨⟨pairing D Φ hΦ Qh hsymm hker, fun x y => ?_, fun x y => ?_⟩, fun α β => ?_⟩
  · rw [pairing_apply, pairing_apply, pairFun_symm D Φ hΦ Qh hsymm hker]
  · obtain ⟨α, rfl⟩ := exists_eq_apply_of D Φ hΦ x
    obtain ⟨β, rfl⟩ := exists_eq_apply_of D Φ hΦ y
    rw [pairing_apply, pairFun_apply_of_of D Φ hΦ Qh hsymm hker, hord α β, ribbonGram_apply]
  · rw [pairing_apply, pairFun_apply_of_of D Φ hΦ Qh hsymm hker]

end CerednikDrinfeld.Mumford.PeriodDatumOfSurjection
open scoped _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld.Mumford _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld.Mumford.PeriodDatumOfSurjection
open scoped _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld.Mumford
open scoped _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld _root_.CerednikDrinfeld.Mumford _root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.CerednikDrinfeld.Mumford in
theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] (D : CerednikDrinfeld.DegeneracyData E V)
    {G : Type} [Group G] (Φ : Additive (Abelianization G) →+ ↥(CerednikDrinfeld.ribbonKernel D))
    (hΦ : Function.Surjective Φ)
    (F L : Type) [Field F] [Field L] [Algebra F L] (ord : Additive Fˣ →+ ℤ)
    (Qh : G →* G →* Fˣ) (hsymm : ∀ α β : G, Qh α β = Qh β α)
    (hker : ∀ α : G, Φ (Additive.ofMul (Abelianization.of α)) = 0 → ∀ β : G, Qh α β = 1)
    (hord : ∀ α β : G, ord (Additive.ofMul (Qh α β)) =
      ∑ e : E, (D.w e : ℤ) * ((Φ (Additive.ofMul (Abelianization.of α)) : E → ℤ) e *
                              (Φ (Additive.ofMul (Abelianization.of β)) : E → ℤ) e)) :
    ∃ P : CerednikDrinfeld.Mumford.PeriodDatum D F L ord,
      ∀ α β : G, P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))) =
        Additive.ofMul (Qh α β) :=
  CerednikDrinfeld.Mumford.PeriodDatumOfSurjection.main D Φ hΦ F L ord Qh hsymm hker hord
