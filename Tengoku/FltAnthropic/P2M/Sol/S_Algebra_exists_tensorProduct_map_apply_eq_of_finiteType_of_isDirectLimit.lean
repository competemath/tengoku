import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Mathlib_Algebra_IsDirectLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit

set_option autoImplicit false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

namespace AlgHomSpreadUnique

open TensorProduct

variable {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))

abbrev F (i j : ι) (h : i ≤ j) : G i →ₗ[R₀] G j := (f i j h).toLinearMap

/--
@isnad1 id=directed.0h4v.s8.3d835b663382 from=translated src=- shape=b28d276e vocab=0912cbe8
-/
scoped instance directedSystem_F : DirectedSystem G fun i j h => ⇑(F f i j h) := by
  change DirectedSystem G fun i j h => ⇑(f i j h)
  infer_instance

abbrev toR (i : ι) : G i →ₐ[R₀] R := IsScalarTower.toAlgHom R₀ (G i) R

/--
@isnad1 id=eq.0h6v.s8.304faeadbb45 from=translated src=- shape=3f3196c6 vocab=78798772
-/
theorem toR_apply (i : ι) (x : G i) : toR (R₀ := R₀) (R := R) i x = algebraMap (G i) R x := rfl

noncomputable def limToR : Module.DirectLimit G (F f) →ₗ[R₀] R :=
  Module.DirectLimit.lift R₀ ι G (F f) (fun i => (toR i).toLinearMap) (fun i j hij x => hR.compatibility i j hij x)

/--
@isnad1 id=eq.1h7v.s10.ae948eb441e5 from=translated src=- shape=81dfb51a vocab=a531abea
-/
theorem limToR_of (i : ι) (x : G i) :
    limToR f hR (Module.DirectLimit.of R₀ ι G (F f) i x) = algebraMap (G i) R x :=
  Module.DirectLimit.lift_of _ _ x

/--
@isnad1 id=bijectiv.1h5v.s10.44051b74fab5 from=translated src=- shape=7b39f547 vocab=6aa8e4b4
-/
theorem limToR_bijective : Function.Bijective (limToR f hR) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
      rw [limToR_of] at hz
      have h0 : algebraMap (G i) R x = algebraMap (G i) R 0 := by rw [hz, map_zero]
      obtain ⟨k, hik, hik', hk⟩ := hR.inj i i x 0 h0
      have hk' : f i k hik x = 0 := by
        have : f i k hik' (0 : G i) = 0 := map_zero _
        rw [← this]; exact hk
      rw [← Module.DirectLimit.of_f (f := F f) (hij := hik)]
      change Module.DirectLimit.of R₀ ι G (F f) k (f i k hik x) = 0
      rw [hk', map_zero]
  · intro r
    obtain ⟨i, x, hx⟩ := hR.surj r
    exact ⟨Module.DirectLimit.of R₀ ι G (F f) i x, by rw [limToR_of]; exact hx⟩

noncomputable def limEquiv : Module.DirectLimit G (F f) ≃ₗ[R₀] R :=
  LinearEquiv.ofBijective (limToR f hR) (limToR_bijective f hR)

/--
@isnad1 id=eq.1h7v.s11.3878b8122a1c from=translated src=- shape=c8adb83e vocab=3963894d
-/
theorem limEquiv_symm_algebraMap (i : ι) (x : G i) :
    (limEquiv f hR).symm (algebraMap (G i) R x) = Module.DirectLimit.of R₀ ι G (F f) i x := by
  rw [LinearEquiv.symm_apply_eq]
  exact (limToR_of f hR i x).symm

section Tensor

variable (B : Type w₂) [CommRing B] [Algebra R₀ B]

abbrev mapT (i : ι) : G i ⊗[R₀] B →ₐ[R₀] R ⊗[R₀] B :=
  Algebra.TensorProduct.map (toR i) (AlgHom.id R₀ B)

abbrev stepT {i j : ι} (hij : i ≤ j) : G i ⊗[R₀] B →ₐ[R₀] G j ⊗[R₀] B :=
  Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B)

/--
@isnad1 id=eq.1h8v.s11.20e7bc4b9f92 from=translated src=- shape=9b29ffaa vocab=7f7fb9b2
-/
theorem stepT_eq_rTensor {i j : ι} (hij : i ≤ j) (x : G i ⊗[R₀] B) :
    stepT f B hij x = (F f i j hij).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/--
@isnad1 id=eq.2h9v.s11.4aeed0e59a5f from=translated src=- shape=96b1e15c vocab=32e6cf17
-/
theorem stepT_stepT {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G i ⊗[R₀] B) :
    stepT f B hjk (stepT f B hij x) = stepT f B (hij.trans hjk) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    congr 1
    exact DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) hij hjk g
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def Φ :
    R ⊗[R₀] B ≃ₗ[R₀] Module.DirectLimit (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) :=
  (limEquiv f hR).symm.rTensor B ≪≫ₗ TensorProduct.directLimitLeft (F f) B

/--
@isnad1 id=eq.1h8v.s13.8e1848a3420f from=translated src=- shape=debca32f vocab=45e1238f
-/
theorem Φ_mapT (i : ι) (x : G i ⊗[R₀] B) :
    Φ f hR B (mapT B i x) =
      Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul]
    change TensorProduct.directLimitLeft (F f) B (((limEquiv f hR).symm.rTensor B) (toR i g ⊗ₜ[R₀] b)) = _
    rw [LinearEquiv.rTensor_tmul, toR_apply, limEquiv_symm_algebraMap, TensorProduct.directLimitLeft_tmul_of]
  | add x y hx hy => simp only [map_add, hx, hy]

include hR in

/--
@isnad1 id=ex.2h8v.s11.0ee553a40347 from=translated src=- shape=fee7d6fd vocab=5b8e3fe3
-/
theorem exists_stepT_eq_zero {i : ι} (x : G i ⊗[R₀] B) (hx : mapT (R := R) B i x = 0) :
    ∃ (j : ι) (hij : i ≤ j), stepT f B hij x = 0 := by
  have h0 : Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) i x = 0 := by
    rw [← Φ_mapT f hR, hx, map_zero]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h0
  exact ⟨j, hij, by rw [stepT_eq_rTensor]; exact hj⟩

include hR in

/--
@isnad1 id=ex.2h9v.s11.11275aff8f5f from=translated src=- shape=1ace8eab vocab=58d9d8fa
-/
theorem exists_common_kill {i : ι} {m : ℕ} (x : Fin m → G i ⊗[R₀] B) (hx : ∀ l, mapT (R := R) B i (x l) = 0) :
    ∃ (j : ι) (hij : i ≤ j), ∀ l, stepT f B hij (x l) = 0 := by
  choose idx hidx hzero using fun l => exists_stepT_eq_zero f hR B (x l) (hx l)
  obtain ⟨M, hM⟩ := Finset.exists_le (insert i (Finset.univ.image idx))
  have hiM : i ≤ M := hM _ (Finset.mem_insert_self _ _)
  have hle : ∀ l, idx l ≤ M := fun l =>
    hM _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem idx (Finset.mem_univ l)))
  refine ⟨M, hiM, fun l => ?_⟩
  have : stepT f B hiM (x l) = stepT f B (hle l) (stepT f B (hidx l) (x l)) := by
    rw [stepT_stepT]
  rw [this, hzero, map_zero]

end Tensor

open MvPolynomial in
include hR in
/--
@isnad1 id=ex.2h10v.s12.f132c1e3ff3d from=translated src=- shape=273f5f7d vocab=dc8bcc41
-/
theorem exists_apply_eq
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FiniteType R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    {i : ι} (φ₁ φ₂ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B)
    (h : ∀ x : G i ⊗[R₀] A, mapT (R := R) B i (φ₁ x) = mapT B i (φ₂ x)) :
    ∃ (j : ι) (hij : i ≤ j), ∀ x : G i ⊗[R₀] A, stepT f B hij (φ₁ x) = stepT f B hij (φ₂ x) := by
  classical

  obtain ⟨n, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R₀) (S := A)).mp ‹_›

  obtain ⟨j, hij, hkill⟩ := exists_common_kill f hR B
    (fun k : Fin n => φ₁ ((1 : G i) ⊗ₜ[R₀] g (X k)) - φ₂ ((1 : G i) ⊗ₜ[R₀] g (X k)))
    (fun k => by rw [map_sub, h, sub_self])
  refine ⟨j, hij, ?_⟩

  let H : (G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) → (G i ⊗[R₀] A →ₐ[R₀] G j ⊗[R₀] B) := fun ψ =>
    (stepT f B hij).comp (ψ.restrictScalars R₀)
  suffices hH : H φ₁ = H φ₂ by
    intro x
    exact AlgHom.congr_fun hH x
  have hleft : ∀ (ψ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) (a : G i),
      ψ (a ⊗ₜ[R₀] (1 : A)) = a ⊗ₜ[R₀] (1 : B) := by
    intro ψ a
    have h1 : a ⊗ₜ[R₀] (1 : A) = algebraMap (G i) (G i ⊗[R₀] A) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : a ⊗ₜ[R₀] (1 : B) = algebraMap (G i) (G i ⊗[R₀] B) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h1, AlgHom.commutes, ← h2]
  apply Algebra.TensorProduct.ext
  · ext a
    change stepT f B hij (φ₁ (a ⊗ₜ[R₀] (1 : A))) = stepT f B hij (φ₂ (a ⊗ₜ[R₀] (1 : A)))
    rw [hleft, hleft]
  ·
    have key : (((H φ₁).restrictScalars R₀).comp Algebra.TensorProduct.includeRight).comp g =
        (((H φ₂).restrictScalars R₀).comp Algebra.TensorProduct.includeRight).comp g := by
      refine MvPolynomial.algHom_ext fun k => ?_
      change stepT f B hij (φ₁ ((1 : G i) ⊗ₜ[R₀] g (X k))) = stepT f B hij (φ₂ ((1 : G i) ⊗ₜ[R₀] g (X k)))
      rw [← sub_eq_zero, ← map_sub]
      exact hkill k
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hg a
    exact AlgHom.congr_fun key p

end AlgHomSpreadUnique
open scoped _root_.P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique

/--
@isnad1 id=ex.2h10v.s12.864737eb6792 from=translated src=- shape=7bd5105b vocab=434134c3
-/
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FiniteType R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    {i : ι} (φ₁ φ₂ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B)
    (h : ∀ x : G i ⊗[R₀] A,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₁ x) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₂ x)) :
    ∃ (j : ι) (hij : i ≤ j), ∀ x : G i ⊗[R₀] A,
      Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) (φ₁ x) =
        Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) (φ₂ x) := by
  classical
  exact AlgHomSpreadUnique.exists_apply_eq f hR A B φ₁ φ₂ h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
