import Tengoku.Seed.LinearAlgebra.Matrix.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complementary right nullities

An invertible map on split coordinates identifies the upper-left kernel with
the lower-right kernel of its inverse. This gives the rectangular law with
its right-nullity orientation and no equal-cardinality premise. Stated over
an arbitrary field (in particular `ℝ` and `ℂ`).
Horn–Johnson 2013, §§0.7.5–0.7.6; atlas `complementary-nullities`, `cs-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {K : Type*} [Field K]

private def firstBlockMap {R E F G H : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (f : (E × F) ≃ₗ[R] (G × H)) : E →ₗ[R] G :=
  (LinearMap.fst R G H).comp (f.toLinearMap.comp (LinearMap.inl R E F))

private def inverseLastBlockMap {R E F G H : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (f : (E × F) ≃ₗ[R] (G × H)) : H →ₗ[R] F :=
  (LinearMap.snd R E F).comp (f.symm.toLinearMap.comp (LinearMap.inr R G H))

private def complementaryKernelEquiv {R E F G H : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (f : (E × F) ≃ₗ[R] (G × H)) :
    LinearMap.ker (firstBlockMap f) ≃ₗ[R] LinearMap.ker (inverseLastBlockMap f) where
  toFun x := ⟨(f (x.val, 0)).2, by
    change (f.symm (0, (f (x.val, 0)).2)).2 = 0
    have hx : (f (x.val, 0)).1 = 0 := x.property
    have hPair : f (x.val, 0) = (0, (f (x.val, 0)).2) := Prod.ext hx rfl
    have h := congrArg (fun y => (f.symm y).2) hPair
    simpa only [LinearEquiv.symm_apply_apply] using h.symm⟩
  invFun y := ⟨(f.symm (0, y.val)).1, by
    change (f ((f.symm (0, y.val)).1, 0)).1 = 0
    have hy : (f.symm (0, y.val)).2 = 0 := y.property
    have hPair : f.symm (0, y.val) = ((f.symm (0, y.val)).1, 0) := Prod.ext rfl hy
    have h := congrArg (fun x => (f x).1) hPair
    simpa only [LinearEquiv.apply_symm_apply] using h.symm⟩
  left_inv x := by
    apply Subtype.ext
    have hx : (f (x.val, 0)).1 = 0 := x.property
    have hPair : (0, (f (x.val, 0)).2) = f (x.val, 0) := Prod.ext hx.symm rfl
    simp only [hPair, LinearEquiv.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    have hy : (f.symm (0, y.val)).2 = 0 := y.property
    have hPair : ((f.symm (0, y.val)).1, 0) = f.symm (0, y.val) := Prod.ext rfl hy.symm
    simp only [hPair, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Subtype.ext
    change (f (x.val + y.val, 0)).2 = (f (x.val, 0)).2 + (f (y.val, 0)).2
    rw [show (x.val + y.val, (0 : F)) = (x.val, 0) + (y.val, 0) by simp, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change (f (c • x.val, 0)).2 = c • (f (x.val, 0)).2
    rw [show (c • x.val, (0 : F)) = c • (x.val, 0) by simp, map_smul]
    rfl

private def coordinateSplit {n : Type*} (p : n → Prop) [DecidablePred p] :
    (n → K) ≃ₗ[K] (({i // p i} → K) × ({i // ¬p i} → K)) where
  toFun x := (fun i => x i.val, fun i => x i.val)
  invFun x := fun i => if h : p i then x.1 ⟨i, h⟩ else x.2 ⟨i, h⟩
  left_inv x := by funext i; dsimp; split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [i.property]
  map_add' x y := rfl
  map_smul' c x := rfl

end NLAlib
