/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku

import Tengoku.LeanPool.LeanPool.SardMoreira.ToMathlib.ContinuousLinearMap

/-!
# LeanPool.SardMoreira.ContDiff
-/

@[expose] public section

open scoped unitInterval Topology NNReal
open Function Asymptotics Filter Set

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {s : Set E}

section NWithTopENat
variable {n : WithTop ℕ∞} {k : ℕ} {a : E}

/--
@isnad1 id=continuo.4h8v.s8.6b8979845a52 from=translated src=- shape=9aa14622 vocab=0bcb1fdd
-/
theorem ContDiffOn.continuousAt_iteratedFDerivWithin (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (ha : s ∈ 𝓝 a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDerivWithin 𝕜 k f s) a :=
  (hf.continuousOn_iteratedFDerivWithin hk hs).continuousAt ha

/--
@isnad1 id=eventual.3h6v.s8.78e1d0bfa7aa from=translated src=- shape=6c61aa25 vocab=aff36bd5
-/
theorem ContDiffAt.eventually_isInvertible_fderiv [CompleteSpace E] (hf : ContDiffAt 𝕜 n f a)
    (ha : (fderiv 𝕜 f a).IsInvertible) (hn : n ≠ 0) :
    ∀ᶠ x in 𝓝 a, (fderiv 𝕜 f x).IsInvertible :=
  ha.eventually <| hf.continuousAt_fderiv hn

end NWithTopENat

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

/--
@isnad1 id=eq.0h2v.s5.543860fabe2f from=translated src=- shape=1c0a5056 vocab=baa482a8
-/
@[simp]
theorem sum_partSize : ∑ i, c.partSize i = n := calc
  ∑ i, c.partSize i = Fintype.card (Σ i, Fin (c.partSize i)) := by simp
  _ = n := by rw [Fintype.card_congr c.equivSigma, Fintype.card_fin]

/--
@isnad1 id=iff.0h2v.s4.2448844d4926 from=translated src=- shape=910e6c44 vocab=b8ee5f34
-/
@[simp]
theorem length_eq_zero : c.length = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ nonpos_iff_eq_zero.mp <| h ▸ c.length_le⟩
  rw [← c.sum_partSize, Finset.sum_eq_zero]
  simp [(c.partSize_pos _).ne', h]

/--
@isnad1 id=iff.0h2v.s4.6868df7c2320 from=translated src=- shape=10844b75 vocab=de95cfbb
-/
@[simp] theorem length_pos_iff : 0 < c.length ↔ 0 < n := by simp [pos_iff_ne_zero]

/--
@isnad1 id=eq.0h10v.s9.145dbfec3b85 from=translated src=- shape=079d413d vocab=71e1d8cc
-/
theorem compContinuousLinearMap_compAlongOrderedFinpartition_left
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (f : F [×c.length]→L[𝕜] G) (g : ∀ i, E [×c.partSize i]→L[𝕜] F) (h : H →L[𝕜] E) :
    (c.compAlongOrderedFinpartition f g).compContinuousLinearMap (fun _ ↦ h) =
      c.compAlongOrderedFinpartition f fun i ↦ (g i).compContinuousLinearMap fun _ ↦ h := by
  ext
  simp [applyOrderedFinpartition_apply, Function.comp_def]

variable
    {α : Type*} {l : Filter α} {p₁ p₂ : α → F [×c.length]→L[𝕜] G}
    {q₁ q₂ : α → ∀ m, E [×c.partSize m]→L[𝕜] F} {B : α → ℝ} {i : ℕ}

/--
@isnad1 id=isbigo.5h13v.s11.270964106e9a from=translated src=- shape=d438e8d3 vocab=7592fd16
-/
theorem compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
    (hp_bdd : l.IsBoundedUnder (· ≤ ·) (‖p₁ ·‖))
    (hpB : (fun x ↦ p₁ x - p₂ x) =O[l] B)
    (hq₁_bdd : ∀ m, l.IsBoundedUnder (· ≤ ·) (‖q₁ · m‖))
    (hq₂_bdd : ∀ m, l.IsBoundedUnder (· ≤ ·) (‖q₂ · m‖))
    (hqB : ∀ m, (fun x ↦ q₁ x m - q₂ x m) =O[l] B) :
    (fun x ↦ (c.compAlongOrderedFinpartition (p₁ x) fun m ↦ q₁ x m) -
        c.compAlongOrderedFinpartition (p₂ x) fun m ↦ q₂ x m) =O[l] B := by
  refine .trans (.of_norm_le fun _ ↦
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · simp only [← isBigO_one_iff ℝ, ← isBigO_pi] at *
    have hqB_pi : (fun x ↦ q₁ x - q₂ x) =O[l] B := by
      simpa [Pi.sub_apply] using hqB
    have H := ((hq₁_bdd.prod_left hq₂_bdd).norm_left.pow (c.length - 1)).mul
      hqB_pi.norm_left
    simpa [mul_assoc, Pi.sub_apply] using hp_bdd.norm_left.mul <| H.const_mul_left c.length
  · have H₂ : ∀ i, (q₂ · i) =O[l] (1 : α → ℝ) := fun i ↦ (hq₂_bdd i).isBigO_one ℝ
    simpa using hpB.norm_left.mul <| .finsetProd fun i _ ↦ (H₂ i).norm_left

end OrderedFinpartition

namespace FormalMultilinearSeries

/-- The formal Taylor left inverse of a formal multilinear series at a point. -/
noncomputable def taylorLeftInv (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    FormalMultilinearSeries 𝕜 F E := fun n ↦
  FormalMultilinearSeries.id 𝕜 E x n -
    ∑ c : {c : OrderedFinpartition n // c.length < n},
      c.val.compAlongOrderedFinpartition (taylorLeftInv p x c.val.length)
        (fun m ↦ p (c.val.partSize m)) |>.compContinuousLinearMap fun _ ↦
          continuousMultilinearCurryFin1 𝕜 E F (p 1) |>.inverse

/--
@isnad1 id=eq.0h5v.s7.bb86ee91b621 from=translated src=- shape=34d3feb1 vocab=7ebffd81
-/
@[simp]
theorem taylorLeftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    p.taylorLeftInv x 0 = .uncurry0 𝕜 F x := by
  have : IsEmpty {c : OrderedFinpartition 0 // c.length < 0} := by constructor; simp
  rw [taylorLeftInv, Fintype.sum_empty]
  ext
  simp

end FormalMultilinearSeries

variable {n : WithTop ℕ∞}

/--
@isnad1 id=eq.0h3v.s6.80d0feeebc1a from=translated src=- shape=eaba7b1a vocab=7a0ae62e
-/
@[simp]
theorem ftaylorSeries_id (x : E) : ftaylorSeries 𝕜 id x = .id 𝕜 E x := by
  unfold ftaylorSeries
  ext (_ | _ | n) v <;> simp [iteratedFDeriv_succ_apply_right, FormalMultilinearSeries.id]

/--
@isnad1 id=hasfderi.1h5v.s9.84e60a3294ed from=translated src=- shape=d2c66c8c vocab=26201d20
-/
theorem ContinuousLinearMap.IsInvertible.hasFDerivAt {f : E → F} {x : E}
    (h : (fderiv 𝕜 f x).IsInvertible) : HasFDerivAt f (h.choose : E →L[𝕜] F) x := by
  rw [h.choose_spec]
  exact differentiableAt_of_isInvertible_fderiv h |>.hasFDerivAt

/--
@isnad1 id=hasfderi.2h5v.s9.fed6fafc4cb4 from=translated src=- shape=4e22bb8a vocab=f0ab0445
-/
theorem OpenPartialHomeomorph.hasFDerivAt_symm_inverse (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    HasFDerivAt f.symm (fderiv 𝕜 f (f.symm y)).inverse y := by
  rw [ContinuousLinearMap.inverse, dite_eq_left hf']
  exact hf'.hasFDerivAt.of_local_left_inverse (f.symm.continuousAt hy)
    <| f.eventually_right_inverse hy

/--
@isnad1 id=eq.2h5v.s9.4fc6f3dccad3 from=translated src=- shape=4d850ab0 vocab=de185903
-/
theorem OpenPartialHomeomorph.fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    fderiv 𝕜 f.symm y = (fderiv 𝕜 f (f.symm y)).inverse :=
  f.hasFDerivAt_symm_inverse hy hf' |>.fderiv

/--
@isnad1 id=bijectiv.2h5v.s9.3afd4d14b745 from=translated src=- shape=804111a8 vocab=2fd28548
-/
theorem OpenPartialHomeomorph.bijective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Bijective (fderiv 𝕜 f.symm y) := by
  rw [f.fderiv_symm hy hf']
  exact hf'.inverse.bijective

/--
@isnad1 id=surjecti.2h5v.s9.e2b7ccf8a7a2 from=translated src=- shape=804111a8 vocab=d7c787cf
-/
theorem OpenPartialHomeomorph.surjective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Surjective (fderiv 𝕜 f.symm y) :=
  f.bijective_fderiv_symm hy hf' |>.surjective

/--
@isnad1 id=injectiv.2h5v.s9.b717d63fce6c from=translated src=- shape=804111a8 vocab=23625789
-/
theorem OpenPartialHomeomorph.injective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Injective (fderiv 𝕜 f.symm y) :=
  f.bijective_fderiv_symm hy hf' |>.injective

/--
@isnad1 id=contdiff.3h6v.s8.0f86528a86ff from=translated src=- shape=fa68f39d vocab=a2005f9c
-/
theorem OpenPartialHomeomorph.contDiffAt_symm' [CompleteSpace E] (f : OpenPartialHomeomorph E F)
    {a : F} (ha : a ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm a)).IsInvertible)
    (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.symm a :=
  f.contDiffAt_symm ha hf'.hasFDerivAt hf

/--
@isnad1 id=eq.0h5v.s11.81befa85687d from=translated src=- shape=287f20ac vocab=c70247ba
-/
theorem iteratedFDeriv_one_eq (f : E → F) (x : E) :
    iteratedFDeriv 𝕜 1 f x = (continuousMultilinearCurryFin1 𝕜 E F).symm (fderiv 𝕜 f x) := by
  ext; simp

/--
@isnad1 id=eq.4h7v.s10.0f0c002cf5a2 from=translated src=- shape=3f1cc727 vocab=2786bec7
-/
theorem OpenPartialHomeomorph.iteratedFDeriv_symm_eq_rec [CompleteSpace E]
    (f : OpenPartialHomeomorph E F) {y : F} (hy : y ∈ f.target) (hf : ContDiffAt 𝕜 n f (f.symm y))
    {i : ℕ} (hi : i ≤ n) (hf' : 0 < i → (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    iteratedFDeriv 𝕜 i f.symm y =
      (FormalMultilinearSeries.id 𝕜 E (f.symm y) i -
        ∑ c ≠ OrderedFinpartition.atomic i,
          c.compAlongOrderedFinpartition (iteratedFDeriv 𝕜 c.length f.symm y)
            (fun m ↦ iteratedFDeriv 𝕜 (c.partSize m) f (f.symm y))).compContinuousLinearMap
      fun _ ↦ fderiv 𝕜 f.symm y := by
  rcases i.eq_zero_or_pos with rfl | hi₀
  · ext
    simp
  · specialize hf' hi₀
    rcases hf' with ⟨f', hf'⟩
    replace hf' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm y) :=
      hf' ▸ (hf.of_le hi |>.differentiableAt <| mod_cast hi₀.ne').hasFDerivAt
    have H₁ : f.source ∈ 𝓝 (f.symm y) := f.open_source.mem_nhds <| f.mapsTo_symm hy
    have H₂ : ContDiffAt 𝕜 n f.symm (f (f.symm y)) := by
      rw [f.rightInvOn hy]
      exact f.contDiffAt_symm hy hf' hf
    have H₃ := calc
      (ftaylorSeries 𝕜 f.symm y).taylorComp (ftaylorSeries 𝕜 f (f.symm y)) i
      _ =  iteratedFDeriv 𝕜 i (f.symm ∘ f) (f.symm y) := by
        rw [iteratedFDeriv_comp H₂ hf hi, f.rightInvOn hy]
      _ = iteratedFDeriv 𝕜 i id (f.symm y) := by
        refine (EventuallyEq.iteratedFDeriv _ ?_ _).self_of_nhds
        filter_upwards [H₁] using f.leftInvOn
      _ = FormalMultilinearSeries.id 𝕜 E (f.symm y) i := by
        rw [← ftaylorSeries_id, ftaylorSeries]
    simp only [← H₃, FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition]
    rw [Fintype.sum_eq_add_sum_compl (OrderedFinpartition.atomic i), Finset.compl_singleton]
    ext v
    simp +unfoldPartialApp only [Finset.mem_univ, Finset.sum_erase_eq_sub,
      add_sub_cancel, sub_sub_cancel,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      OrderedFinpartition.compAlongOrderFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition, ftaylorSeries,
      (f.hasFDerivAt_symm hy hf').fderiv,
      OrderedFinpartition.atomic_emb]
    refine congrArg (iteratedFDeriv 𝕜 i (↑f.symm) y) (funext fun m ↦ ?_)
    dsimp only [OrderedFinpartition.atomic]
    rw [iteratedFDeriv_one_eq, hf'.fderiv]
    change v m =
      ((continuousMultilinearCurryFin1 𝕜 E F).symm f') (fun _ : Fin 1 => f'.symm (v m))
    rw [continuousMultilinearCurryFin1_symm_apply]
    exact (f'.apply_symm_apply (v m)).symm

namespace FormalMultilinearSeries

variable
    {α : Type*} {l : Filter α} {p₁ p₂ : α → FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α → FormalMultilinearSeries 𝕜 E F} {B : α → ℝ} {i n : ℕ}

/--
@isnad1 id=isbigo.5h13v.s11.1ee26ab69960 from=translated src=- shape=572af1a0 vocab=e6c9d45a
-/
theorem compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpB : ∀ k ≤ n, (fun x ↦ p₁ x k - p₂ x k) =O[l] B)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqB : ∀ k ≤ n, (fun x ↦ q₁ x k - q₂ x k) =O[l] B)
    (c : OrderedFinpartition n) :
    (fun x ↦ (p₁ x).compAlongOrderedFinpartition (q₁ x) c -
      (p₂ x).compAlongOrderedFinpartition (q₂ x) c) =O[l] B := by
  apply c.compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
  exacts [hp_bdd _ c.length_le, hpB _ c.length_le, fun _ ↦ hq₁_bdd _ (c.partSize_le _),
    fun _ ↦ hq₂_bdd _ (c.partSize_le _), fun _ ↦ hqB _ (c.partSize_le _)]

end FormalMultilinearSeries
