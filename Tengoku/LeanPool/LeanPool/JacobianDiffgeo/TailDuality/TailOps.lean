/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LaurentTail.Truncation
public import Tengoku

/-!
# `truncT`/`singleT`/`mulInto`/`nuL`: the truncation and multiplication kit (serre-duality-tails)

Unit: serre-duality-tails (`docs/design/serre-duality-tails.md` §3 D1/D3, §5.1, §6 P1).

* `truncAt`/`truncT`: Miranda's truncation lattice `t^{D₁}_{D₂} : T[D₁] → T[D₂]` for `D₁ ≤ D₂`
  (coarser quotient; surjective), and its compatibility with `alphaL` (Miranda Problem C).
* `singleT`: the test-vector tail at a single point (used by the injectivity/Lemma-3.6 witnesses).
* `mulIntoAt`/`mulInto`: Miranda's `t ∘ μ_f` as ONE uniform map `T D →ₗ[ℂ] T E`, linear in `f`
  (no `f ≠ 0` needed), surjective when `f ≠ 0` (Problem B: compatibility with `alphaL`).
* `nuL`: the packaging `↥(LinSys C) →ₗ[ℂ] (T (A - C) →ₗ[ℂ] T A)` Lemma 3.4's pair map is built from,
  plus the `μ_{1/f}` inversion identity `nuL_mulInto_inv` the surjectivity endgame needs.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set TopologicalSpace
open RS RS.LaurentTail

namespace RS.TailDuality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `ordGe` monotonicity (the engine behind `truncAt`/`mulIntoAt`'s well-definedness) -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ordGe_mono (p : X) {m₁ m₂ : ℤ} (h : m₂ ≤ m₁) :
    RS.Cech.ordGe p m₁ ≤ RS.Cech.ordGe p m₂ := by
  intro ψ hψ
  rw [RS.Cech.mem_ordGe_iff] at hψ ⊢
  exact le_trans (by exact_mod_cast h) hψ

/-! ### `truncAt`/`truncT` (D1) -/

/-- Miranda's `t^{D₁}_{D₂}` at a single point: the coarsening `TailAt p D₁ →ₗ TailAt p D₂`. -/
noncomputable def truncAt (p : X) {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) :
    TailAt p D₁ →ₗ[ℂ] TailAt p D₂ :=
  Submodule.mapQ _ _ LinearMap.id (by
    rw [Submodule.comap_id]
    exact ordGe_mono p (neg_le_neg (Function.locallyFinsuppWithin.le_def.1 h p)))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem truncAt_mk (p : X) {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    truncAt p h (TailAt.mk p D₁ ψ) = TailAt.mk p D₂ ψ :=
  Submodule.mapQ_apply _ _ _ ψ

variable [DecidableEq X]

/-- Miranda's `t^{D₁}_{D₂} : T[D₁] → T[D₂]`, assembled pointwise. -/
noncomputable def truncT {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) : T D₁ →ₗ[ℂ] T D₂ where
  toFun τ := DFinsupp.mapRange (fun p => truncAt p h) (fun _ => map_zero _) τ
  map_add' τ σ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.add_apply, DFinsupp.mapRange_apply, map_add]
  map_smul' c τ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.smul_apply, DFinsupp.mapRange_apply, map_smul, RingHom.id_apply]

omit [DecidableEq X] [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem truncT_apply {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) (τ : T D₁) (p : X) :
    truncT h τ p = truncAt p h (τ p) :=
  DFinsupp.mapRange_apply (fun p => truncAt p h) (fun _ => map_zero _) τ p

/-! ### `singleT` (the test-vector tails) -/

/-- A single-point test tail: the class of `ψ` at `p`, zero elsewhere. -/
noncomputable def singleT (p : X) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : T D :=
  DFinsupp.single p (TailAt.mk p D ψ)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem singleT_apply_self (p : X) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : singleT p D ψ p = TailAt.mk p D ψ :=
  DFinsupp.single_eq_same

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem singleT_apply_of_ne {p q : X} (hqp : q ≠ p) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : singleT p D ψ q = 0 :=
  DFinsupp.single_eq_of_ne hqp

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem truncT_singleT {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    truncT h (singleT p D₁ ψ) = singleT p D₂ ψ := by
  apply DFinsupp.ext
  intro q
  rw [truncT_apply]
  rcases eq_or_ne q p with rfl | hqp
  · rw [singleT_apply_self, truncAt_mk, singleT_apply_self]
  · rw [singleT_apply_of_ne hqp, singleT_apply_of_ne hqp, map_zero]

/-! ### `mulIntoAt`/`mulInto` (D3): Miranda's `t ∘ μ_f`, uniform in `f` -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulIntoAt_bound_computation (p : X) (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (hψ : ((-(D p) : ℤ) : WithTop ℤ) ≤ ψ.ord p) :
    ((-(E p) : ℤ) : WithTop ℤ) ≤
      (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) f * ψ).ord p := by
  rw [RS.MeroGermOn.ord_mul (chartAt ℂ p).open_source (mem_chart_source ℂ p),
    RS.MeroGermOn.ord_restrict (Set.subset_univ _) (chartAt ℂ p).open_source isOpen_univ
      (mem_chart_source ℂ p)]
  calc ((-(E p) : ℤ) : WithTop ℤ) = (((D p - E p) + -(D p) : ℤ) : WithTop ℤ) := by
        congr 1; ring
    _ = ((D p - E p : ℤ) : WithTop ℤ) + ((-(D p) : ℤ) : WithTop ℤ) :=
          WithTop.coe_add (D p - E p) (-(D p))
    _ ≤ f.ord p + ψ.ord p := add_le_add hf hψ

/-- Miranda's `μ_f` composed with truncation, at a single point: `TailAt p D →ₗ TailAt p E` for
`f` whose order at `p` is bounded below by `D p - E p`. -/
noncomputable def mulIntoAt (f : RS.Mero X) (p : X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : TailAt p D →ₗ[ℂ] TailAt p E :=
  Submodule.mapQ _ _ (LinearMap.mulLeft ℂ (RS.MeroGermOn.restrict (Set.subset_univ _) f)) (by
    intro ψ hψ
    rw [RS.Cech.mem_ordGe_iff] at hψ
    rw [Submodule.mem_comap, RS.Cech.mem_ordGe_iff, LinearMap.mulLeft_apply]
    exact mulIntoAt_bound_computation p f hf ψ hψ)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
@[simp] theorem mulIntoAt_mk (f : RS.Mero X) (p : X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mulIntoAt f p hf (TailAt.mk p D ψ) =
      TailAt.mk p E (RS.MeroGermOn.restrict (Set.subset_univ _) f * ψ) :=
  Submodule.mapQ_apply _ _ _ ψ

/-- Miranda's `t ∘ μ_f : T D →ₗ T E`, uniform in `f` (linear in `f`, §3 D3). -/
noncomputable def mulInto (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : T D →ₗ[ℂ] T E where
  toFun τ := DFinsupp.mapRange (fun p => mulIntoAt f p (hf p)) (fun _ => map_zero _) τ
  map_add' τ σ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.add_apply, DFinsupp.mapRange_apply, map_add]
  map_smul' c τ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.smul_apply, DFinsupp.mapRange_apply, map_smul, RingHom.id_apply]

/-! ### `LinSys`/`Mero.ord` bookkeeping helpers -/

/-! ### `nuL` -/

end RS.TailDuality
