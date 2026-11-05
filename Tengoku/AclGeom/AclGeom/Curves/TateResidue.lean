/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Canonical
import Tengoku.AclGeom.AclGeom.Tate.FinitePotent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The valuation filtration and Tate's commensurability

The valuation ring of a place as a `k`-subspace of the function field,
its filtration by uniformizer powers, and the finiteness that drives
Tate's residue: each filtration step is spanned over the previous one
by a single monomial (the residue gauge), so `π^{−m}O_P ≺ O_P` in
Tate's almost-containment order, and multiplication operators respect
the commensurability class of `O_P`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6 via Tate residues).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The valuation ring of a place, as a `k`-submodule of the function
field.-/
noncomputable def Place.toSubmodule (P : Place k F) : Submodule k F where
  carrier := {x | P.val.valuation x ≤ 1}
  add_mem' := by
    intro a b ha hb
    change P.val.valuation (a + b) ≤ 1
    exact le_trans (P.val.valuation.map_add a b) (max_le ha hb)
  zero_mem' := by
    change P.val.valuation 0 ≤ 1
    rw [Valuation.map_zero]
    exact zero_le
  smul_mem' := by
    intro c x hx
    change P.val.valuation (c • x) ≤ 1
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul, Valuation.map_zero]
      exact zero_le
    · rw [Algebra.smul_def, Valuation.map_mul,
        valuation_algebraMap_eq_one P.algebraMap_mem hc0, one_mul]
      exact hx

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/--
@isnad1 id=iff.0h4v.s8.b4db68eb105b from=translated src=- shape=840b693d vocab=bc0ed8c3
-/
theorem Place.mem_toSubmodule_iff {P : Place k F} {x : F} :
    x ∈ P.toSubmodule ↔ P.val.valuation x ≤ 1 :=
  ⟨fun h ↦ h, fun h ↦ h⟩

/-- The filtration `A_m = π^{−m} O_P`, as `k`-submodules of the
function field.-/
noncomputable def Place.filtration (P : Place k F) (m : ℕ) :
    Submodule k F where
  carrier := {x | P.val.valuation (P.pi ^ m * x) ≤ 1}
  add_mem' := by
    intro a b ha hb
    change P.val.valuation (_ * (a + b)) ≤ 1
    rw [mul_add]
    exact le_trans (P.val.valuation.map_add _ _) (max_le ha hb)
  zero_mem' := by
    change P.val.valuation (_ * (0 : F)) ≤ 1
    rw [mul_zero, Valuation.map_zero]
    exact zero_le
  smul_mem' := by
    intro c x hx
    change P.val.valuation (_ * (c • x)) ≤ 1
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul, mul_zero, Valuation.map_zero]
      exact zero_le
    · rw [mul_smul_comm, Algebra.smul_def, Valuation.map_mul,
        valuation_algebraMap_eq_one P.algebraMap_mem hc0, one_mul]
      exact hx

/--
@isnad1 id=iff.0h5v.s9.060214f86f55 from=translated src=- shape=17efdb9c vocab=930cbb9e
-/
theorem Place.mem_filtration_iff {P : Place k F} {m : ℕ} {x : F} :
    x ∈ P.filtration m ↔ P.val.valuation (P.pi ^ m * x) ≤ 1 :=
  ⟨fun h ↦ h, fun h ↦ h⟩

/--
@isnad1 id=eq.0h3v.s6.1e7d092f6408 from=translated src=- shape=042753fa vocab=64b95fb1
-/
theorem Place.filtration_zero (P : Place k F) :
    P.filtration 0 = P.toSubmodule := by
  ext x
  rw [Place.mem_filtration_iff, Place.mem_toSubmodule_iff, pow_zero,
    one_mul]

/-- **The one-step gauge**: each filtration step is spanned over the
previous one by a single negative monomial — the residue at the top
order.
@isnad1 id=le.0h4v.s8.6ebc05225ae0 from=translated src=- shape=bb1c7e0e vocab=6a639e9c
-/
theorem Place.filtration_succ_le (P : Place k F) (m : ℕ) :
    P.filtration (m + 1) ≤ P.filtration m ⊔
      Submodule.span k {P.pi ^ (-(m + 1 : ℕ) : ℤ)} := by
  intro x hx
  have hy : P.val.valuation (P.pi ^ (m + 1) * x) ≤ 1 :=
    Place.mem_filtration_iff.1 hx
  obtain ⟨c, hc⟩ := P.exists_residue hy
  have hpine : (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) ≠ 0 :=
    zpow_ne_zero _ P.pi_ne_zero
  rcases eq_or_ne (P.pi ^ (m + 1) * x - algebraMap k F c) 0 with h0 | h0
  · have hxc : x = c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) := by
      have h1 : P.pi ^ (m + 1) * x = algebraMap k F c := by
        rwa [sub_eq_zero] at h0
      have h2 : (P.pi ^ (m + 1) : F) ≠ 0 := pow_ne_zero _ P.pi_ne_zero
      rw [Algebra.smul_def, ← h1, zpow_neg, zpow_natCast]
      field_simp
    rw [hxc]
    exact Submodule.mem_sup_right
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · have hord : 1 ≤ P.ord (P.pi ^ (m + 1) * x - algebraMap k F c) := by
      have h1 := (P.ord_pos_iff h0).2 hc
      omega
    have hmem : x - c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) ∈
        P.filtration m := by
      rw [Place.mem_filtration_iff]
      have halg : P.pi ^ m * (x - c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F)) =
          (P.pi ^ (m + 1) * x - algebraMap k F c) *
            P.pi ^ (-(1 : ℕ) : ℤ) := by
        have h2 : (P.pi : F) ≠ 0 := P.pi_ne_zero
        rw [Algebra.smul_def, zpow_neg, zpow_natCast, zpow_neg,
          zpow_natCast, pow_one]
        field_simp
        ring
      rw [halg]
      have hne : (P.pi ^ (m + 1) * x - algebraMap k F c) *
          P.pi ^ (-(1 : ℕ) : ℤ) ≠ 0 :=
        mul_ne_zero h0 (zpow_ne_zero _ P.pi_ne_zero)
      rw [← P.ord_nonneg_iff hne, P.ord_mul h0
        (zpow_ne_zero _ P.pi_ne_zero), ord_pi_zpow]
      omega
    have hdecomp : x = (x - c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F)) +
        c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) := by
      ring
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hmem)
      (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

/-- Filtration membership in terms of the order.
@isnad1 id=iff.0h5v.s7.b48cafd3f159 from=translated src=- shape=9643b15e vocab=9f9207e2
-/
theorem Place.mem_filtration_iff_ord {P : Place k F} {m : ℕ} {x : F} :
    x ∈ P.filtration m ↔ x = 0 ∨ -(m : ℤ) ≤ P.ord x := by
  rw [Place.mem_filtration_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hne : P.pi ^ m * x ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.pi_ne_zero) hx
    rw [← P.ord_nonneg_iff hne,
      P.ord_mul (pow_ne_zero _ P.pi_ne_zero) hx,
      P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
    constructor
    · intro h
      exact Or.inr (by omega)
    · rintro (h | h)
      · exact absurd h hx
      · omega

/-- **Commensurability of the filtration** (the analytic input to
Tate's residue): every filtration stage is almost contained in the
valuation ring.
@isnad1 id=almostle.0h4v.s6.923e7d0704ac from=translated src=- shape=44fb697d vocab=97cda726
-/
theorem Place.filtration_almostLE (P : Place k F) (m : ℕ) :
    AlmostLE (P.filtration m) P.toSubmodule := by
  induction m with
  | zero =>
    rw [P.filtration_zero]
    exact AlmostLE.rfl
  | succ m ih =>
    refine AlmostLE.trans ?_ ih
    obtain ⟨W, hW, hle⟩ := AlmostLE.rfl (A := P.filtration m)
    refine ⟨Submodule.span k {(P.pi ^ (-(m + 1 : ℕ) : ℤ) : F)},
      FiniteDimensional.span_of_finite k (Set.finite_singleton _), ?_⟩
    exact P.filtration_succ_le m

/-- Multiplication by a nonzero element sends the valuation ring into
a filtration stage: the pole order.
@isnad1 id=le.1h4v.s8.3d6f032d22a2 from=translated src=- shape=e3f2dd66 vocab=98fb72a8
-/
theorem Place.mulLeft_toSubmodule_le_filtration (P : Place k F)
    {h : F} (hh : h ≠ 0) :
    P.toSubmodule.map (LinearMap.mulLeft k h) ≤
      P.filtration (-(P.ord h)).toNat := by
  rintro x ⟨y, hy, rfl⟩
  rw [Place.mem_filtration_iff]
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [LinearMap.mulLeft_apply, mul_zero, mul_zero,
      Valuation.map_zero]
    exact zero_le
  rw [LinearMap.mulLeft_apply, ← mul_assoc]
  rw [Valuation.map_mul]
  have h1 : P.val.valuation (P.pi ^ (-(P.ord h)).toNat * h) ≤ 1 := by
    have h2 : (P.pi ^ (-(P.ord h)).toNat * h) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.pi_ne_zero) hh
    rw [← P.ord_nonneg_iff h2, P.ord_mul (pow_ne_zero _ P.pi_ne_zero) hh,
      P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
    omega
  calc P.val.valuation (P.pi ^ (-(P.ord h)).toNat * h) *
      P.val.valuation y ≤ 1 * 1 :=
        mul_le_mul' h1 (Place.mem_toSubmodule_iff.1 hy)
    _ = 1 := one_mul 1

/-- **Multiplication operators respect the commensurability class**:
`h · O_P ≺ O_P` — Tate's condition for the function field to act
through his algebra `E`.
@isnad1 id=almostle.1h4v.s7.6b4dade40e07 from=translated src=- shape=0de3c8c5 vocab=963473f3
-/
theorem Place.mulLeft_almostLE (P : Place k F) {h : F} (hh : h ≠ 0) :
    AlmostLE (P.toSubmodule.map (LinearMap.mulLeft k h))
      P.toSubmodule :=
  AlmostLE.mono_left (P.mulLeft_toSubmodule_le_filtration hh)
    (P.filtration_almostLE _)

section Projection

/-- A chosen `k`-linear projection of the function field onto the
valuation ring of a place.-/
noncomputable def Place.proj (P : Place k F) : F →ₗ[k] F :=
  P.toSubmodule.projection
    (Classical.choose (Submodule.exists_isCompl P.toSubmodule))
    (Classical.choose_spec (Submodule.exists_isCompl P.toSubmodule))

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/--
@isnad1 id=mem.0h4v.s8.27ea0cb74c71 from=translated src=- shape=16960338 vocab=b1c8ab0a
-/
theorem Place.proj_mem (P : Place k F) (x : F) :
    P.proj x ∈ P.toSubmodule :=
  Submodule.projection_apply_mem _ x

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/--
@isnad1 id=eq.1h4v.s8.3098f3c03dc8 from=translated src=- shape=5f240351 vocab=b1c8ab0a
-/
theorem Place.proj_eq_self (P : Place k F) {x : F}
    (hx : x ∈ P.toSubmodule) : P.proj x = x := by
  rw [Place.proj]
  have h1 := Submodule.projection_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl P.toSubmodule))
    (⟨x, hx⟩ : ↥P.toSubmodule)
  exact h1

/-- A chosen `k`-linear projection of the function field onto a
filtration stage of a place.-/
noncomputable def Place.filtrationProj (P : Place k F) (m : ℕ) :
    F →ₗ[k] F :=
  (P.filtration m).projection
    (Classical.choose (Submodule.exists_isCompl (P.filtration m)))
    (Classical.choose_spec (Submodule.exists_isCompl (P.filtration m)))

/--
@isnad1 id=mem.0h5v.s8.596721ea0e14 from=translated src=- shape=b490e222 vocab=8846402c
-/
theorem Place.filtrationProj_mem (P : Place k F) (m : ℕ) (x : F) :
    P.filtrationProj m x ∈ P.filtration m :=
  Submodule.projection_apply_mem _ x

/-- **Tate's local operator**: the commutator of the projection with
multiplication, `c(h) = [ε, mult h]`. It lies in Tate's trace class
`E₀`: its range is almost inside `O_P` and its image of `O_P` is
finite-dimensional.-/
noncomputable def Place.commutatorProj (P : Place k F) (h : F) :
    Module.End k F :=
  P.proj ∘ₗ LinearMap.mulLeft k h - LinearMap.mulLeft k h ∘ₗ P.proj

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/--
@isnad1 id=eq.0h5v.s9.e627fc8ca210 from=translated src=- shape=17777abd vocab=9af78a75
-/
theorem Place.commutatorProj_apply (P : Place k F) (h x : F) :
    P.commutatorProj h x = P.proj (h * x) - h * P.proj x := rfl

/-- `E₁`-membership: the range of `c(h)` is almost inside `O_P`.
@isnad1 id=almostle.1h4v.s7.8e079a68721f from=translated src=- shape=8540917f vocab=9cd275da
-/
theorem Place.commutatorProj_range_almostLE (P : Place k F) {h : F}
    (hh : h ≠ 0) :
    AlmostLE (LinearMap.range (P.commutatorProj h)) P.toSubmodule := by
  have hle : LinearMap.range (P.commutatorProj h) ≤
      P.toSubmodule ⊔ P.toSubmodule.map (LinearMap.mulLeft k h) := by
    rintro x ⟨y, rfl⟩
    rw [Place.commutatorProj_apply, sub_eq_add_neg]
    refine Submodule.add_mem _
      (Submodule.mem_sup_left (P.proj_mem _)) (Submodule.neg_mem _ ?_)
    exact Submodule.mem_sup_right ⟨P.proj y, P.proj_mem y, rfl⟩
  exact AlmostLE.mono_left hle
    (AlmostLE.sup AlmostLE.rfl (P.mulLeft_almostLE hh))

/-- `E₂`-membership: `c(h)` sends the valuation ring into a
finite-dimensional subspace, since it factors through the defect of
`h · O_P` over `O_P`.
@isnad1 id=finitedi.1h4v.s9.65fdfb57de73 from=translated src=- shape=5599564b vocab=3783d57c
-/
theorem Place.finiteDimensional_commutatorProj_map (P : Place k F)
    {h : F} (hh : h ≠ 0) :
    FiniteDimensional k
      (P.toSubmodule.map (P.commutatorProj h)) := by
  obtain ⟨W, hW, hle⟩ := P.mulLeft_almostLE hh
  haveI := hW
  set δ : F →ₗ[k] F := P.proj - LinearMap.id with hδ
  have hmap : P.toSubmodule.map (P.commutatorProj h) ≤ W.map δ := by
    rintro x ⟨a, ha, rfl⟩
    -- `c(h) a = (ε − 1)(h a)` since `ε a = a`.
    have h1 : P.commutatorProj h a = δ (h * a) := by
      rw [hδ, Place.commutatorProj_apply, P.proj_eq_self ha]
      rfl
    rw [h1]
    -- `h a` decomposes over `O_P ⊔ W`, and `ε − 1` kills `O_P`.
    have h2 : h * a ∈ P.toSubmodule ⊔ W :=
      hle ⟨a, ha, rfl⟩
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 h2
    have h3 : δ (h * a) = δ w := by
      rw [← huw, map_add]
      have h4 : δ u = 0 := by
        rw [hδ, LinearMap.sub_apply, LinearMap.id_apply,
          P.proj_eq_self hu, sub_self]
      rw [h4, zero_add]
    rw [h3]
    exact ⟨w, hw, rfl⟩
  exact Submodule.finiteDimensional_of_le hmap

/-- Multiplication respects the commensurability class, including by
zero.
@isnad1 id=almostle.0h4v.s7.24820c81306a from=translated src=- shape=cc34ed43 vocab=963473f3
-/
theorem Place.mulLeft_map_almostLE (P : Place k F) (h : F) :
    AlmostLE (P.toSubmodule.map (LinearMap.mulLeft k h))
      P.toSubmodule := by
  rcases eq_or_ne h 0 with rfl | hh
  · refine AlmostLE.of_le ?_
    rintro x ⟨y, -, rfl⟩
    rw [LinearMap.mulLeft_apply, zero_mul]
    exact Submodule.zero_mem _
  · exact P.mulLeft_almostLE hh

/-- The commutator operator is trace-class.
@isnad1 id=istracec.0h4v.s6.358fa4aeb518 from=translated src=- shape=3a4d472f vocab=7d467ea2
-/
theorem Place.isTraceClass_commutatorProj (P : Place k F) (h : F) :
    IsTraceClass P.toSubmodule (P.commutatorProj h) := by
  rcases eq_or_ne h 0 with rfl | hh
  · have h1 : P.commutatorProj (0 : F) = 0 := by
      refine LinearMap.ext fun x ↦ ?_
      rw [Place.commutatorProj_apply, zero_mul, zero_mul, map_zero,
        sub_zero, LinearMap.zero_apply]
    rw [h1]
    exact IsTraceClass.zero _
  · exact ⟨P.commutatorProj_range_almostLE hh,
      P.finiteDimensional_commutatorProj_map hh⟩

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- **Tate's commutator identity**: the residue commutator decomposes
through the local operators, using commutativity of multiplication.
@isnad1 id=eq.0h5v.s10.9f98e7d565da from=translated src=- shape=8cd102e9 vocab=21468abd
-/
theorem Place.commutator_eq (P : Place k F) (f g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f) =
    P.commutatorProj (f * g) -
      LinearMap.mulLeft k g ∘ₗ P.commutatorProj f := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Place.commutatorProj_apply, map_sub]
  have h1 : f * (g * x) = f * g * x := by ring
  rw [h1]
  ring

/-- **The Tate residue** of the pair `(f, g)` at a place — morally
`res_P (f dg)`: the trace of the commutator of `ε ∘ (mult f)` with
`mult g`.-/
noncomputable def Place.residue (P : Place k F) (f g : F) : k :=
  tateTrace ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
    LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f))

/-- The residue commutator is trace-class, hence finite-potent with a
well-defined trace.
@isnad1 id=istracec.0h5v.s10.80370aea7d80 from=translated src=- shape=f3863d4f vocab=131dee18
-/
theorem Place.isTraceClass_residue_commutator (P : Place k F)
    (f g : F) :
    IsTraceClass P.toSubmodule
      ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  rw [P.commutator_eq f g]
  exact (P.isTraceClass_commutatorProj (f * g)).sub
    ((P.isTraceClass_commutatorProj f).comp_left
      (P.mulLeft_map_almostLE g))

section OrdLink

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Inverse multiplications compose to the identity.
@isnad1 id=eq.1h3v.s8.3bd0479b5681 from=translated src=- shape=c5f0abcf vocab=1861b165
-/
theorem mulLeft_inv_comp {g : F} (hg : g ≠ 0) :
    LinearMap.mulLeft k g⁻¹ ∘ₗ LinearMap.mulLeft k g = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply, LinearMap.id_apply, ← mul_assoc,
    inv_mul_cancel₀ hg, one_mul]

/-- The projection conjugated by multiplication: a projection onto
`g · O_P`.-/
noncomputable def Place.conjProj (P : Place k F) (g : F) :
    Module.End k F :=
  LinearMap.mulLeft k g ∘ₗ P.proj ∘ₗ LinearMap.mulLeft k g⁻¹

/-- The transversal projection `ρ = (1 − ε') ∘ ε`: an idempotent
projecting onto a transversal of `g · O_P` in `O_P`.-/
noncomputable def Place.transversalProj (P : Place k F) (g : F) :
    Module.End k F :=
  (LinearMap.id - P.conjProj g) ∘ₗ P.proj

end OrdLink

section ResidueCalculus

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator is additive in the first slot.
@isnad1 id=eq.0h6v.s12.c88c53f7051b from=translated src=- shape=4d327681 vocab=5da857bd
-/
theorem Place.residue_commutator_add_left (P : Place k F)
    (f₁ f₂ g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k (f₁ + f₂)) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k (f₁ + f₂)) =
    ((P.proj ∘ₗ LinearMap.mulLeft k f₁) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f₁)) +
    ((P.proj ∘ₗ LinearMap.mulLeft k f₂) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f₂)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, add_mul, map_add]
  ring

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator is additive in the second slot.
@isnad1 id=eq.0h6v.s12.28f667016ccb from=translated src=- shape=f0ff0f73 vocab=5da857bd
-/
theorem Place.residue_commutator_add_right (P : Place k F)
    (f g₁ g₂ : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k (g₁ + g₂) -
      LinearMap.mulLeft k (g₁ + g₂) ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k f) =
    ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g₁ -
      LinearMap.mulLeft k g₁ ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) +
    ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g₂ -
      LinearMap.mulLeft k g₂ ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, add_mul,
    map_add]
  ring

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator scales in the first slot.
@isnad1 id=eq.0h6v.s11.d4cf57d0d473 from=translated src=- shape=e89514ac vocab=685f2a20
-/
theorem Place.residue_commutator_smul_left (P : Place k F) (c : k)
    (f g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k (c • f)) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k (c • f)) =
    c • ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_mul_assoc,
    map_smul, smul_sub]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator scales in the second slot.
@isnad1 id=eq.0h6v.s11.41190ac54ad3 from=translated src=- shape=067bd827 vocab=685f2a20
-/
theorem Place.residue_commutator_smul_right (P : Place k F) (c : k)
    (f g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k (c • g) -
      LinearMap.mulLeft k (c • g) ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k f) =
    c • ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_mul_assoc,
    map_smul, smul_sub]

/-- **Additivity of the residue in the first argument.**
@isnad1 id=eq.0h6v.s6.f60d0c5ee17f from=translated src=- shape=cb9f1c84 vocab=bb09c12a
-/
theorem Place.residue_add_left (P : Place k F) (f₁ f₂ g : F) :
    P.residue (f₁ + f₂) g = P.residue f₁ g + P.residue f₂ g := by
  have hφ := P.isTraceClass_residue_commutator f₁ g
  have hψ := P.isTraceClass_residue_commutator f₂ g
  haveI := hφ.finiteDimensional_range_comp hφ
  haveI := hφ.finiteDimensional_range_comp hψ
  haveI := hψ.finiteDimensional_range_comp hφ
  haveI := hψ.finiteDimensional_range_comp hψ
  rw [Place.residue, Place.residue, Place.residue,
    P.residue_commutator_add_left f₁ f₂ g]
  exact tateTrace_add_of_sq _ _

/-- **Additivity of the residue in the second argument.**
@isnad1 id=eq.0h6v.s6.1e4e2f26b877 from=translated src=- shape=d40c8de3 vocab=bb09c12a
-/
theorem Place.residue_add_right (P : Place k F) (f g₁ g₂ : F) :
    P.residue f (g₁ + g₂) = P.residue f g₁ + P.residue f g₂ := by
  have hφ := P.isTraceClass_residue_commutator f g₁
  have hψ := P.isTraceClass_residue_commutator f g₂
  haveI := hφ.finiteDimensional_range_comp hφ
  haveI := hφ.finiteDimensional_range_comp hψ
  haveI := hψ.finiteDimensional_range_comp hφ
  haveI := hψ.finiteDimensional_range_comp hψ
  rw [Place.residue, Place.residue, Place.residue,
    P.residue_commutator_add_right f g₁ g₂]
  exact tateTrace_add_of_sq _ _

/-- **The residue scales in the first argument.**
@isnad1 id=eq.0h6v.s6.d5f4ddeb9238 from=translated src=- shape=eeab6dbf vocab=77652c5f
-/
theorem Place.residue_smul_left (P : Place k F) (c : k) (f g : F) :
    P.residue (c • f) g = c * P.residue f g := by
  set C : Module.End k F :=
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)
    with hC
  have hφ := P.isTraceClass_residue_commutator f g
  rw [← hC] at hφ
  haveI : FiniteDimensional k (LinearMap.range ((C ^ 2 :
      Module.End k F))) := by
    have h2 : (C ^ 2 : Module.End k F) = C ∘ₗ C := by
      rw [pow_two]
      rfl
    rw [h2]
    exact hφ.finiteDimensional_range_comp hφ
  rw [Place.residue, Place.residue,
    P.residue_commutator_smul_left c f g, ← hC,
    tateTrace_smul (isTateCore_range_pow C 2)]

/-- **The residue scales in the second argument.**
@isnad1 id=eq.0h6v.s6.65dcd31f5dbd from=translated src=- shape=6b7cf740 vocab=77652c5f
-/
theorem Place.residue_smul_right (P : Place k F) (c : k) (f g : F) :
    P.residue f (c • g) = c * P.residue f g := by
  set C : Module.End k F :=
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)
    with hC
  have hφ := P.isTraceClass_residue_commutator f g
  rw [← hC] at hφ
  haveI : FiniteDimensional k (LinearMap.range ((C ^ 2 :
      Module.End k F))) := by
    have h2 : (C ^ 2 : Module.End k F) = C ∘ₗ C := by
      rw [pow_two]
      rfl
    rw [h2]
    exact hφ.finiteDimensional_range_comp hφ
  rw [Place.residue, Place.residue,
    P.residue_commutator_smul_right c f g, ← hC,
    tateTrace_smul (isTateCore_range_pow C 2)]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The valuation ring is closed under multiplication.
@isnad1 id=mem.2h5v.s8.2f5127760d3a from=translated src=- shape=0d435eed vocab=48a6fbed
-/
theorem Place.mul_mem_toSubmodule (P : Place k F) {a b : F}
    (ha : a ∈ P.toSubmodule) (hb : b ∈ P.toSubmodule) :
    a * b ∈ P.toSubmodule := by
  rw [Place.mem_toSubmodule_iff] at ha hb ⊢
  rw [Valuation.map_mul]
  calc P.val.valuation a * P.val.valuation b ≤ 1 * 1 :=
      mul_le_mul' ha hb
    _ = 1 := one_mul 1

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- **Vanishing for integral pairs** (Tate's property (R2)): when `f`
and `g` are both integral at `P`, the residue commutator kills the
valuation ring and lands in it, so it squares to zero.
@isnad1 id=eq.2h5v.s8.a735475f4ef6 from=translated src=- shape=d740cf4e vocab=959cf8e0
-/
theorem Place.residue_eq_zero_of_mem (P : Place k F) {f g : F}
    (hf : f ∈ P.toSubmodule) (hg : g ∈ P.toSubmodule) :
    P.residue f g = 0 := by
  set C : Module.End k F :=
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)
    with hC
  have happ : ∀ x : F,
      C x = P.proj (f * (g * x)) - g * P.proj (f * x) := by
    intro x
    rw [hC]
    rfl
  have hker : ∀ x ∈ P.toSubmodule, C x = 0 := by
    intro x hx
    rw [happ]
    have h1 : f * (g * x) ∈ P.toSubmodule :=
      P.mul_mem_toSubmodule hf (P.mul_mem_toSubmodule hg hx)
    have h2 : f * x ∈ P.toSubmodule := P.mul_mem_toSubmodule hf hx
    rw [P.proj_eq_self h1, P.proj_eq_self h2]
    ring
  have hrange : ∀ x : F, C x ∈ P.toSubmodule := by
    intro x
    rw [happ]
    exact Submodule.sub_mem _ (P.proj_mem _)
      (P.mul_mem_toSubmodule hg (P.proj_mem _))
  have hnil : IsNilpotent C := by
    refine ⟨2, ?_⟩
    have h2 : (C ^ 2 : Module.End k F) = C ∘ₗ C := by
      rw [pow_two]
      rfl
    rw [h2]
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    exact hker _ (hrange x)
  rw [Place.residue, ← hC]
  exact tateTrace_of_isNilpotent hnil

/-- The residue vanishes when the second argument is zero.
@isnad1 id=eq.0h4v.s6.9fa91f0a7c90 from=translated src=- shape=e246e503 vocab=7d5b3352
-/
theorem Place.residue_zero_right (P : Place k F) (f : F) :
    P.residue f 0 = 0 := by
  rw [← zero_smul k (0 : F), P.residue_smul_right, zero_mul]

section AdaptedProjection

variable (P : Place k F)

/-- The **principal-part space** at a place: the span of the negative
uniformizer powers.-/
noncomputable def Place.principalSpan : Submodule k F :=
  Submodule.span k (Set.range fun i : ℕ ↦ (P.pi : F) ^ (-(i : ℤ) - 1))

end AdaptedProjection

end ResidueCalculus

end Projection

end

end AclGeom
