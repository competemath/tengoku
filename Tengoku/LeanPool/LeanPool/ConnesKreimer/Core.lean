/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.ConnesKreimer.PowerSeriesLogMul

/-! Connes–Kreimer / Foissy (planar, R1) coproduct as a genuine Mathlib `Coalgebra` instance.
    Combinatorial core (List.Perm) proven below verbatim from `Coassoc.lean`; the Mathlib bridge
    lifts it to equality of linear maps. LOCAL — not part of the published godsil tree. -/

@[expose] public section

open scoped TensorProduct

namespace CK

/-- Planar rooted trees, represented by the forest of children below the root. -/
inductive RTree where
  | node : List RTree → RTree
deriving Inhabited

/-- A planar rooted forest is a list of planar rooted trees. -/
abbrev Forest := List RTree

/-- Formal sums of coproduct tensor monomials, represented by their forest pairs. -/
abbrev Tens := List (Forest × Forest)

/-- Product on formal tensor monomials, multiplying the two tensor legs by forest concatenation. -/
def tmul (x y : Tens) : Tens :=
  x.flatMap (fun (p, r) => y.map (fun (p', r') => (p ++ p', r ++ r')))

mutual
  /-- The Connes-Kreimer coproduct on one rooted tree, as a formal list of tensor terms. -/
  def coprodTree : RTree → Tens
    | .node F => ([RTree.node F], []) :: (coprodForest F).map (fun (p, r) => (p, [RTree.node r]))
  /-- The multiplicative extension of the coproduct from trees to forests. -/
  def coprodForest : Forest → Tens
    | []      => [([], [])]
    | t :: ts => tmul (coprodTree t) (coprodForest ts)
end

@[simp] theorem _root_.CK.tmul_unit_left (y : Tens) : tmul [([], [])] y = y := by simp [tmul]

@[simp] theorem _root_.CK.tmul_unit_right (x : Tens) : tmul x [([], [])] = x := by
  induction x with
  | nil => rfl
  | cons a xs ih => obtain ⟨p, r⟩ := a; simp [tmul, List.append_nil]

theorem _root_.CK.tmul_append_left (x₁ x₂ y : Tens) :
    tmul (x₁ ++ x₂) y = tmul x₁ y ++ tmul x₂ y := by simp [tmul, List.flatMap_append]

theorem _root_.CK.tmul_cons (p r : Forest) (xs y : Tens) :
    tmul ((p, r) :: xs) y =
      y.map (fun (p', r') => (p ++ p', r ++ r')) ++ tmul xs y := by
  simp [tmul]

theorem _root_.CK.tmul_assoc (x y z : Tens) : tmul (tmul x y) z = tmul x (tmul y z) := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨p, r⟩ := a
    rw [tmul_cons, tmul_append_left, ih, tmul_cons]
    congr 1
    simp [tmul, List.flatMap_map, List.map_flatMap, List.append_assoc, Function.comp_def]

theorem _root_.CK.coprodForest_append (F G : Forest) :
    coprodForest (F ++ G) = tmul (coprodForest F) (coprodForest G) := by
  induction F with
  | nil => simp [coprodForest, tmul_unit_left]
  | cons t ts ih =>
    change coprodForest (t :: (ts ++ G)) = _
    rw [show coprodForest (t :: (ts ++ G)) = tmul (coprodTree t) (coprodForest (ts ++ G)) from rfl,
        ih, ← tmul_assoc,
        show tmul (coprodTree t) (coprodForest ts) = coprodForest (t :: ts) from rfl]

open List in
theorem _root_.CK.perm_middle_swap {α} (A B C D : List α) :
    ((A ++ B) ++ (C ++ D)).Perm ((A ++ C) ++ (B ++ D)) := by
  calc (A ++ B) ++ (C ++ D)
      = A ++ ((B ++ C) ++ D) := by simp [List.append_assoc]
    _ ~ A ++ ((C ++ B) ++ D) := (List.perm_append_comm).append_right D |>.append_left A
    _ = (A ++ C) ++ (B ++ D) := by simp [List.append_assoc]

open List in
theorem _root_.CK.flatMap_append_distrib {α β} (l : List α) (X Y : α → List β) :
    (l.flatMap (fun a => X a ++ Y a)).Perm (l.flatMap X ++ l.flatMap Y) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left (X a ++ Y a) ih).trans ?_
    exact perm_middle_swap (X a) (Y a) (as.flatMap X) (as.flatMap Y)

open List in
theorem _root_.CK.flatMap_const_nil {α β} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  simp_all

theorem _root_.CK.flatMap_singleton_eq_map {α β} (g : α → β) (l : List α) :
    l.flatMap (fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, ih]

open List in
theorem _root_.CK.flatMap_comm {α β γ} (l1 : List α) (l2 : List β)
    (f : α → β → List γ) :
    (l1.flatMap (fun a => l2.flatMap (fun b => f a b))).Perm
    (l2.flatMap (fun b => l1.flatMap (fun a => f a b))) := by
  induction l1 with
  | nil => simp [flatMap_const_nil]
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_right _ (List.Perm.refl _)).trans ?_
    refine (List.Perm.append_left (l2.flatMap (fun b => f a b)) ih).trans ?_
    exact (flatMap_append_distrib l2 (fun b => f a b) (fun b => as.flatMap (fun a => f a b))).symm

theorem _root_.CK.Perm.flatMap_congr_right {α β} (l : List α) {f g : α → List β}
    (h : ∀ a, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons]; exact (h a).append ih

/-- Formal sums of triple tensor monomials, represented by forest triples. -/
abbrev _root_.CK.Tens3 := List (Forest × Forest × Forest)

/-- Expand the left tensor leg of every coproduct term. -/
def _root_.CK.coLeft (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest p).map (fun (a, b) => (a, b, r)))

/-- Expand the right tensor leg of every coproduct term. -/
def _root_.CK.coRight (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest r).map (fun (b, c) => (p, b, c)))

/-- Product on formal triple tensor monomials, multiplying all three tensor legs. -/
def _root_.CK.tmul3 (x y : Tens3) : Tens3 :=
  x.flatMap (fun (a, b, c) => y.map (fun (a', b', c') => (a ++ a', b ++ b', c ++ c')))

theorem _root_.CK.coLeft_tmul (x y : Tens) :
    (coLeft (tmul x y)).Perm (tmul3 (coLeft x) (coLeft y)) := by
  simp only [coLeft, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

theorem _root_.CK.coRight_tmul (x y : Tens) :
    (coRight (tmul x y)).Perm (tmul3 (coRight x) (coRight y)) := by
  simp only [coRight, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

theorem _root_.CK.coprodTree_node (F : Forest) :
    coprodTree (RTree.node F)
      = ([RTree.node F], []) :: (coprodForest F).map (fun pr => (pr.1, [RTree.node pr.2])) := rfl

theorem _root_.CK.coprodForest_single (t : RTree) : coprodForest [t] = coprodTree t := by
  change tmul (coprodTree t) (coprodForest []) = coprodTree t
  rw [show coprodForest ([] : Forest) = [([], [])] from rfl, tmul_unit_right]

theorem _root_.CK.tmul3_perm {a a' b b' : Tens3} (ha : a.Perm a') (hb : b.Perm b') :
    (tmul3 a b).Perm (tmul3 a' b') := by
  refine (ha.flatMap_right _).trans ?_
  exact Perm.flatMap_congr_right a' (fun _ => hb.map _)

mutual
  theorem _root_.CK.coassocTree (t : RTree) :
      (coLeft (coprodTree t)).Perm (coRight (coprodTree t)) := by
    cases t with
    | node F =>
      simp only [coLeft, coRight, coprodTree_node, coprodForest_single, List.map_cons,
        List.flatMap_cons, List.map_map, List.flatMap_map, Function.comp_def,
        show coprodForest ([] : Forest) = [([], [])] from rfl]
      refine List.Perm.cons _ ?_
      have hR2 :
          (List.flatMap (fun a => (a.fst, [RTree.node a.snd], []) ::
              List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
              (coprodForest F)).Perm
          (List.map (fun x => (x.fst, [RTree.node x.snd], [])) (coprodForest F)
            ++ List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
                (coprodForest a.snd)) (coprodForest F)) := by
        have h := flatMap_append_distrib (coprodForest F)
          (fun a => [(a.fst, [RTree.node a.snd], [])])
          (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
        rwa [flatMap_singleton_eq_map] at h
      have hkey :
          (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F)).Perm
          (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F)) := by
        have e1 :
            (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F))
            = (coLeft (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coLeft, List.map_flatMap, List.map_map, Function.comp_def]
        have e2 :
            (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F))
            = (coRight (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coRight, List.map_flatMap, List.map_map, Function.comp_def]
        rw [e1, e2]
        exact (coassocForest F).map _
      exact (List.Perm.append_left _ hkey).trans hR2.symm
  theorem _root_.CK.coassocForest (F : Forest) :
      (coLeft (coprodForest F)).Perm (coRight (coprodForest F)) := by
    cases F with
    | nil => exact .refl _
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl]
      refine (coLeft_tmul _ _).trans ?_
      refine (tmul3_perm (coassocTree t) (coassocForest ts)).trans ?_
      exact (coRight_tmul _ _).symm
end

/-! ### Mathlib bridge: lift the combinatorial coassoc to a `Coalgebra` instance. -/

variable (k : Type*) [CommRing k]

/-- Carrier: forests with k-coefficients (product = forest concatenation). -/
abbrev _root_.CK.H := MonoidAlgebra k (FreeMonoid RTree)

/-- Extensionality for linear maps out of `H k`, tested on the forest basis. A `Forest`-indexed
    repackaging of `MonoidAlgebra.lhom_ext'` (`Forest` and `FreeMonoid RTree` are definitionally
    but not reducibly equal, and `rw` needs the former). -/
theorem _root_.CK.lhom_ext {N : Type*} [AddCommMonoid N] [Module k N] ⦃φ ψ : H k →ₗ[k] N⦄
    (h : ∀ (f : Forest) (b : k),
      φ (MonoidAlgebra.single f b) = ψ (MonoidAlgebra.single f b)) : φ = ψ :=
  MonoidAlgebra.lhom_ext' fun f => LinearMap.ext fun b => h (FreeMonoid.toList f) b

/-- Pure 2-tensor of a cut `(p, r)`. -/
noncomputable def _root_.CK.e2 (pr : Forest × Forest) : H k ⊗[k] H k :=
  MonoidAlgebra.single pr.1 (1 : k) ⊗ₜ[k] MonoidAlgebra.single pr.2 (1 : k)

/-- Pure 3-tensor of an iterated cut `(a, b, c)`, associated to the right. -/
noncomputable def _root_.CK.e3 (t : Forest × Forest × Forest) : H k ⊗[k] (H k ⊗[k] H k) :=
  MonoidAlgebra.single t.1 (1 : k) ⊗ₜ[k]
    (MonoidAlgebra.single t.2.1 (1 : k) ⊗ₜ[k] MonoidAlgebra.single t.2.2 (1 : k))

/-- Δ on a basis forest. -/
noncomputable def _root_.CK.Δ₀ (f : Forest) : H k ⊗[k] H k := ((coprodForest f).map (e2 k)).sum

/-- E3 of a triple-tensor list. -/
noncomputable def _root_.CK.E3 (l : Tens3) : H k ⊗[k] (H k ⊗[k] H k) := (l.map (e3 k)).sum

/-- Comultiplication. -/
noncomputable def _root_.CK.Δ : H k →ₗ[k] H k ⊗[k] H k :=
  Finsupp.linearCombination k (Δ₀ k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.Δ_single (f : Forest) (b : k) :
    Δ k (MonoidAlgebra.single f b) = b • Δ₀ k f := by
  change Finsupp.linearCombination k (Δ₀ k) (Finsupp.single f b) = b • Δ₀ k f
  rw [Finsupp.linearCombination_single]

/-- E3 distributes over `flatMap`. -/
theorem _root_.CK.E3_flatMap (L : Tens) (g : Forest × Forest → Tens3) :
    E3 k (L.flatMap g) = (L.map (fun x => E3 k (g x))).sum := by
  unfold E3
  induction L with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- A linear map commutes with a `List.sum` of mapped terms. -/
theorem _root_.CK.linmap_list_sum {α} {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] (φ : M →ₗ[k] N) (l : List α) (h : α → M) :
    φ ((l.map h).sum) = (l.map (fun a => φ (h a))).sum := by
  rw [map_list_sum, List.map_map]; rfl

/-- The per-cut computation: `assoc ∘ rTensor Δ` on a pure 2-tensor `e2 (p,r)`
    equals `E3` of the left-leg refinement. This is the heart of the coassoc bridge. -/
theorem _root_.CK.elem_lemma (pr : Forest × Forest) :
    (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (e2 k pr))
      = E3 k ((coprodForest pr.1).map (fun ab => (ab.1, ab.2, pr.2))) := by
  obtain ⟨p, r⟩ := pr
  rw [e2, LinearMap.rTensor_tmul, Δ_single, one_smul, Δ₀]
  -- Ψ : y ↦ assoc (y ⊗ single r 1), linear; push through the list sum.
  let Ψ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ
      (TensorProduct.mk k (H k ⊗[k] H k) (H k)).flip (MonoidAlgebra.single r 1)
  have hΨ : (TensorProduct.assoc k (H k) (H k) (H k))
        ((((coprodForest p).map (e2 k)).sum) ⊗ₜ[k] MonoidAlgebra.single r (1 : k))
      = Ψ (((coprodForest p).map (e2 k)).sum) := rfl
  rw [hΨ, linmap_list_sum, E3, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  obtain ⟨a, b⟩ := ab
  simp only [Function.comp_def, Ψ, e2, e3, LinearMap.coe_comp, LinearEquiv.coe_coe,
    TensorProduct.mk_apply, LinearMap.flip_apply, TensorProduct.assoc_tmul]

/-- Right-leg analogue: `lTensor Δ` on `e2 (p,r)` equals `E3` of the right-leg refinement.
    No `assoc` needed — the tensor is already right-associated. -/
theorem _root_.CK.elem_lemma_R (pr : Forest × Forest) :
    LinearMap.lTensor (H k) (Δ k) (e2 k pr)
      = E3 k ((coprodForest pr.2).map (fun bc => (pr.1, bc.1, bc.2))) := by
  rw [e2, LinearMap.lTensor_tmul, Δ_single, one_smul, Δ₀]
  let Θ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    TensorProduct.mk k (H k) (H k ⊗[k] H k) (MonoidAlgebra.single pr.1 1)
  change Θ (((coprodForest pr.2).map (e2 k)).sum) = _
  rw [linmap_list_sum, E3, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bc _
  simp only [Function.comp_def, Θ, e2, e3, TensorProduct.mk_apply]

/-- LHS structural map on `Δ₀ f`. -/
theorem _root_.CK.lhs_core (f : Forest) :
    (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ₀ k f))
      = E3 k (coLeft (coprodForest f)) := by
  rw [Δ₀]
  let Φ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ LinearMap.rTensor (H k) (Δ k)
  have hΦ : (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (((coprodForest f).map (e2 k)).sum))
      = Φ (((coprodForest f).map (e2 k)).sum) := rfl
  rw [hΦ, linmap_list_sum, coLeft, E3_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  exact elem_lemma k pr

/-- RHS structural map on `Δ₀ f`. -/
theorem _root_.CK.rhs_core (f : Forest) :
    LinearMap.lTensor (H k) (Δ k) (Δ₀ k f) = E3 k (coRight (coprodForest f)) := by
  rw [Δ₀]
  rw [linmap_list_sum, coRight, E3_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  exact elem_lemma_R k pr

/-- The combinatorial coassoc, transported to `E3`. -/
theorem _root_.CK.perm_E3 (f : Forest) :
    E3 k (coLeft (coprodForest f)) = E3 k (coRight (coprodForest f)) :=
  (List.Perm.map (e3 k) (coassocForest f)).sum_eq

/-- **Coassociativity** as an equality of linear maps. -/
theorem _root_.CK.coassoc_map :
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ
        LinearMap.rTensor (H k) (Δ k) ∘ₗ Δ k
      = LinearMap.lTensor (H k) (Δ k) ∘ₗ Δ k := by
  apply CK.lhom_ext
  intro f b
  change (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ k (MonoidAlgebra.single f b)))
      = LinearMap.lTensor (H k) (Δ k) (Δ k (MonoidAlgebra.single f b))
  rw [Δ_single]
  simp only [map_smul]
  rw [lhs_core, rhs_core, perm_E3]

/-! ### Counit. -/

/-- Counit monoid hom: every generator ↦ 0, so a word ↦ `0 ^ len` = indicator of empty. -/
def _root_.CK.εmon : FreeMonoid RTree →* k := FreeMonoid.lift (fun _ => (0 : k))

@[simp] theorem _root_.CK.εmon_nil : εmon k ([] : Forest) = 1 := map_one _

@[simp] theorem _root_.CK.εmon_of (a : RTree) : εmon k (FreeMonoid.of a) = 0 := rfl

@[simp] theorem _root_.CK.εmon_cons (a : RTree) (l : Forest) : εmon k (a :: l) = 0 := by
  change εmon k (FreeMonoid.of a * FreeMonoid.ofList l) = 0
  rw [map_mul, εmon_of, zero_mul]

theorem _root_.CK.εmon_append (p p' : Forest) : εmon k (p ++ p') = εmon k p * εmon k p' := by
  induction p with
  | nil => simp
  | cons a as ih => simp

/-- Counit as an algebra hom, then linear. -/
noncomputable def _root_.CK.εalg : H k →ₐ[k] k :=
  MonoidAlgebra.lift k k (FreeMonoid RTree) (εmon k)

/-- The Connes-Kreimer counit as a linear map. -/
noncomputable def _root_.CK.ε : H k →ₗ[k] k := (εalg k).toLinearMap

theorem _root_.CK.ε_single (f : Forest) (b : k) :
    ε k (MonoidAlgebra.single f b) = b * εmon k f := by
  have h : εalg k (MonoidAlgebra.single (FreeMonoid.ofList f) b)
      = b * εmon k (FreeMonoid.ofList f) := by
    rw [εalg, MonoidAlgebra.lift_single, smul_eq_mul]
  exact h

/-- Scalar smul commutes with a `List.sum`. -/
theorem _root_.CK.smul_list_sum {M : Type*} [AddCommMonoid M] [Module k M] (c : k) (l : List M) :
    c • l.sum = (l.map (fun x => c • x)).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [smul_add, ih]

/-- Smul through a mapped `List.sum`. -/
theorem _root_.CK.smul_list_sum' {α M : Type*} [AddCommMonoid M] [Module k M]
    (c : k) (l : List α) (F : α → M) :
    c • (l.map F).sum = (l.map (fun x => c • F x)).sum := by
  rw [smul_list_sum, List.map_map]; rfl

/-- Pull a base-ring scalar out of the right tensor leg (avoids `CompatibleSMul`). -/
theorem _root_.CK.tmul_scalar_right (m : H k) (c : k) :
    m ⊗ₜ[k] c = c • (m ⊗ₜ[k] (1 : k)) := by
  conv_lhs => rw [show c = c • (1 : k) from by rw [smul_eq_mul, mul_one]]
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/-- Pull a base-ring scalar out of the left tensor leg. -/
theorem _root_.CK.tmul_scalar_left (c : k) (m : H k) :
    (c : k) ⊗ₜ[k] m = c • ((1 : k) ⊗ₜ[k] m) := by
  conv_lhs => rw [show c = c • (1 : k) from by rw [smul_eq_mul, mul_one]]
  rw [TensorProduct.smul_tmul']

/-- Generic map-over-`flatMap` `List.sum` distribution. -/
theorem _root_.CK.map_flatMap_sum {α β : Type*} {M : Type*} [AddCommMonoid M]
    (L : List α) (G : α → List β) (h : β → M) :
    ((L.flatMap G).map h).sum = (L.map (fun a => ((G a).map h).sum)).sum := by
  induction L with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-! The left-counit collapse: `ε` on the left leg selects the unique `([], f)` cut. -/
mutual
  theorem _root_.CK.collapseL_tree {M : Type*} [AddCommMonoid M] [Module k M]
      (t : RTree) (g : Forest → M) :
      ((coprodTree t).map (fun pr => εmon k pr.1 • g pr.2)).sum = g [t] := by
    cases t with
    | node F =>
      rw [coprodTree_node]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, εmon_cons,
        zero_smul, zero_add]
      exact collapseL_forest F (fun r => g [RTree.node r])
  theorem _root_.CK.collapseL_forest {M : Type*} [AddCommMonoid M] [Module k M]
      (f : Forest) (g : Forest → M) :
      ((coprodForest f).map (fun pr => εmon k pr.1 • g pr.2)).sum = g f := by
    cases f with
    | nil =>
      rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
      simp
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl, tmul,
          map_flatMap_sum]
      rw [show ((coprodTree t).map (fun pr =>
            (((coprodForest ts).map (fun pr' => (pr.1 ++ pr'.1, pr.2 ++ pr'.2))).map
              (fun q => εmon k q.1 • g q.2)).sum)).sum
          = ((coprodTree t).map (fun pr => εmon k pr.1 • g (pr.2 ++ ts))).sum from ?_]
      · exact collapseL_tree t (fun r => g (r ++ ts))
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pr _
        simp only [List.map_map, Function.comp_def]
        trans (εmon k pr.1 •
            ((coprodForest ts).map (fun x => εmon k x.1 • g (pr.2 ++ x.2))).sum)
        · rw [smul_list_sum']
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          rw [εmon_append k pr.1 x.1, mul_smul]
        · congr 1
          exact collapseL_forest ts (fun r => g (pr.2 ++ r))
end

/-! The right-counit collapse: `ε` on the right leg selects the unique `(f, [])` cut. -/
mutual
  theorem _root_.CK.collapseR_tree {M : Type*} [AddCommMonoid M] [Module k M]
      (t : RTree) (g : Forest → M) :
      ((coprodTree t).map (fun pr => εmon k pr.2 • g pr.1)).sum = g [t] := by
    cases t with
    | node F =>
      simp only [coprodTree_node, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        εmon_nil, εmon_cons, zero_smul, one_smul]
      simp_all
  theorem _root_.CK.collapseR_forest {M : Type*} [AddCommMonoid M] [Module k M]
      (f : Forest) (g : Forest → M) :
      ((coprodForest f).map (fun pr => εmon k pr.2 • g pr.1)).sum = g f := by
    cases f with
    | nil =>
      rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
      simp
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl, tmul,
          map_flatMap_sum]
      rw [show ((coprodTree t).map (fun pr =>
            (((coprodForest ts).map (fun pr' => (pr.1 ++ pr'.1, pr.2 ++ pr'.2))).map
              (fun q => εmon k q.2 • g q.1)).sum)).sum
          = ((coprodTree t).map (fun pr => εmon k pr.2 • g (pr.1 ++ ts))).sum from ?_]
      · exact collapseR_tree t (fun r => g (r ++ ts))
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pr _
        simp only [List.map_map, Function.comp_def]
        trans (εmon k pr.2 •
            ((coprodForest ts).map (fun x => εmon k x.2 • g (pr.1 ++ x.1))).sum)
        · rw [smul_list_sum']
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          rw [εmon_append k pr.2 x.2, mul_smul]
        · congr 1
          exact collapseR_forest ts (fun r => g (pr.1 ++ r))
end

/-- `(ε ⊗ id) ∘ Δ` on a basis forest gives `1 ⊗ single f 1`. -/
theorem _root_.CK.rTensor_ε_Δ₀ (f : Forest) :
    LinearMap.rTensor (H k) (ε k) (Δ₀ k f) = (1 : k) ⊗ₜ[k] MonoidAlgebra.single f 1 := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr => LinearMap.rTensor (H k) (ε k) (e2 k pr))).sum
        = ((coprodForest f).map (fun pr =>
            εmon k pr.1 • ((1 : k) ⊗ₜ[k] MonoidAlgebra.single pr.2 1))).sum from ?_]
  · exact collapseL_forest (k := k) f (fun r => (1 : k) ⊗ₜ[k] MonoidAlgebra.single r 1)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [e2, LinearMap.rTensor_tmul, ε_single, one_mul]
    apply tmul_scalar_left

theorem _root_.CK.single_smul_one (f : FreeMonoid RTree) (b : k) :
    MonoidAlgebra.single f b = b • MonoidAlgebra.single f 1 := by
  simp

noncomputable instance : CoalgebraStruct k (H k) where
  comul := Δ k
  counit := ε k

/-! ### Bialgebra: `Δ` and `ε` are algebra homs. -/

/-- `single` of a concatenation is the product (algebra structure of `H`). -/
theorem _root_.CK.single_append (p p' : Forest) :
    (MonoidAlgebra.single (p ++ p') (1 : k) : H k)
      = (MonoidAlgebra.single p 1 : H k) * (MonoidAlgebra.single p' 1 : H k) := by
  have h : (MonoidAlgebra.single (FreeMonoid.ofList p * FreeMonoid.ofList p') (1 : k) : H k)
      = (MonoidAlgebra.single (FreeMonoid.ofList p) (1 : k) : H k) *
        (MonoidAlgebra.single (FreeMonoid.ofList p') (1 : k) : H k) := by
    rw [MonoidAlgebra.single_mul_single, mul_one]
  exact h

/-- `e2` is multiplicative across leg-wise concatenation. -/
theorem _root_.CK.e2_mul (pr pr' : Forest × Forest) :
    e2 k (pr.1 ++ pr'.1, pr.2 ++ pr'.2) = e2 k pr * e2 k pr' := by
  simp only [e2, Algebra.TensorProduct.tmul_mul_tmul, single_append]

/-- Left-distribute a product over a `List.sum`. -/
theorem _root_.CK.mul_list_sum {M : Type*} [NonUnitalNonAssocSemiring M] (a : M) (L : List M) :
    a * L.sum = (L.map (fun b => a * b)).sum := by
  induction L with
  | nil => simp
  | cons b bs ih => simp [mul_add, ih]

/-- Product of two `List.sum`s is the double sum. -/
theorem _root_.CK.list_sum_mul_sum {M : Type*} [NonUnitalNonAssocSemiring M] (L1 L2 : List M) :
    L1.sum * L2.sum = (L1.flatMap (fun a => L2.map (fun b => a * b))).sum := by
  induction L1 with
  | nil => simp
  | cons a as ih =>
    rw [List.sum_cons, add_mul, ih, mul_list_sum, List.flatMap_cons, List.sum_append]

/-- `Δ₀` is multiplicative. -/
theorem _root_.CK.Δ₀_mul (F G : Forest) : Δ₀ k (F ++ G) = Δ₀ k F * Δ₀ k G := by
  rw [Δ₀, Δ₀, Δ₀, coprodForest_append, list_sum_mul_sum, tmul]
  simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, e2_mul]

/-- `Δ` is multiplicative on all of `H` (reduce to the forest basis, bilinearly). -/
theorem _root_.CK.Δ_mul (a b : H k) : Δ k (a * b) = Δ k a * Δ k b := by
  induction a using MonoidAlgebra.induction_on with
  | of F =>
    induction b using MonoidAlgebra.induction_on with
    | of G =>
      simp only [MonoidAlgebra.of_apply]
      change Δ k ((MonoidAlgebra.single (FreeMonoid.toList F) (1 : k) : H k) *
            (MonoidAlgebra.single (FreeMonoid.toList G) (1 : k) : H k))
          = Δ k (MonoidAlgebra.single (FreeMonoid.toList F) (1 : k) : H k) *
            Δ k (MonoidAlgebra.single (FreeMonoid.toList G) (1 : k) : H k)
      rw [← single_append, Δ_single, Δ_single, Δ_single, one_smul, one_smul, one_smul]
      exact Δ₀_mul k F G
    | add b1 b2 h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | smul r b hb => rw [mul_smul_comm, map_smul, map_smul, hb, mul_smul_comm]
  | add a1 a2 h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | smul r a ha => rw [smul_mul_assoc, map_smul, map_smul, ha, smul_mul_assoc]

/-- `Δ 1 = 1`. -/
theorem _root_.CK.Δ_one : Δ k (1 : H k) = 1 := by
  rw [show (1 : H k) = MonoidAlgebra.single (M := FreeMonoid RTree) ([] : Forest) (1 : k) from rfl,
      Δ_single, one_smul]
  rw [Δ₀, show coprodForest ([] : Forest) = [([], [])] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, e2]
  rfl

/-! ### Toward HopfAlgebra: node count (grading) and its conservation under cuts.
    Conservation `|p| + |r| = |f|` makes the antipode recursion well-founded
    (`r ≠ [] ⟹ |p| < |f|`). -/

mutual
  /-- Number of nodes in a rooted tree. -/
  def _root_.CK.sizeT : RTree → Nat
    | .node F => 1 + sizeF F
  /-- Number of nodes in a rooted forest. -/
  def _root_.CK.sizeF : Forest → Nat
    | []      => 0
    | t :: ts => sizeT t + sizeF ts
end

theorem _root_.CK.sizeF_append (F G : Forest) : sizeF (F ++ G) = sizeF F + sizeF G := by
  induction F with
  | nil => simp [sizeF]
  | cons t ts ih => simp only [List.cons_append, sizeF, ih]; ring

mutual
  theorem _root_.CK.size_consTree (t : RTree) :
      ∀ pr ∈ coprodTree t, sizeF pr.1 + sizeF pr.2 = sizeT t := by
    cases t with
    | node F =>
      intro pr hpr
      rw [coprodTree_node] at hpr
      simp only [List.mem_cons, List.mem_map] at hpr
      rcases hpr with h | ⟨q, hq, rfl⟩
      · subst h; simp [sizeF, sizeT]
      · simp only [sizeF, sizeT]
        have := size_consForest F q hq
        omega
  theorem _root_.CK.size_consForest (f : Forest) :
      ∀ pr ∈ coprodForest f, sizeF pr.1 + sizeF pr.2 = sizeF f := by
    cases f with
    | nil =>
      intro pr hpr
      simp only [show coprodForest ([] : Forest) = [([], [])] from rfl, List.mem_singleton] at hpr
      subst hpr; simp [sizeF]
    | cons t ts =>
      intro pr hpr
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          tmul] at hpr
      simp only [List.mem_flatMap, List.mem_map] at hpr
      obtain ⟨a, ha, b, hb, rfl⟩ := hpr
      have h1 := size_consTree t a ha
      have h2 := size_consForest ts b hb
      simp only [sizeF, sizeF_append]
      omega
end

theorem _root_.CK.sizeF_pos {f : Forest} (h : f ≠ []) : 0 < sizeF f := by
  cases f with
  | nil => exact absurd rfl h
  | cons t ts => cases t with | node F => simp [sizeF, sizeT]

/-- A forest as an `H`-basis element, with the index forced to `FreeMonoid RTree`
    via `ofList` (so it is always typed `H k`, even on the empty forest). -/
noncomputable def _root_.CK.sf (r : Forest) : H k := MonoidAlgebra.single (FreeMonoid.ofList r) 1

@[simp] theorem _root_.CK.sf_nil : sf k [] = 1 := by
  rw [sf, FreeMonoid.ofList_nil, ← MonoidAlgebra.one_def]

theorem _root_.CK.sf_append (a b : Forest) : sf k (a ++ b) = sf k a * sf k b := by
  rw [sf, sf, sf, MonoidAlgebra.single_mul_single, mul_one, FreeMonoid.ofList_append]

/-- The antipode on the forest basis, by well-founded recursion on node count.
    `S(∅) = 1`; `S(f) = -Σ_{(p,r) cut, r ≠ ∅} S(p)·r`. Recursion decreases since
    `|p| < |f|`. -/
noncomputable def _root_.CK.antipodeF : Forest → H k
  | [] => 1
  | (t :: ts) =>
    - (((coprodForest (t :: ts)).filter (fun pr => !pr.2.isEmpty)).attach.map
        (fun pr => antipodeF pr.val.1 * sf k pr.val.2)).sum
termination_by f => sizeF f
decreasing_by
  have hmem := pr.property
  rw [List.mem_filter] at hmem
  have hcons := size_consForest _ pr.val hmem.1
  have hr : pr.val.2 ≠ [] := by simpa [List.isEmpty_iff] using hmem.2
  have hpos := sizeF_pos hr
  have hlt : sizeF pr.val.1 < sizeF pr.val.1 + sizeF pr.val.2 := by omega
  simp_all

/-! ### Antipode as a linear map + the left convolution axiom (`S ⋆ id = η∘ε`). -/

/-- The antipode linear map obtained by extending `antipodeF` from the forest basis. -/
noncomputable def _root_.CK.antipode : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (antipodeF k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.antipode_single (f : Forest) (b : k) :
    antipode k (MonoidAlgebra.single f b) = b • antipodeF k f := by
  change Finsupp.linearCombination k (antipodeF k) (Finsupp.single f b) = b • antipodeF k f
  rw [Finsupp.linearCombination_single]

/-- `antipodeF` on a nonempty forest, as a plain (non-`attach`) sum. -/
theorem _root_.CK.antipodeF_cons (t : RTree) (ts : Forest) :
    antipodeF k (t :: ts)
      = - (((coprodForest (t :: ts)).filter (fun pr => !pr.2.isEmpty)).map
          (fun pr => antipodeF k pr.1 * sf k pr.2)).sum := by
  conv_lhs => rw [antipodeF]
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- `r ++ b` is nonempty when `r` is. -/
theorem _root_.CK.isEmpty_append_of_ne {r b : Forest} (h : r ≠ []) :
    (r ++ b).isEmpty = false := by
  simp_all

/-- Filtering cuts by "empty right leg" factorizes over `tmul`. -/
theorem _root_.CK.filter_emptyR_tmul (A B : Tens) :
    (tmul A B).filter (fun pr => pr.2.isEmpty)
      = tmul (A.filter (fun pr => pr.2.isEmpty)) (B.filter (fun pr => pr.2.isEmpty)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨p, r⟩ := a
    rcases r with _ | ⟨c, cs⟩
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_nil,
        ite_true, List.filter_map, Function.comp_def, List.nil_append]
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_cons,
        Bool.false_eq_true, ite_false, List.filter_map, Function.comp_def]
      simp_all

mutual
  /-- The unique empty-right cut of a tree `t` is `([t], [])`. -/
  theorem _root_.CK.coprodTree_filter_emptyR (t : RTree) :
      (coprodTree t).filter (fun pr => pr.2.isEmpty) = [([t], [])] := by
    cases t with
    | node F =>
      rw [coprodTree_node, List.filter_cons]
      simp only [List.isEmpty_nil, ite_true, List.filter_map, Function.comp_def]
      simp_all
  theorem _root_.CK.coprodForest_filter_emptyR (f : Forest) :
      (coprodForest f).filter (fun pr => pr.2.isEmpty) = [(f, [])] := by
    cases f with
    | nil => rfl
    | cons t ts =>
      have ht := coprodTree_filter_emptyR t
      have hts := coprodForest_filter_emptyR ts
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          filter_emptyR_tmul, ht, hts]
      simp [tmul]
end

/-- Filtering cuts by "empty left leg" factorizes over `tmul`. -/
theorem _root_.CK.filter_emptyL_tmul (A B : Tens) :
    (tmul A B).filter (fun pr => pr.1.isEmpty)
      = tmul (A.filter (fun pr => pr.1.isEmpty)) (B.filter (fun pr => pr.1.isEmpty)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨p, r⟩ := a
    rcases p with _ | ⟨c, cs⟩
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_nil,
        ite_true, List.filter_map, Function.comp_def, List.nil_append]
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_cons,
        Bool.false_eq_true, ite_false, List.filter_map, Function.comp_def]
      simp_all

mutual
  /-- The unique empty-left cut of a tree `t` is `([], [t])`. -/
  theorem _root_.CK.coprodTree_filter_emptyL (t : RTree) :
      (coprodTree t).filter (fun pr => pr.1.isEmpty) = [([], [t])] := by
    cases t with
    | node F =>
      rw [coprodTree_node, List.filter_cons]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.filter_map,
        Function.comp_def]
      rw [coprodForest_filter_emptyL F]
      rfl
  theorem _root_.CK.coprodForest_filter_emptyL (f : Forest) :
      (coprodForest f).filter (fun pr => pr.1.isEmpty) = [([], f)] := by
    cases f with
    | nil => rfl
    | cons t ts =>
      have ht := coprodTree_filter_emptyL t
      have hts := coprodForest_filter_emptyL ts
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          filter_emptyL_tmul, ht, hts]
      simp [tmul]
end

/-- Split a mapped `List.sum` by a boolean predicate. -/
theorem _root_.CK.map_sum_filter_split {α : Type*} (L : List α) (P : α → Bool)
    (g : α → H k) :
    (L.map g).sum
      = ((L.filter P).map g).sum + ((L.filter (fun x => !P x)).map g).sum := by
  rw [← List.sum_append, ← List.map_append]
  exact (List.Perm.map g (List.filter_append_perm P L).symm).sum_eq

/-- **Left convolution axiom** on a basis forest: `(S ⋆ id)(f) = ε(f)·1`. Near-definitional. -/
theorem _root_.CK.leftConvF (f : Forest) :
    ((coprodForest f).map (fun pr => antipodeF k pr.1 * sf k pr.2)).sum =
      εmon k f • (1 : H k) := by
  cases f with
  | nil =>
    rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [antipodeF, one_mul, sf_nil, εmon_nil, one_smul]
  | cons t ts =>
    rw [map_sum_filter_split (k := k) (L := coprodForest (t :: ts))
          (P := fun pr => pr.2.isEmpty)
          (g := fun pr => antipodeF k pr.1 * sf k pr.2),
        coprodForest_filter_emptyR]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sf_nil, mul_one]
    rw [εmon_cons, zero_smul, antipodeF_cons]
    abel

/-- `μ ∘ (S ⊗ id)` on a pure 2-tensor `e2 (p,r)` gives `S(p)·r`. -/
theorem _root_.CK.mul_rTensor_antipode_e2 (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (LinearMap.rTensor (H k) (antipode k) (e2 k pr))
      = antipodeF k pr.1 * sf k pr.2 := by
  rw [e2, LinearMap.rTensor_tmul, LinearMap.mul'_apply, antipode_single, one_smul]
  rfl

/-- `μ ∘ (S ⊗ id) ∘ Δ` on a basis forest equals `ε(f)·1` (left antipode identity). -/
theorem _root_.CK.rTensor_antipode_Δ₀ (f : Forest) :
    (LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k)) (Δ₀ k f)
      = εmon k f • (1 : H k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr =>
        (LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k)) (e2 k pr))).sum
      = ((coprodForest f).map (fun pr => antipodeF k pr.1 * sf k pr.2)).sum from ?_]
  · exact leftConvF k f
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [LinearMap.comp_apply]
    exact mul_rTensor_antipode_e2 k pr

/-! ### Mirror (right) antipode `S'`, satisfying `id ⋆ S' = η∘ε`. -/

/-- The right antipode by well-founded recursion on node count.
    `S'(∅) = 1`; `S'(f) = -Σ_{(p,r) cut, p ≠ ∅} p·S'(r)`. Decreases since `|r| < |f|`. -/
noncomputable def _root_.CK.antipodeF' : Forest → H k
  | [] => 1
  | (t :: ts) =>
    - (((coprodForest (t :: ts)).filter (fun pr => !pr.1.isEmpty)).attach.map
        (fun pr => sf k pr.val.1 * antipodeF' pr.val.2)).sum
termination_by f => sizeF f
decreasing_by
  have hmem := pr.property
  rw [List.mem_filter] at hmem
  have hcons := size_consForest _ pr.val hmem.1
  have hp : pr.val.1 ≠ [] := by simpa [List.isEmpty_iff] using hmem.2
  have hpos := sizeF_pos hp
  have hlt : sizeF pr.val.2 < sizeF pr.val.1 + sizeF pr.val.2 := by omega
  simp_all

theorem _root_.CK.antipodeF'_cons (t : RTree) (ts : Forest) :
    antipodeF' k (t :: ts)
      = - (((coprodForest (t :: ts)).filter (fun pr => !pr.1.isEmpty)).map
          (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum := by
  conv_lhs => rw [antipodeF']
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- Right convolution `id ⋆ S'` on a basis forest equals `ε(f)·1`. Near-definitional. -/
theorem _root_.CK.rightConvF' (f : Forest) :
    ((coprodForest f).map (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum =
      εmon k f • (1 : H k) := by
  cases f with
  | nil =>
    rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [antipodeF', mul_one, sf_nil, εmon_nil, one_smul]
  | cons t ts =>
    rw [map_sum_filter_split (k := k) (L := coprodForest (t :: ts))
          (P := fun pr => pr.1.isEmpty)
          (g := fun pr => sf k pr.1 * antipodeF' k pr.2),
        coprodForest_filter_emptyL]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sf_nil, one_mul]
    rw [εmon_cons, zero_smul, antipodeF'_cons]
    abel

/-- The mirrored antipode candidate used to prove the right convolution identity. -/
noncomputable def _root_.CK.antipode' : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (antipodeF' k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.antipode'_single (f : Forest) (b : k) :
    antipode' k (MonoidAlgebra.single f b) = b • antipodeF' k f := by
  change Finsupp.linearCombination k (antipodeF' k) (Finsupp.single f b) = b • antipodeF' k f
  rw [Finsupp.linearCombination_single]

theorem _root_.CK.mul_lTensor_antipode'_e2 (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (LinearMap.lTensor (H k) (antipode' k) (e2 k pr))
      = sf k pr.1 * antipodeF' k pr.2 := by
  rw [e2, LinearMap.lTensor_tmul, LinearMap.mul'_apply, antipode'_single, one_smul]
  rfl

/-- `μ ∘ (id ⊗ S') ∘ Δ` on a basis forest equals `ε(f)·1` (right antipode identity). -/
theorem _root_.CK.lTensor_antipode'_Δ₀ (f : Forest) :
    (LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k)) (Δ₀ k f)
      = εmon k f • (1 : H k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr =>
        (LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k)) (e2 k pr))).sum
      = ((coprodForest f).map (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum from ?_]
  · exact rightConvF' k f
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [LinearMap.comp_apply]
    exact mul_lTensor_antipode'_e2 k pr

/-- Left antipode identity as a linear-map equality (the Hopf left axiom). -/
theorem _root_.CK.leftAntipode_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  apply CK.lhom_ext
  intro f b
  change LinearMap.mul' k (H k)
        (LinearMap.rTensor (H k) (antipode k) (Δ k (MonoidAlgebra.single f b)))
      = Algebra.linearMap k (H k) (ε k (MonoidAlgebra.single f b))
  rw [Δ_single, map_smul,
      map_smul,
      show LinearMap.mul' k (H k) (LinearMap.rTensor (H k) (antipode k) (Δ₀ k f))
        = εmon k f • (1 : H k) from rTensor_antipode_Δ₀ k f,
      ε_single, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, mul_smul]

/-- Right antipode identity for `S'` as a linear-map equality. -/
theorem _root_.CK.rightAntipode'_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  apply CK.lhom_ext
  intro f b
  change LinearMap.mul' k (H k)
        (LinearMap.lTensor (H k) (antipode' k) (Δ k (MonoidAlgebra.single f b)))
      = Algebra.linearMap k (H k) (ε k (MonoidAlgebra.single f b))
  rw [Δ_single, map_smul,
      map_smul,
      show LinearMap.mul' k (H k) (LinearMap.lTensor (H k) (antipode' k) (Δ₀ k f))
        = εmon k f • (1 : H k) from lTensor_antipode'_Δ₀ k f,
      ε_single, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, mul_smul]

/-! ### Adams operators `Ψₙ = id^{⋆n}` and the antipode as `Ψ₋₁`.

    The convolution ring `WithConv (H k →ₗ[k] H k)` (Mathlib `LinearMap.convRing`) turns the
    identity into a ring element whose convolution powers are the Adams (Hopf-power) operators.
    `Ψ₀ = u∘ε` (the convolution unit), `Ψ₁ = id`, the semigroup law `Ψₘ ⋆ Ψₙ = Ψₘ₊ₙ`, and the
    identity is a convolution UNIT whose inverse is the antipode — i.e. `Ψ₋₁ = S`. This is the
    first combinatorial-Hopf Adams-operator layer in any ITP (Aguiar–Lauve theory; the Eulerian
    idempotent `e⁽¹⁾ = log_⋆ id` is the heavier next step, needing connected-graded nilpotence). -/

/-! ### Part 2 — local nilpotency of `J = id − u∘ε` (the connected-graded engine for `log_⋆`).

    `J` kills the empty forest and is the identity on nonempty ones. Its convolution powers
    `J^{⋆k}` vanish on every basis forest of fewer than `k` nodes (`Jc_pow_ofConv_sf_eq_zero`):
    each of the `k` convolution factors must absorb at least one node, so `k` nodes are needed.
    Hence the series `log_⋆(id) = Σ_{k≥1} ((-1)^{k+1}/k)·J^{⋆k}` is finite in each degree — the
    connected-graded local nilpotency on which the Aguiar–Lauve Eulerian spectrum rests. -/

/-- `Δ` on a basis forest, packaged for `sf`. -/
theorem _root_.CK.Δ_sf (f : Forest) : Δ k (sf k f) = Δ₀ k f := by
  change Finsupp.linearCombination k (Δ₀ k) (Finsupp.single f (1 : k)) = Δ₀ k f
  rw [Finsupp.linearCombination_single, one_smul]

/-- `ε` on a basis forest: the counit of `sf f` is `εmon f`. -/
theorem _root_.CK.ε_sf (p : Forest) : ε k (sf k p) = εmon k p := by
  have h := ε_single k p 1
  rw [one_mul] at h
  exact h

/-- `μ ∘ (F ⊗ G)` on a pure cut-tensor `e2 (p,r)` is `F(p)·G(r)`. -/
theorem _root_.CK.mul_map_e2 (F G : H k →ₗ[k] H k) (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (TensorProduct.map F G (e2 k pr))
      = F (sf k pr.1) * G (sf k pr.2) := by
  obtain ⟨p, r⟩ := pr
  rw [e2, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

/-- `comul` on a basis forest equals the combinatorial `Δ₀`. -/
theorem _root_.CK.comul_sf (f : Forest) :
    (Coalgebra.comul (R := k) (A := H k)) (sf k f) = Δ₀ k f := Δ_sf k f

/-- **Convolution-on-basis engine.** `(F ⋆ G)` on a basis forest is the sum over cuts:
    `(F ⋆ G)(f) = Σ_{(p,r) ∈ coprodForest f} F(p)·G(r)`. Reusable for all of Part 2. -/
theorem _root_.CK.conv_ofConv_sf (F G : H k →ₗ[k] H k) (f : Forest) :
    (WithConv.toConv F * WithConv.toConv G).ofConv (sf k f)
      = ((coprodForest f).map (fun pr => F (sf k pr.1) * G (sf k pr.2))).sum := by
  rw [LinearMap.convMul_def]
  change LinearMap.mul' k (H k) (TensorProduct.map F G (Coalgebra.comul (R := k) (sf k f))) = _
  rw [comul_sf, Δ₀,
      show LinearMap.mul' k (H k) (TensorProduct.map F G (((coprodForest f).map (e2 k)).sum))
        = (LinearMap.mul' k (H k) ∘ₗ TensorProduct.map F G) (((coprodForest f).map (e2 k)).sum)
        from rfl,
      linmap_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  rw [LinearMap.comp_apply]
  exact mul_map_e2 k F G pr

/-! ### The Adams eigenvalue on primitives: `Ψₙ(x) = n·x` for primitive `x`.

    The first piece of the Aguiar–Lauve spectrum, valid on ANY connected graded bialgebra (no
    commutativity needed): the primitives are the eigenspace of every Adams operator `Ψₙ` with
    eigenvalue `n`. Proof is at the element level (not the basis): on a primitive `x`, the recursion
    `Ψₙ₊₁ = id ⋆ Ψₙ` and `Δx = x⊗1 + 1⊗x` give `Ψₙ₊₁(x) = x + Ψₙ(x)`, and `Ψₙ` fixes the unit. -/

/-- A primitive element: `Δx = x⊗1 + 1⊗x`. -/
def _root_.CK.IsPrimitive (x : H k) : Prop := Δ k x = x ⊗ₜ[k] (1 : H k) + (1 : H k) ⊗ₜ[k] x

/-- Convolution at the element level: `(F ⋆ G)(x) = μ((F⊗G)(Δx))`. -/
theorem _root_.CK.conv_apply (F G : H k →ₗ[k] H k) (x : H k) :
    (WithConv.toConv F * WithConv.toConv G).ofConv x
      = LinearMap.mul' k (H k) (TensorProduct.map F G (Δ k x)) := by
  rw [LinearMap.convMul_def]; rfl

/-- `Δ(1) = 1⊗1` (the unit is grouplike), in pure-tensor form. -/
theorem _root_.CK.Δ_one_tmul : Δ k (1 : H k) = (1 : H k) ⊗ₜ[k] (1 : H k) := by
  rw [Δ_one, Algebra.TensorProduct.one_def]

/-! ### The first Eulerian idempotent `e⁽¹⁾ = log_⋆(id)` as a linear map.

    Over a `ℚ`-algebra the series `log_⋆(id) = Σ_{k≥1} ((-1)^{k+1}/k)·J^{⋆k}` is, by the local
    nilpotency above, finite on each basis forest (only `k ≤ |f|` contribute). We define `e⁽¹⁾`
    by that finite per-degree sum, mirroring how `Δ` and the antipode are defined on the basis.
    `e⁽¹⁾` kills the unit and fixes primitives (eigenvalue `1`) — the connected-graded projector
    onto primitives that begins the Aguiar–Lauve spectral decomposition. -/

variable [Algebra ℚ k]

/-- Coefficient `(-1)^{j+1}/j` of the convolution-log series, pushed into `k`. `j = 0 ↦ 0`. -/
noncomputable def _root_.CK.eulerCoef (j : ℕ) : k := algebraMap ℚ k ((-1) ^ (j + 1) / (j : ℚ))

@[simp] theorem _root_.CK.eulerCoef_zero : eulerCoef k 0 = 0 := by
  simp [eulerCoef]

@[simp] theorem _root_.CK.eulerCoef_one : eulerCoef k 1 = 1 := by
  simp [eulerCoef]

/-! ### `e⁽¹⁾` fixes every primitive (Phase 1: the element-level primitive facts).
    For primitive `x`: `ε(x)=0`, `J(x)=x`, and `J^{⋆k}(x)=0` for `k ≥ 2` (each higher factor must
    absorb the unit, which `J` kills). These feed the operator identity in Phase 2. -/

/-! ### `e⁽¹⁾` fixes every primitive (Phase 2: assembling the operator identity).
    `e⁽¹⁾` agrees on degree-`≤N` elements with the finite truncation `Σ_{j≤N} c_j J^{⋆j}` (extra
    terms vanish by nilpotency); on a primitive only the `j=1` term survives, giving `e⁽¹⁾(x)=x`. -/

/-- Bridge: a `List.range` map-sum equals the corresponding `Finset.range` sum. -/
theorem _root_.CK.list_range_sum_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    ((List.range m).map g).sum = ∑ j ∈ Finset.range m, g j := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

omit [Algebra ℚ k] in
/-- A linear endomorphism of `H` is the basis-sum of its values on the singletons (proved by
    `exact`, sidestepping the `MonoidAlgebra`/`Finsupp` syntactic wall in `rw`). -/
theorem _root_.CK.lmap_eq_sum (g : H k →ₗ[k] H k) (y : H k) :
    g y = y.coeff.sum (fun a b => g (MonoidAlgebra.single a b)) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single y]
  exact map_finsuppSum g y.coeff MonoidAlgebra.single

/-! ### A2 — the commutative quotient `H_ab = H / ⟨ab − ba⟩`
    (Foissy's planar → commutative map).

    Abelianizing the (forest) product turns the planar Hopf algebra into a commutative one. This is
    the algebra step (S1): the quotient ring `RingQuot` by the commutator relation, shown
    commutative.
    The coproduct, counit and antipode descend in the following stones, giving the classical
    (commutative) Connes–Kreimer / Butcher Hopf algebra, where the Eulerian idempotents become
    genuine orthogonal idempotents. -/

/-- The commutator relation `x·y ∼ y·x` on `H`. -/
inductive _root_.CK.commRel : H k → H k → Prop
  | mul (x y : H k) : commRel (x * y) (y * x)

/-- The commutative quotient `H_ab = H / ⟨ab − ba⟩`. -/
abbrev _root_.CK.Hab : Type _ := RingQuot (commRel k)

/-- The quotient algebra map `π : H → H_ab`. -/
noncomputable def _root_.CK.π : H k →ₐ[k] Hab k := RingQuot.mkAlgHom k (commRel k)

/-- `H_ab` is commutative: the relation forces `π(x)·π(y) = π(y)·x`. -/
noncomputable instance : CommRing (Hab k) where
  __ := (inferInstance : Ring (RingQuot (commRel k)))
  mul_comm a b := by
    obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (commRel k) a
    obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k (commRel k) b
    rw [← map_mul, ← map_mul]
    exact RingQuot.mkAlgHom_rel k (commRel.mul x y)

omit [Algebra ℚ k] in
theorem _root_.CK.π_surjective : Function.Surjective (π k) :=
  RingQuot.mkAlgHom_surjective k (commRel k)

omit [Algebra ℚ k] in
theorem _root_.CK.π_mul_comm (x y : H k) : π k (x * y) = π k (y * x) :=
  RingQuot.mkAlgHom_rel k (commRel.mul x y)

/-! #### S2 — the coproduct descends to `Delta_ab : H_ab → H_ab ⊗ H_ab`. -/

/-- `Δ` as an algebra homomorphism (the bialgebra coproduct), from `Δ_one` and `Δ_mul`. -/
noncomputable def _root_.CK.ΔAlg : H k →ₐ[k] H k ⊗[k] H k :=
  AlgHom.ofLinearMap (Δ k) (Δ_one k) (Δ_mul k)

omit [Algebra ℚ k] in
/-- `(π⊗π)∘Δ` respects the commutator relation, since `H_ab ⊗ H_ab` is commutative. -/
theorem _root_.CK.ΔAlg_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    (Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k) a
      = (Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k) b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended coproduct `Delta_ab : H_ab → H_ab ⊗ H_ab`. -/
noncomputable def _root_.CK.Δab : Hab k →ₐ[k] Hab k ⊗[k] Hab k :=
  RingQuot.liftAlgHom k
    ⟨(Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k), ΔAlg_resp_commRel k⟩

omit [Algebra ℚ k] in
/-- The descent square commutes: `Delta_ab ∘ π = (π⊗π) ∘ Δ`. -/
theorem _root_.CK.Δab_π (x : H k) :
    Δab k (π k x) = Algebra.TensorProduct.map (π k) (π k) (ΔAlg k x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (ΔAlg_resp_commRel k) x

/-! #### S3 — the counit descends to `epsilon_ab : H_ab → k`. -/

omit [Algebra ℚ k] in
/-- `ε` respects the commutator relation (`k` is commutative). -/
theorem _root_.CK.εalg_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    εalg k a = εalg k b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended counit `epsilon_ab : H_ab → k`. -/
noncomputable def _root_.CK.εab : Hab k →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨εalg k, εalg_resp_commRel k⟩

omit [Algebra ℚ k] in
theorem _root_.CK.εab_π (x : H k) : εab k (π k x) = εalg k x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (εalg_resp_commRel k) x

/-! #### S4 — `H_ab` is a coalgebra (coassoc + counit laws descend through `π`). -/

omit [Algebra ℚ k] in
/-- Extensionality on `H_ab`: a linear map out of `H_ab` is determined by its values on `π`. -/
theorem _root_.CK.Hab_lhom_ext {M : Type*} [AddCommMonoid M] [Module k M]
    {g₁ g₂ : Hab k →ₗ[k] M} (h : ∀ x : H k, g₁ (π k x) = g₂ (π k x)) :
    g₁ = g₂ := by
  ext u
  obtain ⟨x, rfl⟩ := π_surjective k u
  exact h x

omit [Algebra ℚ k] in
/-- `ε` (right) counit naturality: `(epsilon_ab⊗id)∘(π⊗π) = ε⊗π`. -/
theorem _root_.CK.εab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (εab k).toLinearMap) ∘ₗ
        (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (ε k) (π k).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
      LinearMap.rTensor_tmul,
      TensorProduct.map_tmul]
  change εab k (π k a) ⊗ₜ[k] π k b = ε k a ⊗ₜ[k] π k b
  rw [εab_π]; rfl

omit [Algebra ℚ k] in
/-- `ε` (left) counit naturality: `(id⊗epsilon_ab)∘(π⊗π) = π⊗ε`. -/
theorem _root_.CK.εab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (εab k).toLinearMap) ∘ₗ
        (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (π k).toLinearMap (ε k) := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
      LinearMap.lTensor_tmul,
      TensorProduct.map_tmul]
  change π k a ⊗ₜ[k] εab k (π k b) = π k a ⊗ₜ[k] ε k b
  rw [εab_π]; rfl

omit [Algebra ℚ k] in
/-- `Delta_ab ∘ π = (π⊗π) ∘ Δ` in purely linear (TensorProduct.map) form. -/
theorem _root_.CK.Δab_π' (x : H k) :
    Δab k (π k x)
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap (Δ k x) := by
  have h : (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap := by
    apply TensorProduct.ext'; simp_all
  rw [Δab_π, ← AlgHom.toLinearMap_apply, h]
  rfl

omit [Algebra ℚ k] in
/-- `Delta_ab ∘ π` in `.toLinearMap` form (for use inside compositions). -/
theorem _root_.CK.Δab_tl_π (x : H k) :
    (Δab k).toLinearMap (π k x)
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap (Δ k x) := by
  rw [AlgHom.toLinearMap_apply, Δab_π']

omit [Algebra ℚ k] in
/-- Coproduct (right) naturality for the descent:
    `(Delta_ab⊗id)∘(π⊗π) = ((π⊗π)⊗π)∘(Δ⊗id)`. -/
theorem _root_.CK.Δab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (Δab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map
          (TensorProduct.map (π k).toLinearMap (π k).toLinearMap) (π k).toLinearMap
          ∘ₗ LinearMap.rTensor (H k) (Δ k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, Δab_π']

omit [Algebra ℚ k] in
/-- Coproduct (left) naturality for the descent:
    `(id⊗Delta_ab)∘(π⊗π) = (π⊗(π⊗π))∘(id⊗Δ)`. -/
theorem _root_.CK.Δab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (Δab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap
          (TensorProduct.map (π k).toLinearMap (π k).toLinearMap)
          ∘ₗ LinearMap.lTensor (H k) (Δ k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, Δab_π']

/-- `H_ab` is a coalgebra (the commutative Connes–Kreimer coalgebra). -/
noncomputable instance : CoalgebraStruct k (Hab k) where
  comul := (Δab k).toLinearMap
  counit := (εab k).toLinearMap

/-! ### S5 — `H_ab` is a Bialgebra.
    `Δab`, `εab` are algebra homs by construction, so the four `Bialgebra.mk'`
    compatibilities are just `map_one`/`map_mul` (cf. planar `instCKBialg`, which
    needed a separate `Δ_mul` because there `Δ` was not yet packaged as an AlgHom). -/

/-! #### S6 — the antipode descends to `S_ab : H_ab → H_ab`, giving `HopfAlgebra k (H_ab)`.

`S = antipode k` is an algebra anti-homomorphism; composing with
`π` into the COMMUTATIVE quotient `H_ab` turns it into a genuine algebra hom, so it lifts
through `RingQuot`. The two antipode axioms then descend through `π` exactly like
coassociativity in S4. -/

omit [Algebra ℚ k] in
/-- `mu_ab ∘ (π⊗π) = π ∘ μ` (multiplication naturality, `π` an algebra hom). -/
theorem _root_.CK.mul'_π :
    LinearMap.mul' k (Hab k) ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = (π k).toLinearMap ∘ₗ LinearMap.mul' k (H k) := by
  apply TensorProduct.ext'
  simp_all

/-! #### Toward the Eulerian-idempotent payoff — Adams operators on `H_ab`.

On the COMMUTATIVE `H_ab` the Eulerian idempotents `e⁽ⁱ⁾` become orthogonal idempotents
(Patras/Loday), so `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` HOLDS (unlike the planar non-idempotency of D1). The
principled route is via the Adams operators `Ψⁿ`: on a commutative Hopf algebra each `Ψⁿ` is an
algebra morphism, whence `Ψᵖ∘Ψq = Ψ^{pq}`, whence the `e⁽ⁱ⁾` are the orthogonal eigen-projectors.

Brick 1 (no commutativity yet): the Adams operators on `H_ab`, and their naturality through `π`
(`Ψⁿ_ab ∘ π = π ∘ Ψⁿ`), which both defines `Ψⁿ_ab` and ties it to the planar `Ψⁿ`. -/

omit [Algebra ℚ k] in
/-- Element-level convolution on `H_ab`: `(F⋆G)(x) = mu_ab((F⊗G)(Delta_ab x))`. -/
theorem _root_.CK.conv_apply_ab (F G : Hab k →ₗ[k] Hab k) (x : Hab k) :
    (WithConv.toConv F * WithConv.toConv G).ofConv x
      = LinearMap.mul' k (Hab k) (TensorProduct.map F G ((Δab k).toLinearMap x)) := by
  rw [LinearMap.convMul_def]; rfl

/-! Brick 2 (commutativity enters): each Adams operator `Ψⁿ` is an ALGEBRA morphism on the
    commutative `H_ab`. We package `Ψⁿ` as an `AlgHom` built by composition:
    `Ψⁿ⁺¹ = mu_ab∘(id⊗Ψⁿ)∘Delta_ab`. This is a composite of the algebra homs
    `Delta_ab`, `id⊗Ψⁿ`, and `mu_ab`, and the multiplication is an algebra hom precisely
    because `H_ab` is commutative. -/

/-- `Ψⁿ` packaged as an algebra hom on the commutative `H_ab` (`Ψ₀ = u∘ε`,
    `Ψⁿ⁺¹ = mu_ab ∘ (id ⊗ Ψⁿ) ∘ Delta_ab`). -/
noncomputable def _root_.CK.adamsAbHom : ℕ → (Hab k →ₐ[k] Hab k)
  | 0 => (Algebra.ofId k (Hab k)).comp (εab k)
  | (n + 1) => (Algebra.TensorProduct.lmul' k).comp
      ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom n)).comp (Δab k))

/-! Brick 3: the Adams composition law `Ψᵖ ∘ Ψq = Ψ^{pq}`. Post-composition by an algebra hom
    distributes over convolution (`LinearMap.algHom_comp_convMul_distrib`), so an algebra-hom
    `φ` post-composed with `Ψᵖ = id^{⋆p}` gives `(φ ∘ id)^{⋆p} = (toConv φ)^p`.
    Taking `φ = Ψq` gives `Ψq ∘ Ψᵖ = (Ψq)^{⋆p} = id^{⋆qp} = Ψ^{qp}`. -/

/-! Brick 4 — toward `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` on the commutative `H_ab`, via the
finite-difference engine.

    The route AVOIDS the full Eulerian decomposition / Vandermonde inversion. The point:
    if `v` is an Adams eigenvector with `Ψⁱ(v) = i·v` for all `i`, then expanding
    `J^{⋆j} = (id − u∘ε)^{⋆j}` into Adams operators and applying to `v` collapses
    each `J^{⋆j}(v)` to a scalar multiple of `v` by the finite-difference identity below.
    Hence `e⁽¹⁾` is the identity on its own image. -/

/-- **Finite-difference engine**: the `j`-th finite difference of the identity sequence `i ↦ i`,
    `∑ᵢ (-1)^{j-i} C(j,i)·i = δ_{j,1}`. This collapses the convolution-log of an
    Adams eigenvector to its weight-1 component, which is the combinatorial heart of the
    Eulerian idempotency on `H_ab`. -/
theorem _root_.CK.alternating_choose_weighted (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), ((-1 : ℤ) ^ (j - i) * (j.choose i) * i)
      = if j = 1 then 1 else 0 := by
  rcases j with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    have hinner : ∀ i ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ (n + 1 - (i + 1)) * ((n + 1).choose (i + 1)) * ((i + 1 : ℕ) : ℤ))
          = (n + 1 : ℤ) * ((-1 : ℤ) ^ (n - i) * (n.choose i)) := by
      intro i _
      have hc : (((n + 1).choose (i + 1) : ℤ)) * ((i + 1 : ℕ) : ℤ)
          = (n + 1 : ℤ) * (n.choose i) := by
        exact_mod_cast (Nat.add_one_mul_choose_eq n i).symm
      rw [show n + 1 - (i + 1) = n - i from by omega, mul_assoc, hc]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - i) * (n.choose i))
        = (0 : ℤ) ^ n := by
      have hap := add_pow (1 : ℤ) (-1) n
      simp_all
    simp only [Nat.cast_zero, mul_zero, add_zero, Nat.sub_zero, hsum]
    rcases n with _ | m
    · simp
    · simp [pow_succ]

/-! Brick B (binomial expansion) — `J_ab^{⋆j}` into Adams operators on the commutative `H_ab`.
    Toward `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾`: expand the convolution-log's `J^{⋆j}` into the Adams
    basis so that, on an Adams eigenvector, `alternating_choose_weighted` collapses it. -/

-- **Brick B.** On the commutative `H_ab`, the convolution power
-- `J_ab^{⋆j} = (id − u∘ε)^{⋆j}` expands into Adams operators:
-- `(J_ab^j)(x) = Σ_{i=0}^{j} (-1)^{j-i} C(j,i) · Ψⁱ(x)`. Pure ring
-- algebra in the commutative convolution ring (`convCommRing`); no nilpotency needed. The
-- `maxHeartbeats 0` is the documented WithConv `whnf` cost. The proof itself is elementary
-- (`Commute.add_pow` on `id + (-1)`, then `ofConv` linearity per term via the `key` scalar bridge).

/-! Brick A scaffolding — `J^{⋆j}` naturality through `π` and per-degree nilpotency
on `H_ab`. -/

-- **Planar Brick B.** Same binomial expansion on the planar `H` (the convolution ring is
-- non-commutative, but `id` and `1` commute, so `Commute.add_pow` still applies). `maxHeartbeats 0`
-- for the WithConv `whnf` cost. Used to transport `J^{⋆j}` through `π`.

/-! Brick A core — the Φ_p ring-hom step: post-composition by `Ψᵖ` (`adamsAb p`, an
algebra hom) is a ⋆-ring hom, sending `J_ab ↦ Yᵖ − 1` (`Y = toConv id_ab`). This is
`Ψᵖ ∘ e = log(Yᵖ)`. -/

-- General: an algebra hom `φ` post-composed with a convolution power `g^{⋆j}` is the `j`-th
-- convolution power of `φ ∘ g`:
-- `φ ∘ (g^j).ofConv = ((toConv(φ ∘ g.ofConv))^j).ofConv`. Mirrors
-- `algHom_comp_adamsAb` (the case `g = toConv id`); pure `algHom_comp_convMul_distrib` induction.

/-! Brick A step 2 — eval₂ plumbing: bridge the PowerSeries coeff identity (`coeff_logTrunc_pow`)
    to the convolution sums via `eval₂ (X ↦ J_ab)`, then kill high powers with nilpotency. -/

/-- The Eulerian coefficient `(-1)^{j+1}/j` equals the `j`-th coefficient of the formal `log`. -/
theorem _root_.CK.eulerCoef_eq_coeff_log (j : ℕ) :
    eulerCoef k j = PowerSeries.coeff j (PowerSeries.log k) := by
  rw [eulerCoef, PowerSeries.coeff_log]
  simp_all

/-! Brick C — the finite-difference collapse: on an Adams eigenvector the convolution-log
truncation collapses to the eigenvector itself (only the weight-1 term survives). -/

end CK
