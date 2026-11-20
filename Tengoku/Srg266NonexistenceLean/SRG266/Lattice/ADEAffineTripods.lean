/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADETripodShape

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open SimpleGraph

abbrev TripodVertex (a b c : ℕ) := Option (Fin a ⊕ (Fin b ⊕ Fin c))

def tripodArmZero {a b c : ℕ} : Fin a ⊕ (Fin b ⊕ Fin c) → Prop
  | .inl i => i.1 = 0
  | .inr (.inl i) => i.1 = 0
  | .inr (.inr i) => i.1 = 0

def tripodArmRel {a b c : ℕ} :
    Fin a ⊕ (Fin b ⊕ Fin c) → Fin a ⊕ (Fin b ⊕ Fin c) → Prop
  | .inl i, .inl j => (pathGraph a).Adj i j
  | .inr (.inl i), .inr (.inl j) => (pathGraph b).Adj i j
  | .inr (.inr i), .inr (.inr j) => (pathGraph c).Adj i j
  | _, _ => False

def tripodRel {a b c : ℕ} : TripodVertex a b c → TripodVertex a b c → Prop
  | none, some x => tripodArmZero x
  | some x, some y => tripodArmRel x y
  | _, _ => False

def tripodGraph (a b c : ℕ) : SimpleGraph (TripodVertex a b c) :=
  SimpleGraph.fromRel tripodRel

def tripodArm0Hom (a b c : ℕ) : pathGraph a →g tripodGraph a b c where
  toFun i := some (.inl i)
  map_rel' := by
    intro i j hij
    rw [tripodGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp [hij.ne], Or.inl hij⟩

def tripodArm1Hom (a b c : ℕ) : pathGraph b →g tripodGraph a b c where
  toFun i := some (.inr (.inl i))
  map_rel' := by
    intro i j hij
    rw [tripodGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp [hij.ne], Or.inl hij⟩

def tripodArm2Hom (a b c : ℕ) : pathGraph c →g tripodGraph a b c where
  toFun i := some (.inr (.inr i))
  map_rel' := by
    intro i j hij
    rw [tripodGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp [hij.ne], Or.inl hij⟩

/--
@isnad1 id=connecte.3h3v.s5.835f147ccb17 from=translated src=- shape=e374b5c2 vocab=5e6b10e7
-/
theorem tripodGraph_connected {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (tripodGraph a b c).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  intro x
  cases x with
  | none => exact .rfl
  | some x =>
      rcases x with i | x
      · let z₀ : Fin a := ⟨0, ha⟩
        have hz : (tripodGraph a b c).Adj none (some (.inl z₀)) := by
          rw [tripodGraph, SimpleGraph.fromRel_adj]
          exact ⟨by simp, Or.inl rfl⟩
        exact hz.reachable.trans
          ((SimpleGraph.pathGraph_preconnected a z₀ i).map (tripodArm0Hom a b c))
      · rcases x with i | i
        · let z₁ : Fin b := ⟨0, hb⟩
          have hz : (tripodGraph a b c).Adj none (some (.inr (.inl z₁))) := by
            rw [tripodGraph, SimpleGraph.fromRel_adj]
            exact ⟨by simp, Or.inl rfl⟩
          exact hz.reachable.trans
            ((SimpleGraph.pathGraph_preconnected b z₁ i).map (tripodArm1Hom a b c))
        · let z₂ : Fin c := ⟨0, hc⟩
          have hz : (tripodGraph a b c).Adj none (some (.inr (.inr z₂))) := by
            rw [tripodGraph, SimpleGraph.fromRel_adj]
            exact ⟨by simp, Or.inl rfl⟩
          exact hz.reachable.trans
            ((SimpleGraph.pathGraph_preconnected c z₂ i).map (tripodArm2Hom a b c))

def affineE6Weight : TripodVertex 2 2 2 → ℤ
  | none => 3
  | some (.inl i) => 2 - i.1
  | some (.inr (.inl i)) => 2 - i.1
  | some (.inr (.inr i)) => 2 - i.1

def affineE7Weight : TripodVertex 1 3 3 → ℤ
  | none => 4
  | some (.inl _) => 2
  | some (.inr (.inl i)) => 3 - i.1
  | some (.inr (.inr i)) => 3 - i.1

def affineE8Weight : TripodVertex 1 2 5 → ℤ
  | none => 6
  | some (.inl _) => 3
  | some (.inr (.inl i)) => 4 - 2 * i.1
  | some (.inr (.inr i)) => 5 - i.1

set_option maxHeartbeats 2000000 in

/--
@isnad1 id=eq.0h0v.s8.4376ab94f679 from=translated src=- shape=b3845ce0 vocab=e8fe9b81
-/
theorem affineE6_cartanEnergy_zero :
    graphCartanEnergy (tripodGraph 2 2 2) affineE6Weight = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    tripodGraph, tripodRel, tripodArmRel, tripodArmZero,
    affineE6Weight, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
    Fin.sum_univ_succ]
  decide

set_option maxHeartbeats 2000000 in

/--
@isnad1 id=eq.0h0v.s8.23b611cd9a6c from=translated src=- shape=b3845ce0 vocab=53a25219
-/
theorem affineE7_cartanEnergy_zero :
    graphCartanEnergy (tripodGraph 1 3 3) affineE7Weight = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    tripodGraph, tripodRel, tripodArmRel, tripodArmZero,
    affineE7Weight, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
    Fin.sum_univ_succ]
  decide

set_option maxHeartbeats 2000000 in

/--
@isnad1 id=eq.0h0v.s8.fa52828ad454 from=translated src=- shape=b3845ce0 vocab=6d966e73
-/
theorem affineE8_cartanEnergy_zero :
    graphCartanEnergy (tripodGraph 1 2 5) affineE8Weight = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    tripodGraph, tripodRel, tripodArmRel, tripodArmZero,
    affineE8Weight, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
    Fin.sum_univ_succ]
  decide

/--
@isnad1 id=le.0h1v.s4.95cde9a34258 from=translated src=- shape=db5f9187 vocab=d79b412c
-/
theorem affineE6Weight_nonnegative (x) : 0 ≤ affineE6Weight x := by
  rcases x with _ | x
  · norm_num [affineE6Weight]
  rcases x with i | x
  · fin_cases i <;> norm_num [affineE6Weight]
  rcases x with i | i <;> fin_cases i <;> norm_num [affineE6Weight]

/--
@isnad1 id=le.0h1v.s4.51e4b7efec0f from=translated src=- shape=db5f9187 vocab=be6e62b1
-/
theorem affineE7Weight_nonnegative (x) : 0 ≤ affineE7Weight x := by
  rcases x with _ | x
  · norm_num [affineE7Weight]
  rcases x with i | x
  · fin_cases i; norm_num [affineE7Weight]
  rcases x with i | i <;> fin_cases i <;> norm_num [affineE7Weight]

/--
@isnad1 id=le.0h1v.s4.165da16b8174 from=translated src=- shape=db5f9187 vocab=fb4f4bea
-/
theorem affineE8Weight_nonnegative (x) : 0 ≤ affineE8Weight x := by
  rcases x with _ | x
  · norm_num [affineE8Weight]
  rcases x with i | x
  · fin_cases i; norm_num [affineE8Weight]
  rcases x with i | i <;> fin_cases i <;> norm_num [affineE8Weight]

/--
@isnad1 id=ne.0h0v.s6.b1b582018d2a from=translated src=- shape=43d66ac9 vocab=87b8815b
-/
theorem affineE6Weight_ne_zero : affineE6Weight ≠ 0 := by
  intro h
  have := congrFun h (none : TripodVertex 2 2 2)
  norm_num [affineE6Weight] at this

/--
@isnad1 id=ne.0h0v.s6.27a7ecd441df from=translated src=- shape=43d66ac9 vocab=be1d25d3
-/
theorem affineE7Weight_ne_zero : affineE7Weight ≠ 0 := by
  intro h
  have := congrFun h (none : TripodVertex 1 3 3)
  norm_num [affineE7Weight] at this

/--
@isnad1 id=ne.0h0v.s6.bc8bf7e65c30 from=translated src=- shape=43d66ac9 vocab=ca33c7ee
-/
theorem affineE8Weight_ne_zero : affineE8Weight ≠ 0 := by
  intro h
  have := congrFun h (none : TripodVertex 1 2 5)
  norm_num [affineE8Weight] at this

def tripodVertexMap {V : Type*} {a b c : ℕ} (z : V)
    (f₀ : Fin a → V) (f₁ : Fin b → V) (f₂ : Fin c → V) :
    TripodVertex a b c → V
  | none => z
  | some (.inl i) => f₀ i
  | some (.inr (.inl i)) => f₁ i
  | some (.inr (.inr i)) => f₂ i

def tripodVertexEmbedding {V : Type*} {a b c : ℕ} (z : V)
    (f₀ : Fin a ↪ V) (f₁ : Fin b ↪ V) (f₂ : Fin c ↪ V)
    (h₀z : ∀ i, f₀ i ≠ z) (h₁z : ∀ i, f₁ i ≠ z)
    (h₂z : ∀ i, f₂ i ≠ z)
    (h₀₁ : ∀ i j, f₀ i ≠ f₁ j) (h₀₂ : ∀ i j, f₀ i ≠ f₂ j)
    (h₁₂ : ∀ i j, f₁ i ≠ f₂ j) : TripodVertex a b c ↪ V :=
  ⟨tripodVertexMap z f₀ f₁ f₂, by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            rcases y with y | y
            · exact (h₀z y hxy.symm).elim
            · rcases y with y | y
              · exact (h₁z y hxy.symm).elim
              · exact (h₂z y hxy.symm).elim
    | some x =>
        cases y with
        | none =>
            rcases x with x | x
            · exact (h₀z x hxy).elim
            · rcases x with x | x
              · exact (h₁z x hxy).elim
              · exact (h₂z x hxy).elim
        | some y =>
            rcases x with x | x
            · rcases y with y | y
              · exact congr_arg (some ∘ Sum.inl) (f₀.injective hxy)
              · rcases y with y | y
                · exact (h₀₁ x y hxy).elim
                · exact (h₀₂ x y hxy).elim
            · rcases x with x | x
              · rcases y with y | y
                · exact (h₀₁ y x hxy.symm).elim
                · rcases y with y | y
                  · exact congr_arg (some ∘ Sum.inr ∘ Sum.inl) (f₁.injective hxy)
                  · exact (h₁₂ x y hxy).elim
              · rcases y with y | y
                · exact (h₀₂ y x hxy.symm).elim
                · rcases y with y | y
                  · exact (h₁₂ y x hxy.symm).elim
                  · exact congr_arg (some ∘ Sum.inr ∘ Sum.inr) (f₂.injective hxy)⟩

/--
@isnad1 id=adj.7h11v.s7.458cfc008273 from=translated src=- shape=07a8e2e3 vocab=6978da04
-/
theorem tripodRel_map {V : Type*} {G : SimpleGraph V} {a b c : ℕ}
    (z : V) (f₀ : Fin a → V) (f₁ : Fin b → V) (f₂ : Fin c → V)
    (h₀ : ∀ {i j}, (pathGraph a).Adj i j → G.Adj (f₀ i) (f₀ j))
    (h₁ : ∀ {i j}, (pathGraph b).Adj i j → G.Adj (f₁ i) (f₁ j))
    (h₂ : ∀ {i j}, (pathGraph c).Adj i j → G.Adj (f₂ i) (f₂ j))
    (hz₀ : ∀ i, i.1 = 0 → G.Adj z (f₀ i))
    (hz₁ : ∀ i, i.1 = 0 → G.Adj z (f₁ i))
    (hz₂ : ∀ i, i.1 = 0 → G.Adj z (f₂ i))
    {x y : TripodVertex a b c} (hxy : tripodRel x y) :
    G.Adj (tripodVertexMap z f₀ f₁ f₂ x)
      (tripodVertexMap z f₀ f₁ f₂ y) := by
  cases x with
  | none =>
      cases y with
      | none => simp [tripodRel] at hxy
      | some y =>
          rcases y with y | y
          · exact hz₀ y hxy
          · rcases y with y | y
            · exact hz₁ y hxy
            · exact hz₂ y hxy
  | some x =>
      cases y with
      | none => simp [tripodRel] at hxy
      | some y =>
          rcases x with x | x
          · rcases y with y | y
            · exact h₀ hxy
            · rcases y with y | y <;> simp [tripodRel, tripodArmRel] at hxy
          · rcases x with x | x
            · rcases y with y | y
              · simp [tripodRel, tripodArmRel] at hxy
              · rcases y with y | y
                · exact h₁ hxy
                · simp [tripodRel, tripodArmRel] at hxy
            · rcases y with y | y
              · simp [tripodRel, tripodArmRel] at hxy
              · rcases y with y | y
                · simp [tripodRel, tripodArmRel] at hxy
                · exact h₂ hxy

/--
@isnad1 id=false.5h7v.s8.767eb5fbcbd6 from=translated src=- shape=0f8df948 vocab=e86a7802
-/
theorem false_of_tripod_null_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hpos : IsPositiveCartan G)
    {a b c : ℕ} (f : TripodVertex a b c ↪ V)
    (hmap : ∀ {x y}, (tripodGraph a b c).Adj x y → G.Adj (f x) (f y))
    (w : TripodVertex a b c → ℤ) (hw0 : w ≠ 0) (hw : ∀ x, 0 ≤ w x)
    (henergy : graphCartanEnergy (tripodGraph a b c) w ≤ 0) : False := by
  classical
  have hle : tripodGraph a b c ≤ G.comap f := by
    intro x y hxy
    simpa only [SimpleGraph.comap_adj] using hmap hxy
  have hcomp : IsPositiveCartan (G.comap f) := hpos.comap f
  exact (not_isPositiveCartan_of_nonpositive_subgraph hle hw0 hw henergy) hcomp

/--
@isnad1 id=false.11h10v.s8.adcbba14b47f from=translated src=- shape=c1f1cc23 vocab=42683794
-/
theorem false_of_orientedArm_tripod
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    {a b c : ℕ} (ha : a ≤ A₀.length) (hb : b ≤ A₁.length)
    (hc : c ≤ A₂.length)
    (w : TripodVertex a b c → ℤ) (hw0 : w ≠ 0) (hw : ∀ x, 0 ≤ w x)
    (henergy : graphCartanEnergy (tripodGraph a b c) w ≤ 0) : False := by
  classical
  let f₀ := A₀.prefixEmbedding ha
  let f₁ := A₁.prefixEmbedding hb
  let f₂ := A₂.prefixEmbedding hc
  let f : TripodVertex a b c ↪ V := tripodVertexEmbedding z f₀ f₁ f₂
    (fun i ↦ A₀.prefixEmbedding_ne_center ha i)
    (fun i ↦ A₁.prefixEmbedding_ne_center hb i)
    (fun i ↦ A₂.prefixEmbedding_ne_center hc i)
    (fun i j ↦ A₀.prefixEmbedding_ne_of_component_ne A₁ h₀₁ ha hb i j)
    (fun i j ↦ A₀.prefixEmbedding_ne_of_component_ne A₂ h₀₂ ha hc i j)
    (fun i j ↦ A₁.prefixEmbedding_ne_of_component_ne A₂ h₁₂ hb hc i j)
  have hmap : ∀ {x y}, (tripodGraph a b c).Adj x y → G.Adj (f x) (f y) := by
    intro x y hxy
    rw [tripodGraph, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with hxy | hxy
    · exact tripodRel_map z f₀ f₁ f₂
        (fun h ↦ A₀.adj_prefixEmbedding_of_path_adj ha h)
        (fun h ↦ A₁.adj_prefixEmbedding_of_path_adj hb h)
        (fun h ↦ A₂.adj_prefixEmbedding_of_path_adj hc h)
        (fun i hi ↦ A₀.adj_center_prefixEmbedding_of_val_eq_zero ha i hi)
        (fun i hi ↦ A₁.adj_center_prefixEmbedding_of_val_eq_zero hb i hi)
        (fun i hi ↦ A₂.adj_center_prefixEmbedding_of_val_eq_zero hc i hi) hxy
    · exact (tripodRel_map z f₀ f₁ f₂
        (fun h ↦ A₀.adj_prefixEmbedding_of_path_adj ha h)
        (fun h ↦ A₁.adj_prefixEmbedding_of_path_adj hb h)
        (fun h ↦ A₂.adj_prefixEmbedding_of_path_adj hc h)
        (fun i hi ↦ A₀.adj_center_prefixEmbedding_of_val_eq_zero ha i hi)
        (fun i hi ↦ A₁.adj_center_prefixEmbedding_of_val_eq_zero hb i hi)
        (fun i hi ↦ A₂.adj_center_prefixEmbedding_of_val_eq_zero hc i hi) hxy).symm
  exact false_of_tripod_null_embedding hpos f hmap w hw0 hw henergy

/--
@isnad1 id=false.8h6v.s7.f1d8d71fe39e from=translated src=- shape=46794116 vocab=961bdf98
-/
theorem not_all_three_arms_length_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    (h₀ : 2 ≤ A₀.length) (h₁ : 2 ≤ A₁.length) (h₂ : 2 ≤ A₂.length) :
    False :=
  false_of_orientedArm_tripod hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
    h₀ h₁ h₂ affineE6Weight affineE6Weight_ne_zero
    affineE6Weight_nonnegative affineE6_cartanEnergy_zero.le

/--
@isnad1 id=false.8h6v.s7.21122d32de1c from=translated src=- shape=46794116 vocab=961bdf98
-/
theorem not_arms_length_one_three_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    (h₀ : 1 ≤ A₀.length) (h₁ : 3 ≤ A₁.length) (h₂ : 3 ≤ A₂.length) :
    False :=
  false_of_orientedArm_tripod hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
    h₀ h₁ h₂ affineE7Weight affineE7Weight_ne_zero
    affineE7Weight_nonnegative affineE7_cartanEnergy_zero.le

/--
@isnad1 id=false.8h6v.s7.53313e2f38ed from=translated src=- shape=46794116 vocab=961bdf98
-/
theorem not_arms_length_one_two_five
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    (h₀ : 1 ≤ A₀.length) (h₁ : 2 ≤ A₁.length) (h₂ : 5 ≤ A₂.length) :
    False :=
  false_of_orientedArm_tripod hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
    h₀ h₁ h₂ affineE8Weight affineE8Weight_ne_zero
    affineE8Weight_nonnegative affineE8_cartanEnergy_zero.le

end Lattice
end SRG266
