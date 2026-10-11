import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.Relay

namespace OAI

universe uOmega

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model

def Internal : (m : Model) → Set Vertex → m.Bit → Prop
  | .bond,D,e => e.1 ∈ D ∧ step e.1 e.2 ∈ D
  | .site,D,x => x ∈ D

def UniformOn (m : Model) (p : m.Bit → Set.Icc (0:ℝ) 1)
    (q : Set.Icc (0:ℝ) 1) (D : Set Vertex) : Prop := ∀ e, m.Internal D e → p e = q

theorem box_internal (m : Model) (B : Box) (e : m.Bit) :
    e ∈ B.bits m ↔ m.Internal {x | B.Contains x} e := by
  cases m <;> simp [Box.bits,Internal]

theorem internal_mono (m : Model) {D T : Set Vertex} (h : D ⊆ T) {e : m.Bit}
    (he : m.Internal D e) : m.Internal T e := by
  cases m
  · exact ⟨h he.1,h he.2⟩
  · exact h he

theorem UniformOn.box (m : Model) {p : m.Bit → Set.Icc (0:ℝ) 1} {q : Set.Icc (0:ℝ) 1}
    {D : Set Vertex} (h : m.UniformOn p q D) (B : Box) (hB : ∀ x, B.Contains x → x ∈ D) :
    ∀ e ∈ B.bits m, p e = q := fun e he => h e (m.internal_mono hB ((m.box_internal B e).mp he))

theorem seedReaches_target_mono (m : Model) (c : Vertex) (a b : ℕ) {T U : Set Vertex} (h : T ⊆ U) :
    m.SeedReaches c a b T ⊆ m.SeedReaches c a b U := by
  rintro ω ⟨x,hx,ho,y,hy,hp⟩
  exact ⟨x,hx,ho,y,h hy,hp⟩

end Model

namespace LatticeGraph
variable (G : LatticeGraph)
def ContainsSet (D : Set Vertex) : Prop :=
  (∀ x ∈ D, x ∈ G.vertices) ∧ ∀ e : Bond, e.1 ∈ D → step e.1 e.2 ∈ D → e ∈ G.edges

theorem ContainsSet.box {D : Set Vertex} (h : G.ContainsSet D) (B : Box)
    (hB : ∀ x, B.Contains x → x ∈ D) : G.ContainsBox B := by
  constructor
  · intro x hx; exact h.1 x (hB x (Box.mem_vertices B x |>.mp hx))
  · intro e he
    have hh := (Box.mem_bonds B e).mp he
    exact h.2 e (hB _ hh.1) (hB _ hh.2)
end LatticeGraph

namespace Box

def rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  ⟨fun i => c i-w i,fun i => c i+w i,fun i => by linarith [hw i]⟩

theorem contains_rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (rect c w hw).Contains x ↔ x ∈ LatticeRelay.Rect c w := by
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ w i
    rw [abs_le]
    dsimp [rect] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ w i at hh
    rw [abs_le] at hh
    change c i-w i ≤ x i ∧ x i ≤ c i+w i
    omega

def framedRect (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  rect (S.vertex c) (fun i => w (S.perm i)) (fun i => hw (S.perm i))

theorem abs_vertex_sub (S : SignedSymmetry) (x c : Vertex) (i : Fin 3) :
    |S.vertex x i-S.vertex c i| = |x (S.perm i)-c (S.perm i)| := by
  dsimp [SignedSymmetry.vertex]
  cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · have he : S.shift i+-x (S.perm i)-(S.shift i+-c (S.perm i)) =
        -(x (S.perm i)-c (S.perm i)) := by ring
    rw [he,abs_neg]
  · congr 1; ring

theorem framedRect_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (framedRect S c w hw).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Rect c w := by
  rw [framedRect,contains_rect]
  change (∀ i, |S.vertex x i-S.vertex c i| ≤ w (S.perm i)) ↔ _
  simp_rw [abs_vertex_sub]
  constructor
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)
  · intro h i; exact h _

theorem framedRect_expand_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i)
    (R : ℕ) (x : Vertex) :
    ((framedRect S c w hw).expand R).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Expand c w R := by
  have he : (framedRect S c w hw).expand R =
      framedRect S c (fun i => w i+R) (fun i => by have := hw i; positivity) := by
    apply Box.ext <;> funext i <;> dsimp [expand,framedRect,rect] <;> ring
  rw [he,framedRect_map]
  rfl
end Box

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem radius_seed {n : ℕ} (hn : n ∈ ({2*s.r,2*s.r+1,10*s.r} : Finset ℕ)) : s.seed ≤ n := by
  have := s.seed_R
  have := s.large_r
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

end ScaleData
end CriticalZ3

namespace MeasureTheory
open scoped _root_.MeasureTheory
open Classical
variable {Ω : Type uOmega} [MeasurableSpace Ω]
theorem finite_relay_bound (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsProbabilityMeasure μ] (A : ℕ → Set Ω)
    (η : ℝ) (n : ℕ) (h : ∀ i < n, μ.real (A i \ A (i+1)) ≤ η) :
    μ.real (A 0 \ A n) ≤ n*η := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,Set.sdiff_self,_root_.MeasureTheory.measureReal_empty,le_refl]
  | succ n ih =>
    have hs : A 0 \ A (n+1) ⊆ (A 0 \ A n) ∪ (A n \ A (n+1)) := by
      intro ω hω
      by_cases hn : ω ∈ A n
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    have hh := (_root_.MeasureTheory.measureReal_mono (μ := μ) hs).trans (_root_.MeasureTheory.measureReal_union_le _ _)
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith
end MeasureTheory

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem R_pos : 0 < s.R := s.seed_pos.trans s.seed_R

theorem route_width_nonneg (i : ℕ) (j : Fin 3) : 0 ≤ LatticeRelay.routeWidths s.r s.R i j := by
  unfold LatticeRelay.routeWidths
  split_ifs
  · dsimp [LatticeRelay.contractionWidths]
    split_ifs <;> positivity
  · positivity

def routeBox (S : SignedSymmetry) (i : ℕ) : Box :=
  Box.framedRect S (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i)
    (s.route_width_nonneg i)

theorem routeBox_contains (S : SignedSymmetry) (i : ℕ) (x : Vertex) :
    (s.routeBox S i).Contains x ↔ x ∈ S.vertex '' LatticeRelay.P s.r s.R i := by
  rw [←S.vertex.apply_symm_apply x,routeBox,Box.framedRect_map]
  simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
  rfl

end ScaleData
end CriticalZ3

end OAI
