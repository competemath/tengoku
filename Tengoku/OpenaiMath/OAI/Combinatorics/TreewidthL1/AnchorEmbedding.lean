import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.AnchorGeometry

namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

noncomputable def graphPath (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (hdist : ∀ u v, dist u v = shortestPathDistance G ℓ u v)
    (hne : ∀ i, (B i).Nonempty)
    (hD : ∀ i, D i = bagDistance G ℓ (B i) (hne i))
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (hbag : ∀ i, (B i).card ≤ k) (hbound : ∀ i v, D i v ≤ P.Δ)
    (X Y : Fin (n+1)) (x y : V) (hx : x ∈ B X) (hy : y ∈ B Y) (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (hpos : 0 < D ((downPath T hT root X).getVert s) x) : PathGeometry P := by
  let q := downPath T hT root X
  have hgeo (a t : ℕ) (hat : a ≤ t) :
      D (q.getVert t) x ≤ D (q.getVert a) x ∧
      ∃ v ∈ B (q.getVert t), D (q.getVert a) v+dist x v = D (q.getVert a) x := by
    have hp : q.getVert t ∈ (q.drop a).support := by
      simpa only [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hat] using (q.drop a).getVert_mem_support (t-a)
    have hh := separator_bag_geometry G ℓ hG hℓ T B hne hT hedge hrun (q.drop a)
      ((downPath_isPath T hT root X).drop a) hp hx
    rw [hD,hD]
    refine ⟨hh.1,?_⟩
    obtain ⟨v,hv,hhv⟩ := hh.2
    refine ⟨v,hv,?_⟩
    rw [hdist,shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le) x v]
    exact hhv
  refine {
    X := X, Y := Y, x := x, y := y, start := s, start_le := hsx, hx := hx, hy := hy,
    positive := hpos, bounded := hbound, bag_bound := hbag
    nonneg := ?_, lipschitz := ?_, zero := ?_, monotone := ?_, near := ?_, geodesic := ?_, suffix := ?_ }
  · intro i v
    rw [hD]
    exact bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  · intro i u v
    rw [hD,hdist]
    exact bagDistance_lipschitz G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) u v
  · intro i v hv
    rw [hD]
    apply le_antisymm
    · have hh := bagDistance_le G ℓ (B i) (hne i) v hv
      rw [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)] at hh
      exact hh
    · exact bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  · intro a t hat
    exact (hgeo a t hat).1
  · intro t
    obtain ⟨p,hp,hpdist⟩ := bagDistance_attained G ℓ (B (q.getVert t)) (hne _) x
    exact ⟨p,hp,by rw [hD,hdist]; exact hpdist.symm⟩
  · intro a t hat ht
    exact (hgeo a t hat).2
  · intro e hse he
    exact ⟨(forest T hT root).depth Y-s,join_prefix_data T hT root X Y s hsx hsy hs hmax e hse he⟩

namespace PathGeometry
variable {P} (A : PathGeometry P)

end PathGeometry
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
noncomputable section

theorem test_parameters_exist (k : ℕ) (α π : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/8)
    (hπ : 0 < π) (hπ1 : π ≤ 1) :
    ∃ J H η Q : ℝ, J = 10*(upper k+4) ∧ 10^5*J < H ∧
      Nonempty (TestParameters k α π η H Q) := by
  let J := 10*(upper k+4)
  let H := 10^5*J+1
  have hU := upper_pos k
  have hL := particleLip_pos k
  have hJ : 0 < J := by dsimp [J]; positivity
  have hH : 1 < H := by dsimp [H]; nlinarith
  let η := 1/(16*H)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η < 1/4 := by
    dsimp [η]; apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr; nlinarith
  have hr : 4*η*H < 1 := by
    have hH0 : H ≠ 0 := by linarith
    dsimp [η]; field_simp; norm_num
  let c := α/8*η
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ≤ 1/2 := by
    have hαη := mul_le_mul_of_nonneg_right hα1 hη.le
    dsimp [c]; nlinarith
  let b := c/(8*((k:ℝ)+1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  let w := π/8*b
  have hw : 0 < w := by dsimp [w]; positivity
  let Q := (1+upper k+particleLip k)/w+(upper k+1)
  have hQ : upper k+1 ≤ Q := by
    dsimp [Q]; have hh : 0 ≤ (1+upper k+particleLip k)/w := by positivity
    linarith
  have hbound : 1+upper k+particleLip k ≤ (π/8*b)*Q := by
    have hh : w*((1+upper k+particleLip k)/w) = 1+upper k+particleLip k :=
      mul_div_cancel₀ _ hw.ne'
    change _ ≤ w*Q
    dsimp only [Q]
    nlinarith [mul_nonneg hw.le (show 0 ≤ upper k+1 by positivity)]
  refine ⟨J,H,η,Q,rfl,by dsimp [H]; linarith,⟨?_⟩⟩
  exact {
    c := c, b := b, c_eq := rfl, c_pos := hc, c_half := hc2,
    b_eq := rfl, b_pos := hb, b_one := hb1, eta_pos := hη, eta_small := hη4,
    pi_pos := hπ, pi_one := hπ1, radius := hr, qbound := hbound, qlarge := hQ }
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

end
end BoundedTreewidthL1.AnchorExperiment

end OAI
