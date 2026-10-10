import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.EquivariantFlags

namespace OAI

universe u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter

/-! Disjoint equivariant coordinate balls for the unique initial zero orbit. -/

open Set Finset
namespace SharpLiebThirring.PLParity
section OrbitBalls
attribute [local instance] Classical.propDecidable
variable {G : Type u103} {E : Type u104} [Group G] [MetricSpace E] [MulAction G E]
  [IsIsometricSMul G E]

omit [IsIsometricSMul G E] in
lemma orbit_separation [Fintype G] (p : E) (hp : ∀ g : G, g • p = p → g = 1) :
    ∃ R > 0, ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p) := by
  classical
  let d : G × G → ℝ := fun q ↦ if q.1 = q.2 then 1 else dist (q.1 • p) (q.2 • p)
  have hd (q : G × G) : 0 < d q := by
    dsimp [d]
    split_ifs with he
    · norm_num
    · apply dist_pos.mpr
      intro hh
      have hx : (q.2⁻¹ * q.1) • p = p := by rw [mul_smul, hh, inv_smul_smul]
      exact he (inv_mul_eq_one.mp (hp _ hx)).symm
  have hn : (Finset.univ : Finset (G × G)).Nonempty := ⟨(1,1), Finset.mem_univ _⟩
  let b := Finset.univ.inf' hn d
  have hb : 0 < b := (Finset.lt_inf'_iff _).mpr (fun q _ ↦ hd q)
  refine ⟨b / 16, by positivity, ?_⟩
  intro g k hgk
  have hle : b ≤ d (g,k) := Finset.inf'_le _ (Finset.mem_univ _)
  dsimp [d] at hle
  rw [ite_eq_right hgk] at hle
  linarith

variable (p : E) (R : ℝ)

def orbitBall : Set E := {x | ∃ g : G, dist x (g • p) < R}

noncomputable def ballLabel (x : E) : G :=
  if hx : x ∈ orbitBall (G := G) p R then hx.choose else 1

omit [IsIsometricSMul G E] in
lemma ballLabel_dist {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    dist x (ballLabel (G := G) p R x • p) < R := by
  simp only [ballLabel, dite_eq_left hx]
  exact hx.choose_spec

lemma orbitBall_smul (g : G) {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    g • x ∈ orbitBall (G := G) p R := by
  obtain ⟨k,hk⟩ := hx
  refine ⟨g*k, ?_⟩
  rw [mul_smul, dist_smul]
  exact hk

lemma mem_orbitBall_smul_iff (g : G) (x : E) :
    g • x ∈ orbitBall (G := G) p R ↔ x ∈ orbitBall (G := G) p R := by
  constructor
  · intro hx
    simpa only [inv_smul_smul] using orbitBall_smul p R g⁻¹ hx
  · exact orbitBall_smul p R g

variable (hR : 0 < R) (hsep : ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p))

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq {x : E} {g : G} (hx : dist x (g • p) < R) :
    ballLabel (G := G) p R x = g := by
  by_contra hn
  have hl := ballLabel_dist p R (show x ∈ orbitBall (G := G) p R from ⟨g,hx⟩)
  have hd := dist_triangle (ballLabel (G := G) p R x • p) x (g • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

include hR hsep in
lemma ballLabel_smul (g : G) {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    ballLabel (G := G) p R (g • x) = g * ballLabel (G := G) p R x := by
  apply ballLabel_eq p R hR hsep
  rw [mul_smul, dist_smul]
  exact ballLabel_dist p R hx

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq_of_dist {x y : E} (hx : x ∈ orbitBall (G := G) p R)
    (hy : y ∈ orbitBall (G := G) p R) (hxy : dist x y ≤ R) :
    ballLabel (G := G) p R x = ballLabel (G := G) p R y := by
  by_contra hn
  have hlx := ballLabel_dist p R hx
  have hly := ballLabel_dist p R hy
  have hd := dist_triangle4 (ballLabel (G := G) p R x • p) x y (ballLabel (G := G) p R y • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

include hR hsep in
omit [IsIsometricSMul G E] in
lemma exists_common_ballLabel {ι : Type u105} (v : ι → E) (P : ι → Prop)
    (hv : ∀ i, P i → v i ∈ orbitBall (G := G) p R)
    (hd : ∀ i j, dist (v i) (v j) ≤ R) :
    ∃ g : G, ∀ i, P i → ballLabel (G := G) p R (v i) = g := by
  by_cases hn : ∃ i, P i
  · obtain ⟨j,hj⟩ := hn
    refine ⟨ballLabel (G := G) p R (v j), ?_⟩
    intro i hi
    exact ballLabel_eq_of_dist p R hR hsep (hv i hi) (hv j hj) (hd i j)
  · exact ⟨1, fun i hi ↦ False.elim (hn ⟨i,hi⟩)⟩

end OrbitBalls
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
section Translate
variable {V : Type u106} {W : Type u107} {ι : Type u108} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
lemma augmented_translate_independent (v : ι → V) (p : V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i - p)) := by
  let fst : (ℝ × V) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ V
  let snd : (ℝ × V) →ₗ[ℝ] V := LinearMap.snd ℝ ℝ V
  let T : (ℝ × V) →ₗ[ℝ] (ℝ × V) := fst.prod (snd - fst.smulRight p)
  have hT : Function.Injective T := by
    rintro ⟨a,x⟩ ⟨b,y⟩ he
    have hab : a = b := congrArg Prod.fst he
    have hxy : x - a • p = y - b • p := congrArg Prod.snd he
    rw [← hab] at hxy
    exact Prod.ext hab (sub_left_inj.mp hxy)
  have hh := hv.map' T (LinearMap.ker_eq_bot.mpr hT)
  change LinearIndependent ℝ (fun i ↦ T ((1 : ℝ), v i)) at hh
  have he : (fun i ↦ T ((1 : ℝ), v i)) = (fun i ↦ ((1 : ℝ), v i - p)) := by
    funext i
    change ((1 : ℝ), v i - (1 : ℝ) • p) = (1, v i - p)
    rw [one_smul]
  rwa [he] at hh

lemma augmented_equiv_independent (v : ι → V) (L : V ≃ₗ[ℝ] W)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), L (v i))) :=
  hv.map' ((LinearEquiv.refl ℝ ℝ).prodCongr L).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))
end Translate

section Model
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u110} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin (d + 1) → ℝ) (R : ℝ)

def affineOrbitModel (q : Fin d → ℝ) (x : Fin (d + 1) → ℝ) : V :=
  let s := ballLabel (G := H) p R x
  ρ s (L (spatial (s⁻¹ • x) - q))

end Model
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

lemma Flag.dist_gridPoint_gridPoint {n : ℕ} (F : Flag n) (h : ℝ) (hh : 0 ≤ h)
    (j k : Fin (n + 1)) : dist (gridPoint h (F.vertex j)) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, gridPoint_vertex]
  calc
    _ ≤ dist (h • F.point j) (h • F.center) + dist (h • F.center) (h • F.point k) := dist_triangle _ _ _
    _ ≤ h / 2 + h / 2 := by
      apply add_le_add (F.dist_scaled_point_center h hh j)
      rw [dist_comm]
      exact F.dist_scaled_point_center h hh k
    _ = h := by ring

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
