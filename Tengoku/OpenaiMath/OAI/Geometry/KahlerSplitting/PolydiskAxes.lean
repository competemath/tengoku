import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.ParameterGrid

namespace OAI

section

noncomputable section
open Set Metric
namespace UnitPolydisk

def discShift (a z : ℂ) : ℂ := (a+z)/(1+star a*z)

lemma denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : 1+star a*z ≠ 0 := by
  intro he
  have hn : ‖star a*z‖ < 1 := by
    rw [norm_mul,norm_star]
    nlinarith [norm_nonneg a,norm_nonneg z]
  have hh : star a*z = -1 := by linear_combination he
  rw [hh,norm_neg,norm_one] at hn
  exact (lt_irrefl 1) hn

lemma normSq_difference (a z : ℂ) :
    Complex.normSq (1+star a*z) - Complex.normSq (a+z) =
      (1-Complex.normSq a)*(1-Complex.normSq z) := by
  simp only [Complex.star_def,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.one_re,Complex.one_im]
  ring

lemma discShift_mem {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖discShift a z‖ < 1 := by
  have hden := denominator_ne_zero ha hz
  have ha2 : Complex.normSq a < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz2 : Complex.normSq z < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hn : Complex.normSq (a+z) < Complex.normSq (1+star a*z) := by
    have hh := normSq_difference a z
    have hp := mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hz2)
    linarith
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hn
  rw [discShift,norm_div,div_lt_one (norm_pos_iff.mpr hden)]
  nlinarith [norm_nonneg (a+z),norm_nonneg (1+star a*z)]

lemma discShift_zero (a : ℂ) : discShift a 0=a := by simp [discShift]

lemma discShift_neg_self {a : ℂ}  : discShift (-a) a=0 := by
  simp [discShift]

lemma discShift_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    discShift (-a) (discShift a z)=z := by
  have hden := denominator_ne_zero ha hz
  have ha' : ‖-a‖ < 1 := by simpa using ha
  have hden' := denominator_ne_zero ha' (discShift_mem ha hz)
  change (-a+discShift a z)/(1+star (-a)*discShift a z)=z
  apply (div_eq_iff hden').mpr
  simp only [discShift,star_neg,div_eq_mul_inv]
  have hcancel : (1+star a*z)*(1+star a*z)⁻¹=1 := mul_inv_cancel₀ hden
  linear_combination (a+z)*hcancel

lemma differentiableOn_discShift {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (discShift a) (ball (0:ℂ) 1) := by
  exact ((differentiable_const a).add differentiable_id).differentiableOn.div
    ((differentiable_const 1).add ((differentiable_const (star a)).mul differentiable_id)).differentiableOn
    (fun z hz ↦ denominator_ne_zero ha (mem_ball_zero_iff.mp hz))

def shift {d : ℕ} (a z : Fin d → ℂ) : Fin d → ℂ := fun i ↦ discShift (a i) (z i)

lemma norm_coord_lt_one {d : ℕ} {a : Fin d → ℂ} (ha : a ∈ ball 0 1) (i : Fin d) : ‖a i‖ < 1 :=
  (norm_le_pi_norm a i).trans_lt (mem_ball_zero_iff.mp ha)

lemma shift_mem {d : ℕ} {a z : Fin d → ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    shift a z ∈ ball 0 1 := by
  rw [mem_ball_zero_iff,pi_norm_lt_iff (by norm_num : (0:ℝ)<1)]
  exact fun i ↦ discShift_mem (norm_coord_lt_one ha i) (norm_coord_lt_one hz i)

lemma shift_zero {d : ℕ} (a : Fin d → ℂ) : shift a 0=a := by ext i; exact discShift_zero (a i)

lemma shift_inverse {d : ℕ} {a z : Fin d → ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    shift (-a) (shift a z)=z := by
  ext i
  exact discShift_inverse (norm_coord_lt_one ha i) (norm_coord_lt_one hz i)

lemma differentiableOn_shift {d : ℕ} {a : Fin d → ℂ} (ha : a ∈ ball 0 1) :
    DifferentiableOn ℂ (shift a) (ball 0 1) := by
  apply differentiableOn_pi.mpr
  intro i
  exact (differentiableOn_discShift (norm_coord_lt_one ha i)).comp
    (differentiable_apply i).differentiableOn
    (fun z hz ↦ mem_ball_zero_iff.mpr (norm_coord_lt_one hz i))

end UnitPolydisk
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s d e : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBlockBox.unique_polydisk {F G : Model d × Model e → X.Carrier}
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (hF : IsBlockBox S (ball 0 1 ×ˢ ball 0 1) F) (hG : IsBlockBox S (ball 0 1 ×ˢ ball 0 1) G)
    {p₀ : Model d} {q₀ : Model e} (hp₀ : p₀ ∈ ball 0 1) (hq₀ : q₀ ∈ ball 0 1)
    (hb : ∀ p ∈ ball 0 1, F (p,q₀)=G (p,q₀))
    (hl : ∀ q ∈ ball 0 1, F (p₀,q)=G (p₀,q)) : EqOn F G (ball 0 1 ×ˢ ball 0 1) := by
  let : PathConnectedSpace (ball (0:Model d) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp ((convex_ball (0:Model d) 1).isPathConnected ⟨p₀,hp₀⟩)
  let : PathConnectedSpace (ball (0:Model e) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp ((convex_ball (0:Model e) 1).isPathConnected ⟨q₀,hq₀⟩)
  have hcover : ∀ x : X.Carrier, ∃ c ∈ splittingAtlas S, x ∈ c.source := by
    intro x
    obtain ⟨c,hc,_⟩ := exists_splittingChart S h₁ h₂ x
    exact ⟨c.chart,⟨c,rfl⟩,hc⟩
  have he := ProductBoxTopology.unique_connected (splittingAtlas S) hcover
    (hF.plaqueBox isOpen_ball isOpen_ball) (hG.plaqueBox isOpen_ball isOpen_ball)
    (⟨p₀,hp₀⟩ : ball (0:Model d) 1) (⟨q₀,hq₀⟩ : ball (0:Model e) 1)
    (fun p ↦ hb p p.property) (fun q ↦ hl q q.property)
  intro z hz
  exact congrFun he (⟨z.1,hz.1⟩,⟨z.2,hz.2⟩)

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s d e : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def IsDiskHorizontal (S : HolomorphicSplitting X r s) (f : Polydisk d → X.Carrier) : Prop :=
  ∃ g : Model d → X.Carrier, IsHorizontalMap S (Polydisk d) g ∧ ∀ z : Polydisk d, g z=f z

def IsDiskVertical (S : HolomorphicSplitting X r s) (f : Polydisk e → X.Carrier) : Prop :=
  ∃ g : Model e → X.Carrier, IsVerticalMap S (Polydisk e) g ∧ ∀ z : Polydisk e, g z=f z

def IsDiskTile (S : HolomorphicSplitting X r s) (f : Polydisk d × Polydisk e → X.Carrier) : Prop :=
  ∃ g : Model d × Model e → X.Carrier, IsBlockBox S (Polydisk d ×ˢ Polydisk e) g ∧
    ∀ z : Polydisk d × Polydisk e, g (z.1,z.2)=f z

lemma IsDiskTile.horizontal {f : Polydisk d × Polydisk e → X.Carrier}
    (hf : IsDiskTile S f) (q : Polydisk e) : IsDiskHorizontal S (fun p ↦ f (p,q)) := by
  obtain ⟨g,hg,he⟩ := hf
  exact ⟨fun p ↦ g (p,q),hg.horizontal_slice isOpen_ball isOpen_ball q.property,
    fun p ↦ he (p,q)⟩

lemma IsDiskTile.vertical {f : Polydisk d × Polydisk e → X.Carrier}
    (hf : IsDiskTile S f) (p : Polydisk d) : IsDiskVertical S (fun q ↦ f (p,q)) := by
  obtain ⟨g,hg,he⟩ := hf
  exact ⟨fun q ↦ g (p,q),hg.vertical_slice isOpen_ball isOpen_ball p.property,
    fun q ↦ he (p,q)⟩

lemma IsDiskTile.plaqueBox {f : Polydisk d × Polydisk e → X.Carrier}
    (hf : IsDiskTile S f) : ProductBoxTopology.IsBox (splittingAtlas S) f := by
  obtain ⟨g,hg,he⟩ := hf
  have heq : f=(fun z : Polydisk d × Polydisk e ↦ g (z.1,z.2)) := funext fun z ↦ (he z).symm
  rw [heq]
  exact hg.plaqueBox isOpen_ball isOpen_ball

end UniversalCoverSplitting
end
end

end OAI
