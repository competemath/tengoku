import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Complex_contDiffOn_infty_of_differentiableOn_pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 7 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc

set_option autoImplicit false

open Topology Filter Metric Set

noncomputable section

namespace LocalGroupLawK3b

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def S (ρ : ℝ) : Set (E × E) := ball (0 : E) ρ ×ˢ ball (0 : E) ρ

/--
@isnad1 id=isopen.0h2v.s5.fa366310d191 from=translated src=- shape=d35e94b6 vocab=ff7ffded
-/
theorem isOpen_S (ρ : ℝ) : IsOpen (S (E := E) ρ) := isOpen_ball.prod isOpen_ball

/--
@isnad1 id=mem.2h4v.s6.c43c33d4a5b0 from=translated src=- shape=bf4e6437 vocab=7e80f17f
-/
theorem mem_S {ρ : ℝ} {x y : E} (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) :
    (x, y) ∈ S ρ := ⟨hx, hy⟩

def uc (F : E → E → E) : E × E → E := fun p => F p.1 p.2

def D1 (F : E → E → E) : E × E → (E × E →L[ℂ] E) := fun p => fderiv ℂ (uc F) p

def D2 (F : E → E → E) : E × E → (E × E →L[ℂ] (E × E →L[ℂ] E)) := fun p => fderiv ℂ (D1 F) p

def P2 (F : E → E → E) (p : E × E) : E →L[ℂ] E := (D1 F p).comp (ContinuousLinearMap.inr ℂ E E)

def P1 (F : E → E → E) (p : E × E) : E →L[ℂ] E := (D1 F p).comp (ContinuousLinearMap.inl ℂ E E)

def Φ (F : E → E → E) (u : E) : E →L[ℂ] E := P2 F (u, 0)

def ω (F : E → E → E) (u : E) : E →L[ℂ] E := Ring.inverse (Φ F u)

def ω' (F : E → E → E) (u : E) : E →L[ℂ] (E →L[ℂ] E) := fderiv ℂ (ω F) u

section regularity

variable {F : E → E → E} {ρ : ℝ}

/--
@isnad1 id=eq.0h0v.s5.99aa3679fed1 from=translated src=- shape=9fd49ca8 vocab=2c75a68e
-/
theorem two_eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num

/--
@isnad1 id=differen.1h3v.s7.7927de77be15 from=translated src=- shape=ec36df92 vocab=892e9031
-/
theorem differentiableOn_uc (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) :
    DifferentiableOn ℂ (uc F) (S ρ) :=
  hF2.differentiableOn (by norm_num)

/--
@isnad1 id=hasfderi.2h4v.s7.2c50e6ec2267 from=translated src=- shape=76c99622 vocab=09bc5f8f
-/
theorem hasFDerivAt_uc (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {p : E × E} (hp : p ∈ S ρ) :
    HasFDerivAt (uc F) (D1 F p) p :=
  ((differentiableOn_uc hF2).differentiableAt ((isOpen_S ρ).mem_nhds hp)).hasFDerivAt

/--
@isnad1 id=contdiff.1h3v.s8.d8a4cea80d46 from=translated src=- shape=e2bb862a vocab=fd9d4c4c
-/
theorem contDiffOn_D1 (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) : ContDiffOn ℂ 1 (D1 F) (S ρ) := by
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 1) (f := uc F) (isOpen_S ρ)).1
    (by rw [← two_eq]; exact hF2)
  exact h.2.2

/--
@isnad1 id=hasfderi.2h4v.s9.91758586b802 from=translated src=- shape=dd0162ae vocab=e3160f62
-/
theorem hasFDerivAt_D1 (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {p : E × E} (hp : p ∈ S ρ) :
    HasFDerivAt (D1 F) (D2 F p) p :=
  (((contDiffOn_D1 hF2).differentiableOn one_ne_zero).differentiableAt
    ((isOpen_S ρ).mem_nhds hp)).hasFDerivAt

/--
@isnad1 id=hasfderi.3h5v.s7.604b623fbb13 from=translated src=- shape=86c63d29 vocab=da1f7274
-/
theorem hasFDerivAt_right (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {x y : E}
    (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) :
    HasFDerivAt (fun y' => F x y') (P2 F (x, y)) y := by
  have h := (hasFDerivAt_uc hF2 (mem_S hx hy)).comp y (hasFDerivAt_prodMk_right (𝕜 := ℂ) x y)
  exact h

/--
@isnad1 id=hasfderi.3h5v.s7.0a04fb997874 from=translated src=- shape=8ddda472 vocab=77e41044
-/
theorem hasFDerivAt_left (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {x y : E}
    (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) :
    HasFDerivAt (fun x' => F x' y) (P1 F (x, y)) x := by
  have h := (hasFDerivAt_uc hF2 (mem_S hx hy)).comp x (hasFDerivAt_prodMk_left (𝕜 := ℂ) x y)
  exact h

/--
@isnad1 id=mem.1h2v.s6.f3d1726ebb0a from=translated src=- shape=db58bd0e vocab=18310016
-/
theorem zero_mem_ball (hρ : 0 < ρ) : (0 : E) ∈ ball (0 : E) ρ := mem_ball_self hρ

/--
@isnad1 id=eq.3h3v.s8.7b25b065b17b from=translated src=- shape=16aadb37 vocab=e1c4d343
-/
theorem Φ_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) : Φ F 0 = 1 := by
  have h1 : HasFDerivAt (fun y' => F 0 y') (Φ F 0) 0 :=
    hasFDerivAt_right hF2 (zero_mem_ball hρ) (zero_mem_ball hρ)
  have h2 : HasFDerivAt (fun y' : E => y') (Φ F 0) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) hρ] with v hv
    exact (hzero_left v hv).symm
  have h3 : HasFDerivAt (fun y' : E => y') (ContinuousLinearMap.id ℂ E) 0 := hasFDerivAt_id 0
  exact (h3.unique h2).symm ▸ rfl

end regularity

section units

variable {F : E → E → E} {ρ : ℝ}

/--
@isnad1 id=contdiff.1h3v.s7.2cb3e6a1ed18 from=translated src=- shape=22bd7832 vocab=82c096aa
-/
theorem contDiffOn_Φ (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) : ContDiffOn ℂ 1 (Φ F) (ball (0 : E) ρ) := by
  have h1 : ContDiffOn ℂ 1 (fun u : E => D1 F (u, 0)) (ball (0 : E) ρ) := by
    refine (contDiffOn_D1 hF2).comp (contDiffOn_id.prodMk contDiffOn_const) ?_
    intro u hu
    exact mem_S hu (by simpa using (lt_of_le_of_lt (norm_nonneg u) (mem_ball_zero_iff.mp hu)))
  exact h1.clm_comp contDiffOn_const

/--
@isnad1 id=isunit.1h2v.s9.fa80dc745e93 from=translated src=- shape=3f3113a4 vocab=bff5bfef
-/
theorem isUnit_of_norm_sub_one_lt {A : E →L[ℂ] E} (h : ‖A - 1‖ < 1) : IsUnit A := by
  have := (Units.oneSub (1 - A) (by rw [norm_sub_rev]; exact h)).isUnit
  simpa using this

/--
@isnad1 id=eq.1h3v.s9.6f6de3268474 from=translated src=- shape=bf3eee6c vocab=ce12bc9a
-/
theorem ω_mul_Φ {u : E} (hu : IsUnit (Φ F u)) : ω F u * Φ F u = 1 :=
  Ring.inverse_mul_cancel _ hu

/--
@isnad1 id=eq.1h3v.s9.c4624394cf0d from=translated src=- shape=ba27e7ad vocab=ce12bc9a
-/
theorem Φ_mul_ω {u : E} (hu : IsUnit (Φ F u)) : Φ F u * ω F u = 1 :=
  Ring.mul_inverse_cancel _ hu

/--
@isnad1 id=eq.1h4v.s8.c4b71f1427ae from=translated src=- shape=ff330c1b vocab=f3ce130e
-/
theorem Φ_ω_apply {u : E} (hu : IsUnit (Φ F u)) (a : E) : Φ F u (ω F u a) = a := by
  have := congrArg (fun T : E →L[ℂ] E => T a) (Φ_mul_ω hu)
  simpa using this

/--
@isnad1 id=eq.3h3v.s8.5e7401ab3e32 from=translated src=- shape=16aadb37 vocab=4ec24cc5
-/
theorem ω_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) : ω F 0 = 1 := by
  simp [ω, Φ_zero hρ hF2 hzero_left]

/--
@isnad1 id=contdiff.3h4v.s8.f2733adbda6c from=translated src=- shape=ab33e457 vocab=121f15fd
-/
theorem contDiffOn_ω (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) : ContDiffOn ℂ 1 (ω F) (ball (0 : E) r₀) := by
  intro u hu
  have hΦ : ContDiffAt ℂ 1 (Φ F) u :=
    (contDiffOn_Φ hF2).contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball hr₀ hu))
  have hinv : ContDiffAt ℂ 1 Ring.inverse (Φ F u) := by
    have := contDiffAt_ringInverse ℂ (n := 1) (hunit u hu).unit
    rwa [IsUnit.unit_spec] at this
  exact (hinv.comp u hΦ).contDiffWithinAt

/--
@isnad1 id=hasfderi.4h5v.s9.79ca5a79b3a1 from=translated src=- shape=d9a11d23 vocab=22bd6969
-/
theorem hasFDerivAt_ω (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) {u : E} (hu : u ∈ ball (0 : E) r₀) :
    HasFDerivAt (ω F) (ω' F u) u :=
  (((contDiffOn_ω hF2 hr₀ hunit).differentiableOn one_ne_zero).differentiableAt
    (isOpen_ball.mem_nhds hu)).hasFDerivAt

/--
@isnad1 id=continuo.3h4v.s8.9a45177e4941 from=translated src=- shape=e66d8e59 vocab=127d28a6
-/
theorem continuousOn_ω (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) : ContinuousOn (ω F) (ball (0 : E) r₀) :=
  (contDiffOn_ω hF2 hr₀ hunit).continuousOn

/--
@isnad1 id=continuo.3h4v.s9.7932609ff843 from=translated src=- shape=6f66eaec vocab=8404bccb
-/
theorem continuousOn_ω' (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) : ContinuousOn (ω' F) (ball (0 : E) r₀) :=
  (contDiffOn_ω hF2 hr₀ hunit).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl

end units

section assoc

variable {F : E → E → E} {ρ : ℝ}

/--
@isnad1 id=eq.7h5v.s9.5842f01840a2 from=translated src=- shape=c548ef4d vocab=1092b349
-/
theorem P2_comp_Φ (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {x y : E} (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) (hxy : F x y ∈ ball (0 : E) ρ) :
    (P2 F (x, y)).comp (Φ F y) = Φ F (F x y) := by

  have hin : HasFDerivAt (fun z => F y z) (Φ F y) 0 := hasFDerivAt_right hF2 hy (zero_mem_ball hρ)
  have hout : HasFDerivAt (fun q => F x q) (P2 F (x, y)) (F y 0) := by
    rw [hzero_right y hy]; exact hasFDerivAt_right hF2 hx hy
  have hcomp : HasFDerivAt (fun z => F x (F y z)) ((P2 F (x, y)).comp (Φ F y)) 0 := hout.comp 0 hin

  have hleft : HasFDerivAt (fun z => F (F x y) z) (Φ F (F x y)) 0 :=
    hasFDerivAt_right hF2 hxy (zero_mem_ball hρ)

  have hev : ∀ᶠ z in 𝓝 (0 : E), F (F x y) z = F x (F y z) := by
    have h1 : ∀ᶠ z in 𝓝 (0 : E), z ∈ ball (0 : E) ρ := ball_mem_nhds _ hρ
    have h2 : ∀ᶠ z in 𝓝 (0 : E), F y z ∈ ball (0 : E) ρ := by
      have hc : ContinuousAt (fun z => F y z) 0 := hin.continuousAt
      have : F y 0 ∈ ball (0 : E) ρ := by rw [hzero_right y hy]; exact hy
      exact hc.preimage_mem_nhds (isOpen_ball.mem_nhds this)
    filter_upwards [h1, h2] with z hz hyz
    exact hassoc x y z hx hy hz hxy hyz
  have hleft' : HasFDerivAt (fun z => F x (F y z)) (Φ F (F x y)) 0 :=
    hleft.congr_of_eventuallyEq (hev.mono fun z hz => hz.symm)
  exact hcomp.unique hleft'

/--
@isnad1 id=eq.9h5v.s9.0aa0571e90a9 from=translated src=- shape=784e7c7d vocab=5566cfe3
-/
theorem ω_comp_P2 (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {x y : E} (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) (hxy : F x y ∈ ball (0 : E) ρ)
    (huy : IsUnit (Φ F y)) (huxy : IsUnit (Φ F (F x y))) :
    (ω F (F x y)).comp (P2 F (x, y)) = ω F y := by
  have h := P2_comp_Φ hρ hF2 hzero_right hassoc hx hy hxy

  have h2 : P2 F (x, y) = (Φ F (F x y)).comp (ω F y) := by
    have := congrArg (fun T : E →L[ℂ] E => T.comp (ω F y)) h
    simp only [ContinuousLinearMap.comp_assoc] at this
    rw [show (Φ F y).comp (ω F y) = 1 from Φ_mul_ω huy] at this
    exact this
  rw [h2, ← ContinuousLinearMap.comp_assoc, show (ω F (F x y)).comp (Φ F (F x y)) = 1 from ω_mul_Φ huxy]
  simp [ContinuousLinearMap.one_def]

end assoc

section symmetry

variable {F : E → E → E} {ρ : ℝ}

def Ψr : (E × E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (E × E) E).flip (ContinuousLinearMap.inr ℂ E E)

def Ψl : (E × E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (E × E) E).flip (ContinuousLinearMap.inl ℂ E E)

/--
@isnad1 id=eq.0h2v.s10.ddf6808413d1 from=translated src=- shape=2a647234 vocab=5f7b1850
-/
@[scoped simp] theorem Ψr_apply (L : E × E →L[ℂ] E) : Ψr L = L.comp (ContinuousLinearMap.inr ℂ E E) := by
  simp [Ψr]

/--
@isnad1 id=eq.0h2v.s10.fff471c56467 from=translated src=- shape=2a647234 vocab=b3121af1
-/
@[scoped simp] theorem Ψl_apply (L : E × E →L[ℂ] E) : Ψl L = L.comp (ContinuousLinearMap.inl ℂ E E) := by
  simp [Ψl]

/--
@isnad1 id=eq.0h3v.s10.4391801a2d79 from=translated src=- shape=e1fb7365 vocab=c4d062ae
-/
theorem Φ_eq_Ψr (u : E) : Φ F u = Ψr (D1 F (u, 0)) := by simp [Φ, P2]

/--
@isnad1 id=eq.0h3v.s10.0f288b906ffe from=translated src=- shape=3c8eaaa9 vocab=6abf81d3
-/
theorem P1_eq_Ψl (p : E × E) : P1 F p = Ψl (D1 F p) := by simp [P1]

/--
@isnad1 id=eq.2h6v.s11.384460b90189 from=translated src=- shape=066adfb5 vocab=f78d694c
-/
theorem D2_symm (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {p : E × E} (hp : p ∈ S ρ) (v w : E × E) :
    D2 F p v w = D2 F p w v := by
  have hf : ∀ᶠ q in 𝓝 p, HasFDerivAt (uc F) (D1 F q) q := by
    filter_upwards [(isOpen_S ρ).mem_nhds hp] with q hq
    exact hasFDerivAt_uc hF2 hq
  exact second_derivative_symmetric_of_eventually hf (hasFDerivAt_D1 hF2 hp) v w

/--
@isnad1 id=eq.4h4v.s8.a19dc844f1af from=translated src=- shape=6e2851d0 vocab=4f336d84
-/
theorem Φ_eq_P1 (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    {u : E} (hu : u ∈ ball (0 : E) ρ) : Φ F u = P1 F (0, u) := by
  have h1 : HasFDerivAt (fun y => F u y) (Φ F u) 0 := hasFDerivAt_right hF2 hu (zero_mem_ball hρ)
  have h2 : HasFDerivAt (fun y => F y u) (P1 F (0, u)) 0 := hasFDerivAt_left hF2 (zero_mem_ball hρ) hu
  have h3 : HasFDerivAt (fun y => F y u) (Φ F u) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) hρ] with y hy
    exact (hcomm u y hu hy).symm
  exact h3.unique h2

/--
@isnad1 id=hasfderi.2h3v.s10.f7135db7efc5 from=translated src=- shape=9a01dd94 vocab=066b750d
-/
theorem hasFDerivAt_Φ_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) :
    HasFDerivAt (Φ F) (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E))) 0 := by
  have hc : HasFDerivAt (fun u : E => D1 F (u, 0)) ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E)) 0 :=
    HasFDerivAt.comp (f := fun u : E => (u, (0 : E))) 0
      (hasFDerivAt_D1 hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)))
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) (0 : E) (0 : E))
  have h := (Ψr (E := E)).hasFDerivAt.comp 0 hc
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  show Φ F u = Ψr (D1 F (u, 0))
  exact Φ_eq_Ψr u

/--
@isnad1 id=hasfderi.3h3v.s10.a135c933ca9c from=translated src=- shape=27dfacd5 vocab=a86c06c4
-/
theorem hasFDerivAt_Φ_zero' (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v) :
    HasFDerivAt (Φ F) (Ψl.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inr ℂ E E))) 0 := by
  have hc : HasFDerivAt (fun u : E => D1 F (0, u)) ((D2 F (0, 0)).comp (ContinuousLinearMap.inr ℂ E E)) 0 :=
    HasFDerivAt.comp (f := fun u : E => ((0 : E), u)) 0
      (hasFDerivAt_D1 hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)))
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0 : E) (0 : E))
  have h := (Ψl (E := E)).hasFDerivAt.comp 0 hc
  have h' : HasFDerivAt (fun u : E => P1 F (0, u))
      (Ψl.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inr ℂ E E))) 0 := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show P1 F (0, u) = Ψl (D1 F (0, u))
    exact P1_eq_Ψl (0, u)
  refine h'.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds (0 : E) hρ] with u hu
  exact Φ_eq_P1 hρ hF2 hcomm hu

/--
@isnad1 id=eq.3h5v.s12.1b70c15dde5a from=translated src=- shape=7f194e0b vocab=d5f4e665
-/
theorem DΦ_zero_symm (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v) (a b : E) :
    (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E))) a b =
      (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E))) b a := by
  have heq := (hasFDerivAt_Φ_zero hρ hF2).unique (hasFDerivAt_Φ_zero' hρ hF2 hcomm)
  conv_lhs => rw [heq]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Ψr_apply, Ψl_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  exact D2_symm hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)) _ _

/--
@isnad1 id=hasfderi.3h3v.s16.a098c6e97179 from=translated src=- shape=7eee2239 vocab=c8c4400f
-/
theorem hasFDerivAt_ω_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) :
    HasFDerivAt (ω F) ((-ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) 1 1).comp
      (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E)))) 0 := by
  have hinv : HasFDerivAt (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E))
      (-ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) 1 1) (Φ F 0) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℂ) (1 : (E →L[ℂ] E)ˣ)
    rw [Φ_zero hρ hF2 hzero_left]
    simpa using this
  exact hinv.comp 0 (hasFDerivAt_Φ_zero hρ hF2)

/--
@isnad1 id=eq.7h6v.s10.0ec02d8475ff from=translated src=- shape=49e1cc70 vocab=6123312c
-/
theorem ω'_zero_symm (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v)
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    {r₀ : ℝ} (hr₀p : 0 < r₀) (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) (a b : E) :
    ω' F 0 a b = ω' F 0 b a := by
  have heq := (hasFDerivAt_ω hF2 hr₀ hunit (zero_mem_ball hr₀p)).unique
    (hasFDerivAt_ω_zero hρ hF2 hzero_left)
  rw [heq]
  have hs := DΦ_zero_symm hρ hF2 hcomm a b
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one] at hs ⊢
  rw [hs]

/--
@isnad1 id=eq.8h7v.s11.20a6e8da84fa from=translated src=- shape=00298f73 vocab=daf1b147
-/
theorem key_identity (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {r₀ : ℝ} (hr₀p : 0 < r₀) (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u))
    {x : E} (hx : x ∈ ball (0 : E) r₀) (a b : E) :
    ω F x (D2 F (x, 0) (0, a) (0, b)) + ω' F x (Φ F x a) (Φ F x b) = ω' F 0 a b := by
  have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hr₀ hx

  have hω : HasFDerivAt (ω F) (ω' F x) (F x 0) := by
    rw [hzero_right x hxρ]; exact hasFDerivAt_ω hF2 hr₀ hunit hx
  have hc : HasFDerivAt (fun y => ω F (F x y)) ((ω' F x).comp (Φ F x)) 0 :=
    hω.comp 0 (hasFDerivAt_right hF2 hxρ (zero_mem_ball hρ))

  have hd0 : HasFDerivAt (fun y : E => D1 F (x, y)) ((D2 F (x, 0)).comp (ContinuousLinearMap.inr ℂ E E)) 0 :=
    HasFDerivAt.comp (f := fun y : E => (x, y)) 0
      (hasFDerivAt_D1 hF2 (mem_S hxρ (zero_mem_ball hρ)))
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) x (0 : E))
  have hd1 := (Ψr (E := E)).hasFDerivAt.comp 0 hd0
  have hd : HasFDerivAt (fun y : E => P2 F (x, y))
      (Ψr.comp ((D2 F (x, 0)).comp (ContinuousLinearMap.inr ℂ E E))) 0 := by
    refine hd1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show P2 F (x, y) = Ψr (D1 F (x, y))
    simp [P2]

  have hG := hc.clm_comp hd

  have hev : ∀ᶠ y in 𝓝 (0 : E), (ω F (F x y)).comp (P2 F (x, y)) = ω F y := by
    have h1 : ∀ᶠ y in 𝓝 (0 : E), y ∈ ball (0 : E) r₀ := ball_mem_nhds _ hr₀p
    have h2 : ∀ᶠ y in 𝓝 (0 : E), F x y ∈ ball (0 : E) r₀ := by
      have hcont : ContinuousAt (fun y => F x y) 0 :=
        (hasFDerivAt_right hF2 hxρ (zero_mem_ball hρ)).continuousAt
      have : F x 0 ∈ ball (0 : E) r₀ := by rw [hzero_right x hxρ]; exact hx
      exact hcont.preimage_mem_nhds (isOpen_ball.mem_nhds this)
    filter_upwards [h1, h2] with y hy hxy
    exact ω_comp_P2 hρ hF2 hzero_right hassoc hxρ (ball_subset_ball hr₀ hy)
      (ball_subset_ball hr₀ hxy) (hunit y hy) (hunit _ hxy)
  have hG' : HasFDerivAt (fun y => (ω F (F x y)).comp (P2 F (x, y))) (ω' F 0) 0 :=
    (hasFDerivAt_ω hF2 hr₀ hunit (zero_mem_ball hr₀p)).congr_of_eventuallyEq hev
  have heq := hG.unique hG'
  have key := congrArg (fun T : E →L[ℂ] (E →L[ℂ] E) => T a b) heq
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, Ψr_apply,
    ContinuousLinearMap.inr_apply, hzero_right x hxρ] at key

  simpa [Φ] using key

/--
@isnad1 id=eq.10h7v.s11.6af89fb4cade from=translated src=- shape=3c7ce2dd vocab=6123312c
-/
theorem ω'_symm (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {r₀ : ℝ} (hr₀p : 0 < r₀) (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u))
    {x : E} (hx : x ∈ ball (0 : E) r₀) (a b : E) :
    ω' F x a b = ω' F x b a := by
  have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hr₀ hx

  have main : ∀ a₀ b₀ : E, ω' F x (Φ F x a₀) (Φ F x b₀) = ω' F x (Φ F x b₀) (Φ F x a₀) := by
    intro a₀ b₀
    have k1 := key_identity hρ hF2 hzero_right hassoc hr₀p hr₀ hunit hx a₀ b₀
    have k2 := key_identity hρ hF2 hzero_right hassoc hr₀p hr₀ hunit hx b₀ a₀
    have s1 : D2 F (x, 0) (0, a₀) (0, b₀) = D2 F (x, 0) (0, b₀) (0, a₀) :=
      D2_symm hF2 (mem_S hxρ (zero_mem_ball hρ)) _ _
    have s2 := ω'_zero_symm hρ hF2 hzero_left hcomm hr₀p hr₀ hunit a₀ b₀
    rw [s1, s2] at k1
    have e1 := eq_sub_of_add_eq' k1
    have e2 := eq_sub_of_add_eq' k2
    rw [e1, e2]
  have ha : Φ F x (ω F x a) = a := Φ_ω_apply (hunit x hx) a
  have hb : Φ F x (ω F x b) = b := Φ_ω_apply (hunit x hx) b
  have := main (ω F x a) (ω F x b)
  rwa [ha, hb] at this

end symmetry

section poincare

/--
@isnad1 id=mem.2h4v.s7.22ee414b66b5 from=translated src=- shape=db504fa9 vocab=cc62ca32
-/
theorem seg_mem {R : ℝ} {y : E} (hy : y ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    (t : ℂ) • y ∈ ball (0 : E) R := by
  rw [mem_ball_zero_iff] at hy ⊢
  calc ‖(t : ℂ) • y‖ = |t| * ‖y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖y‖ := by gcongr
    _ < R := by simpa using hy

/--
@isnad1 id=le.1h1v.s5.541ab9c92640 from=translated src=- shape=7d05db34 vocab=9f289bf6
-/
theorem abs_le_one_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [ht.1], ht.2⟩

/--
@isnad1 id=le.1h1v.s5.5a8814ca1096 from=translated src=- shape=7d05db34 vocab=e4db74ae
-/
theorem abs_le_one_of_mem_uIoc {t : ℝ} (ht : t ∈ uIoc (0 : ℝ) 1) : |t| ≤ 1 := by
  rw [uIoc_of_le zero_le_one] at ht
  exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩

def lineInt (w : E → (E →L[ℂ] E)) (x : E) : E := ∫ t in (0 : ℝ)..1, w ((t : ℂ) • x) x

/--
@isnad1 id=eq.0h2v.s6.3ef9bb6173d8 from=translated src=- shape=72385130 vocab=6c56b690
-/
theorem lineInt_zero (w : E → (E →L[ℂ] E)) : lineInt w 0 = 0 := by
  simp [lineInt]

def lineInt' (w : E → (E →L[ℂ] E)) (w' : E → (E →L[ℂ] (E →L[ℂ] E))) (y : E) (t : ℝ) : E →L[ℂ] E :=
  (w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E) +
    ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y

/--
@isnad1 id=continuo.0h3v.s6.6a79af0b351b from=translated src=- shape=23365565 vocab=9000e744
-/
theorem continuousOn_path (y : E) (s : Set ℝ) : ContinuousOn (fun t : ℝ => (t : ℂ) • y) s :=
  (Complex.continuous_ofReal.smul continuous_const).continuousOn

/--
@isnad1 id=mapsto.1h3v.s7.1e7277062013 from=translated src=- shape=ab5dc180 vocab=a43dd6d8
-/
theorem mapsTo_path {R : ℝ} {y : E} (hy : y ∈ ball (0 : E) R) :
    MapsTo (fun t : ℝ => (t : ℂ) • y) (Icc (0 : ℝ) 1) (ball (0 : E) R) :=
  fun _ ht => seg_mem hy (abs_le_one_of_mem_Icc ht)

/--
@isnad1 id=continuo.2h5v.s7.055b0160bd56 from=translated src=- shape=66624df5 vocab=67133929
-/
theorem continuousOn_comp_path {X : Type*} [TopologicalSpace X] {w : E → X} {R : ℝ}
    (hwc : ContinuousOn w (ball (0 : E) R)) {y : E} (hy : y ∈ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => w ((t : ℂ) • y)) (Icc (0 : ℝ) 1) :=
  hwc.comp (continuousOn_path y _) (mapsTo_path hy)

/--
@isnad1 id=continuo.2h4v.s8.4c138d196985 from=translated src=- shape=d85646a2 vocab=e218a205
-/
theorem continuousOn_lineInt_integrand {w : E → (E →L[ℂ] E)} {R : ℝ}
    (hwc : ContinuousOn w (ball (0 : E) R)) {y : E} (hy : y ∈ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => w ((t : ℂ) • y) y) (Icc (0 : ℝ) 1) :=
  (continuousOn_comp_path hwc hy).clm_apply continuousOn_const

/--
@isnad1 id=continuo.3h5v.s10.31fe0582f385 from=translated src=- shape=63d69a9d vocab=5a8aef8c
-/
theorem continuousOn_lineInt' {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))} {R : ℝ}
    (hwc : ContinuousOn w (ball (0 : E) R)) (hw'c : ContinuousOn w' (ball (0 : E) R))
    {y : E} (hy : y ∈ ball (0 : E) R) :
    ContinuousOn (lineInt' w w' y) (Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)) (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path hwc hy).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun t : ℝ => (w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E))
      (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path hw'c hy).clm_comp
      ((Complex.continuous_ofReal.smul continuous_const).continuousOn)
  have h3 : ContinuousOn (fun t : ℝ =>
      ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y) (Icc (0 : ℝ) 1) := by
    have hflip : ContinuousOn (fun t : ℝ =>
        ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip) (Icc (0 : ℝ) 1) :=
      (ContinuousLinearMap.flipₗᵢ ℂ E E E).continuous.comp_continuousOn h2
    exact hflip.clm_apply continuousOn_const
  exact h1.add h3

/--
@isnad1 id=hasfderi.3h6v.s9.1c7bc607d66b from=translated src=- shape=e60c0931 vocab=0cc60769
-/
theorem hasFDerivAt_lineInt_integrand {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    {y : E} (hy : y ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    HasFDerivAt (fun y' : E => w ((t : ℂ) • y') y') (lineInt' w w' y t) y := by
  have hpath : HasFDerivAt (fun y' : E => (t : ℂ) • y') ((t : ℂ) • ContinuousLinearMap.id ℂ E) y :=
    (hasFDerivAt_id y).const_smul (t : ℂ)
  have hc : HasFDerivAt (fun y' : E => w ((t : ℂ) • y'))
      ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)) y :=
    HasFDerivAt.comp (f := fun y' : E => (t : ℂ) • y') y (hw _ (seg_mem hy ht)) hpath
  exact hc.clm_apply (hasFDerivAt_id y)

/--
@isnad1 id=le.4h7v.s10.eee9189b82f6 from=translated src=- shape=527f70ac vocab=8f0b6f33
-/
theorem norm_lineInt'_le {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R C : ℝ} (hbw : ∀ u ∈ ball (0 : E) R, ‖w u‖ ≤ C) (hbw' : ∀ u ∈ ball (0 : E) R, ‖w' u‖ ≤ C)
    {y : E} (hy : y ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    ‖lineInt' w w' y t‖ ≤ C + C * R := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbw y hy)
  have hmem := seg_mem hy ht
  have hyR : ‖y‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hy)
  have h1 : ‖(w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)‖ ≤ C := by
    calc ‖(w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)‖
        ≤ ‖w ((t : ℂ) • y)‖ * ‖ContinuousLinearMap.id ℂ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by gcongr; exacts [hbw _ hmem, ContinuousLinearMap.norm_id_le]
      _ = C := mul_one C
  have ht1 : ‖(t : ℂ) • ContinuousLinearMap.id ℂ E‖ ≤ 1 := by
    calc ‖(t : ℂ) • ContinuousLinearMap.id ℂ E‖ = ‖(t : ℂ)‖ * ‖ContinuousLinearMap.id ℂ E‖ := norm_smul _ _
      _ ≤ 1 * 1 := by
          gcongr
          · rw [Complex.norm_real, Real.norm_eq_abs]; exact ht
          · exact ContinuousLinearMap.norm_id_le
      _ = 1 := one_mul 1
  have h2 : ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y‖ ≤ C * R := by
    calc ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y‖
        ≤ ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)‖ * ‖y‖ := by
          rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖w' ((t : ℂ) • y)‖ * ‖(t : ℂ) • ContinuousLinearMap.id ℂ E‖) * ‖y‖ := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * 1) * R := by gcongr; exact hbw' _ hmem
      _ = C * R := by ring
  calc ‖lineInt' w w' y t‖ ≤ ‖(w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)‖ +
        ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y‖ := norm_add_le _ _
    _ ≤ C + C * R := add_le_add h1 h2

/--
@isnad1 id=hasfderi.6h6v.s11.55bc9703a3b1 from=translated src=- shape=d380665d vocab=b3db6520
-/
theorem hasFDerivAt_lineInt_aux {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R C : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    (hwc : ContinuousOn w (ball (0 : E) R)) (hw'c : ContinuousOn w' (ball (0 : E) R))
    (hbw : ∀ u ∈ ball (0 : E) R, ‖w u‖ ≤ C) (hbw' : ∀ u ∈ ball (0 : E) R, ‖w' u‖ ≤ C)
    {x : E} (hx : x ∈ ball (0 : E) R) :
    HasFDerivAt (lineInt w) (∫ t in (0 : ℝ)..1, lineInt' w w' x t) x := by

  set ε : ℝ := R - ‖x‖ with hε
  have hεpos : 0 < ε := by have := mem_ball_zero_iff.mp hx; linarith
  have hsub : ball x ε ⊆ ball (0 : E) R := by
    intro y hy
    rw [mem_ball_zero_iff]
    have h1 : ‖y - x‖ < ε := by simpa [dist_eq_norm] using hy
    calc ‖y‖ = ‖(y - x) + x‖ := by abel_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ < ε + ‖x‖ := by linarith
      _ = R := by simp [hε]
  have hs : ball x ε ∈ 𝓝 x := ball_mem_nhds x hεpos
  have hIcc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨le_of_lt ht.1, ht.2⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := MeasureTheory.volume) (F := fun y t => w ((t : ℂ) • y) y) (F' := lineInt' w w')
    (bound := fun _ => C + C * R) hs ?_ ?_ ?_ ?_ ?_ ?_
  ·
    filter_upwards [hs] with y hy
    exact ((continuousOn_lineInt_integrand hwc (hsub hy)).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  ·
    exact ((continuousOn_lineInt_integrand hwc hx).mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  ·
    exact ((continuousOn_lineInt' hwc hw'c hx).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  ·
    refine Filter.Eventually.of_forall fun t ht y hy => ?_
    exact norm_lineInt'_le hbw hbw' (hsub hy) (abs_le_one_of_mem_uIoc ht)
  · exact intervalIntegrable_const
  ·
    refine Filter.Eventually.of_forall fun t ht y hy => ?_
    exact hasFDerivAt_lineInt_integrand hw (hsub hy) (abs_le_one_of_mem_uIoc ht)

/--
@isnad1 id=hasderiv.3h6v.s11.4f8cd57ad772 from=translated src=- shape=fbd1e6f4 vocab=7b72c6c9
-/
theorem hasDerivAt_primitive {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    {x : E} (hx : x ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    HasDerivAt (fun s : ℝ => (s : ℂ) • w ((s : ℂ) • x))
      ((t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x)) t := by
  have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hpath : HasDerivAt (fun s : ℝ => (s : ℂ) • x) x t := by
    simpa using hc.smul_const x
  have hwt : HasFDerivAt w ((w' ((t : ℂ) • x)).restrictScalars ℝ) ((t : ℂ) • x) :=
    (hw _ (seg_mem hx ht)).restrictScalars ℝ
  have hf : HasDerivAt (fun s : ℝ => w ((s : ℂ) • x)) (w' ((t : ℂ) • x) x) t := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s : ℂ) • x) t hwt hpath
    simp at this
    exact this
  exact hc.smul hf

/--
@isnad1 id=eq.3h6v.s11.ca4a48782268 from=translated src=- shape=a6a60925 vocab=9cb55dc6
-/
theorem lineInt'_eq_of_symm {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R : ℝ} (hsymm : ∀ u ∈ ball (0 : E) R, ∀ a b : E, w' u a b = w' u b a)
    {x : E} (hx : x ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    lineInt' w w' x t = (t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x) := by
  ext a
  have hs := hsymm _ (seg_mem hx ht) a x
  simp only [lineInt', add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, smul_apply,
    FunLike.coe_smul, Pi.smul_apply, one_smul, map_smul]
  rw [hs, add_comm]

/--
@isnad1 id=hasfderi.7h6v.s11.420e44dd4882 from=translated src=- shape=6fd51833 vocab=c9857729
-/
theorem hasFDerivAt_lineInt {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R C : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    (hwc : ContinuousOn w (ball (0 : E) R)) (hw'c : ContinuousOn w' (ball (0 : E) R))
    (hbw : ∀ u ∈ ball (0 : E) R, ‖w u‖ ≤ C) (hbw' : ∀ u ∈ ball (0 : E) R, ‖w' u‖ ≤ C)
    (hsymm : ∀ u ∈ ball (0 : E) R, ∀ a b : E, w' u a b = w' u b a)
    {x : E} (hx : x ∈ ball (0 : E) R) :
    HasFDerivAt (lineInt w) (w x) x := by
  have h := hasFDerivAt_lineInt_aux hw hwc hw'c hbw hbw' hx
  have hI : ∫ t in (0 : ℝ)..1, lineInt' w w' x t = w x := by
    have hcongr : ∫ t in (0 : ℝ)..1, lineInt' w w' x t =
        ∫ t in (0 : ℝ)..1, ((t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      exact lineInt'_eq_of_symm hsymm hx (abs_le_one_of_mem_Icc ht)
    rw [hcongr]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (s : ℂ) • w ((s : ℂ) • x))
        ((t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact hasDerivAt_primitive hw hx (abs_le_one_of_mem_Icc ht)
    have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x))
        MeasureTheory.volume 0 1 := by
      refine (ContinuousOn.intervalIntegrable ?_)
      rw [uIcc_of_le zero_le_one]
      refine ContinuousOn.fun_add ?_ ?_
      · exact Complex.continuous_ofReal.continuousOn.fun_smul
          ((continuousOn_comp_path hw'c hx).clm_apply continuousOn_const)
      · exact continuousOn_const.fun_smul (continuousOn_comp_path hwc hx)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  rw [hI] at h
  exact h

end poincare

section logadd

variable {F : E → E → E} {ρ : ℝ}

/--
@isnad1 id=eq.14h9v.s9.564f2fac175f from=translated src=- shape=574057d2 vocab=6db96fa8
-/
theorem log_add (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {r₀ : ℝ} (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u))
    {R : ℝ} (hRp : 0 < R) (hRr₀ : R ≤ r₀)
    {log : E → E} (hlog : ∀ x ∈ ball (0 : E) R, HasFDerivAt log (ω F x) x) (hlog0 : log 0 = 0)
    {a : ℝ} (hap : 0 < a)
    (hamul : ∀ x y : E, x ∈ ball (0 : E) a → y ∈ ball (0 : E) a → F x y ∈ ball (0 : E) R)
    {x y : E} (hx : x ∈ ball (0 : E) (min a R)) (hy : y ∈ ball (0 : E) (min a R)) :
    log (F x y) = log x + log y := by
  have hRρ : R ≤ ρ := le_trans hRr₀ hr₀
  have hsubR : ball (0 : E) R ⊆ ball (0 : E) r₀ := ball_subset_ball hRr₀
  have haR : ∀ {x : E}, x ∈ ball (0 : E) (min a R) → x ∈ ball (0 : E) R := fun hx =>
    ball_subset_ball (min_le_right _ _) hx
  have haa : ∀ {x : E}, x ∈ ball (0 : E) (min a R) → x ∈ ball (0 : E) a := fun hx =>
    ball_subset_ball (min_le_left _ _) hx
  have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hRρ (haR hx)
  have hderiv : ∀ z ∈ ball (0 : E) (min a R),
      HasFDerivAt (fun z => log (F x z) - log z) (0 : E →L[ℂ] E) z := by
    intro z hz
    have hzρ : z ∈ ball (0 : E) ρ := ball_subset_ball hRρ (haR hz)
    have hxz : F x z ∈ ball (0 : E) R := hamul x z (haa hx) (haa hz)
    have h1 : HasFDerivAt (fun z => log (F x z)) ((ω F (F x z)).comp (P2 F (x, z))) z :=
      HasFDerivAt.comp (f := fun z => F x z) z (hlog _ hxz) (hasFDerivAt_right hF2 hxρ hzρ)
    have h2 := h1.sub (hlog z (haR hz))
    rwa [ω_comp_P2 hρ hF2 hzero_right hassoc hxρ hzρ (ball_subset_ball hRρ hxz)
      (hunit z (hsubR (haR hz))) (hunit _ (hsubR hxz)), sub_self] at h2
  have hconst := (convex_ball (0 : E) (min a R)).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
    (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by
      rw [fderivWithin_of_isOpen isOpen_ball hz]
      exact (hderiv z hz).fderiv)
    hy (mem_ball_self (lt_min hap hRp))
  simp only [hzero_right x hxρ, hlog0, sub_zero] at hconst
  rw [← hconst]; abel

end logadd

end LocalGroupLawK3b
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b

namespace LocalGroupLawB1

open LocalGroupLawK3b

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def F3 (F : P → E → E → E) : P × (E × E) → E := fun q => F q.1 q.2.1 q.2.2

def N (z₀ : P) (σ ρ : ℝ) : Set (P × (E × E)) := ball z₀ σ ×ˢ S ρ

/--
@isnad1 id=isopen.0h5v.s6.0a242fe70714 from=translated src=- shape=f5452e24 vocab=374019de
-/
theorem isOpen_N (z₀ : P) (σ ρ : ℝ) : IsOpen (N (E := E) z₀ σ ρ) := isOpen_ball.prod (isOpen_S ρ)

/--
@isnad1 id=ex.1h4v.s6.e3a1687103f1 from=translated src=- shape=1ad8c0b6 vocab=ab6141c0
-/
theorem exists_ball_norm_le' {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] {f : X → Y} {x₀ : X}
    (hf : ContinuousAt f x₀) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ball x₀ ε, ‖f x‖ ≤ ‖f x₀‖ + 1 := by
  have hev : ∀ᶠ x in 𝓝 x₀, f x ∈ ball (f x₀) 1 := hf.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun x hx => ?_⟩
  have h := hb x hx
  rw [mem_ball, dist_eq_norm] at h
  calc ‖f x‖ = ‖(f x - f x₀) + f x₀‖ := by abel_nf
    _ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_add_le _ _
    _ ≤ ‖f x₀‖ + 1 := by linarith

/--
@isnad1 id=mem.2h7v.s6.456fe4a96e85 from=translated src=- shape=851f88ff vocab=04c79cf7
-/
theorem mem_ball_prod {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {x₀ x : X} {y₀ y : Y}
    {ε : ℝ} (hx : x ∈ ball x₀ ε) (hy : y ∈ ball y₀ ε) : ((x, y) : X × Y) ∈ ball ((x₀, y₀) : X × Y) ε := by
  rw [mem_ball, Prod.dist_eq]
  exact max_lt hx hy

section fibre

variable {F : P → E → E → E} {z₀ : P} {σ ρ : ℝ}

/--
@isnad1 id=contdiff.2h7v.s7.f47940f2ec52 from=translated src=- shape=345e4b43 vocab=db892795
-/
theorem contDiffOn_fibre (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {z : P} (hz : z ∈ ball z₀ σ) :
    ContDiffOn ℂ 2 (uc (F z)) (S ρ) := by
  have h : ContDiffOn ℂ 2 (F3 F ∘ fun p : E × E => (z, p)) (S ρ) :=
    hF3.comp (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => ⟨hz, hp⟩)
  exact h

/--
@isnad1 id=eq.3h8v.s9.72e63f985da6 from=translated src=- shape=4250e2c5 vocab=613ad2b9
-/
theorem D1_fibre (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {z : P} (hz : z ∈ ball z₀ σ)
    {p : E × E} (hp : p ∈ S ρ) :
    D1 (F z) p = (fderiv ℂ (F3 F) (z, p)).comp (ContinuousLinearMap.inr ℂ P (E × E)) := by
  have h3 : HasFDerivAt (F3 F) (fderiv ℂ (F3 F) (z, p)) (z, p) :=
    ((hF3.differentiableOn (by norm_num)).differentiableAt ((isOpen_N z₀ σ ρ).mem_nhds ⟨hz, hp⟩)).hasFDerivAt
  have h : HasFDerivAt (uc (F z)) ((fderiv ℂ (F3 F) (z, p)).comp (ContinuousLinearMap.inr ℂ P (E × E))) p :=
    HasFDerivAt.comp (f := fun p : E × E => (z, p)) p h3 (hasFDerivAt_prodMk_right (𝕜 := ℂ) z p)
  exact h.fderiv

def Φt (F : P → E → E → E) (q : P × E) : E →L[ℂ] E := Φ (F q.1) q.2

def ωt (F : P → E → E → E) (q : P × E) : E →L[ℂ] E := ω (F q.1) q.2

def ωt' (F : P → E → E → E) (q : P × E) : E →L[ℂ] (E →L[ℂ] E) := ω' (F q.1) q.2

/--
@isnad1 id=eq.0h5v.s7.c758b4c7f9ad from=translated src=- shape=b778c350 vocab=3025a3ec
-/
@[scoped simp] theorem Φt_apply (F : P → E → E → E) (z : P) (u : E) : Φt F (z, u) = Φ (F z) u := rfl

/--
@isnad1 id=eq.3h7v.s11.a8cbf56a58bb from=translated src=- shape=43243967 vocab=ff323564
-/
theorem Φt_eq (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {q : P × E}
    (hq : q ∈ ball z₀ σ ×ˢ ball (0 : E) ρ) :
    Φt F q = Ψr ((fderiv ℂ (F3 F) (q.1, (q.2, 0))).comp (ContinuousLinearMap.inr ℂ P (E × E))) := by
  show Φ (F q.1) q.2 = _
  rw [Φ_eq_Ψr, D1_fibre hF3 hq.1 (mem_S hq.2 (zero_mem_ball hρ))]

/--
@isnad1 id=contdiff.2h6v.s8.397693fba511 from=translated src=- shape=5a250c78 vocab=c988f345
-/
theorem contDiffOn_Φt (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) :
    ContDiffOn ℂ 1 (Φt F) (ball z₀ σ ×ˢ ball (0 : E) ρ) := by
  have hD : ContDiffOn ℂ 1 (fderiv ℂ (F3 F)) (N z₀ σ ρ) :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 1) (f := F3 F) (isOpen_N z₀ σ ρ)).1
      (by rw [← two_eq]; exact hF3)).2.2
  have hι : ContDiffOn ℂ 1 (fun q : P × E => (q.1, (q.2, (0 : E)))) (ball z₀ σ ×ˢ ball (0 : E) ρ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const)
  have hmaps : MapsTo (fun q : P × E => (q.1, (q.2, (0 : E)))) (ball z₀ σ ×ˢ ball (0 : E) ρ) (N z₀ σ ρ) :=
    fun q hq => ⟨hq.1, mem_S hq.2 (zero_mem_ball hρ)⟩
  have h1 : ContDiffOn ℂ 1 (fun q : P × E => fderiv ℂ (F3 F) (q.1, (q.2, (0 : E)))) (ball z₀ σ ×ˢ ball (0 : E) ρ) :=
    hD.comp hι hmaps
  have h2 : ContDiffOn ℂ 1 (fun q : P × E =>
      Ψr ((fderiv ℂ (F3 F) (q.1, (q.2, (0 : E)))).comp (ContinuousLinearMap.inr ℂ P (E × E))))
      (ball z₀ σ ×ˢ ball (0 : E) ρ) :=
    (Ψr (E := E)).contDiff.comp_contDiffOn (h1.clm_comp contDiffOn_const)
  exact h2.congr (fun q hq => Φt_eq hρ hF3 hq)

/--
@isnad1 id=ex.4h6v.s8.789cdcafd48b from=translated src=- shape=67212483 vocab=5b396827
-/
theorem exists_uniform_units (hσ : 0 < σ) (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ))
    (hzero_left : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z 0 v = v) :
    ∃ σ₁ r₀ : ℝ, 0 < σ₁ ∧ σ₁ ≤ σ ∧ 0 < r₀ ∧ r₀ ≤ ρ ∧
      ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u) := by
  have hc : ContinuousAt (Φt F) (z₀, 0) :=
    (contDiffOn_Φt hρ hF3).continuousOn.continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hσ, mem_ball_self hρ⟩)
  have h0 : Φt F (z₀, 0) = 1 := by
    rw [Φt_apply]
    exact Φ_zero hρ (contDiffOn_fibre hF3 (mem_ball_self hσ)) (hzero_left z₀ (mem_ball_self hσ))
  have hev : ∀ᶠ q in 𝓝 ((z₀, (0 : E)) : P × E), ‖Φt F q - 1‖ < 1 := by
    have : ∀ᶠ q in 𝓝 ((z₀, (0 : E)) : P × E), Φt F q ∈ ball (Φt F (z₀, 0)) 1 :=
      hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
    filter_upwards [this] with q hq
    rw [h0] at hq
    simpa [dist_eq_norm] using hq
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε σ, min ε ρ, lt_min hε hσ, min_le_right _ _, lt_min hε hρ, min_le_right _ _,
    fun z hz u hu => ?_⟩
  have hq : ((z, u) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε :=
    mem_ball_prod (ball_subset_ball (min_le_left _ _) hz) (ball_subset_ball (min_le_left _ _) hu)
  have hb' := hb _ hq
  rw [Φt_apply] at hb'
  exact isUnit_of_norm_sub_one_lt hb'

/--
@isnad1 id=contdiff.5h8v.s9.1515ed8de70c from=translated src=- shape=d54a4b8c vocab=8930f1af
-/
theorem contDiffOn_ωt (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {σ₁ r₀ : ℝ}
    (hσ₁ : σ₁ ≤ σ) (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u)) :
    ContDiffOn ℂ 1 (ωt F) (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := by
  intro q hq
  have hq' : q ∈ ball z₀ σ ×ˢ ball (0 : E) ρ := ⟨ball_subset_ball hσ₁ hq.1, ball_subset_ball hr₀ hq.2⟩
  have hΦ : ContDiffAt ℂ 1 (Φt F) q :=
    (contDiffOn_Φt hρ hF3).contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds hq')
  have hinv : ContDiffAt ℂ 1 Ring.inverse (Φt F q) := by
    have := contDiffAt_ringInverse ℂ (n := 1) (hunit q.1 hq.1 q.2 hq.2).unit
    rwa [IsUnit.unit_spec] at this
  exact (hinv.comp q hΦ).contDiffWithinAt

/--
@isnad1 id=eq.6h9v.s10.ea2c2ff6d4c9 from=translated src=- shape=83e367b5 vocab=de2f0ca9
-/
theorem ωt'_eq (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {σ₁ r₀ : ℝ}
    (hσ₁ : σ₁ ≤ σ) (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u))
    {q : P × E} (hq : q ∈ ball z₀ σ₁ ×ˢ ball (0 : E) r₀) :
    ωt' F q = (fderiv ℂ (ωt F) q).comp (ContinuousLinearMap.inr ℂ P E) := by
  have hd : HasFDerivAt (ωt F) (fderiv ℂ (ωt F) q) q :=
    (((contDiffOn_ωt hρ hF3 hσ₁ hr₀ hunit).differentiableOn one_ne_zero).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hq)).hasFDerivAt
  have h : HasFDerivAt (ω (F q.1)) ((fderiv ℂ (ωt F) q).comp (ContinuousLinearMap.inr ℂ P E)) q.2 :=
    HasFDerivAt.comp (f := fun u : E => (q.1, u)) q.2 hd (hasFDerivAt_prodMk_right (𝕜 := ℂ) q.1 q.2)
  exact h.fderiv

/--
@isnad1 id=continuo.5h8v.s9.8fb467334d75 from=translated src=- shape=42e833c7 vocab=515adf7d
-/
theorem continuousOn_ωt' (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {σ₁ r₀ : ℝ}
    (hσ₁ : σ₁ ≤ σ) (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u)) :
    ContinuousOn (ωt' F) (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := by
  have h : ContinuousOn (fun q : P × E => (fderiv ℂ (ωt F) q).comp (ContinuousLinearMap.inr ℂ P E))
      (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) :=
    ((contDiffOn_ωt hρ hF3 hσ₁ hr₀ hunit).continuousOn_fderiv_of_isOpen (isOpen_ball.prod isOpen_ball)
      le_rfl).clm_comp continuousOn_const
  exact h.congr (fun q hq => ωt'_eq hρ hF3 hσ₁ hr₀ hunit hq)

end fibre
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b

section paramlog

variable {z₀ : P} {σ₂ R : ℝ}

def πt (t : ℝ) : P × E →L[ℂ] P × E :=
  (ContinuousLinearMap.fst ℂ P E).prod (0 : P × E →L[ℂ] E) +
    (t : ℂ) • ((0 : P × E →L[ℂ] P).prod (ContinuousLinearMap.snd ℂ P E))

/--
@isnad1 id=eq.0h4v.s8.e757a322b2b1 from=translated src=- shape=628ff7fe vocab=14a20828
-/
@[scoped simp] theorem πt_apply (t : ℝ) (q : P × E) : πt t q = (q.1, (t : ℂ) • q.2) := by
  simp [πt]

/--
@isnad1 id=continuo.0h2v.s8.21a19620dcde from=translated src=- shape=637583b4 vocab=ed77599c
-/
theorem continuous_πt : Continuous (fun t : ℝ => (πt t : P × E →L[ℂ] P × E)) :=
  continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

/--
@isnad1 id=le.1h3v.s8.03901e01a362 from=translated src=- shape=fa6b7263 vocab=f4cf0d65
-/
theorem norm_πt_le {t : ℝ} (ht : |t| ≤ 1) : ‖(πt t : P × E →L[ℂ] P × E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q => ?_)
  rw [πt_apply, one_mul, Prod.norm_def, Prod.norm_def]
  apply max_le_max le_rfl
  calc ‖(t : ℂ) • q.2‖ = |t| * ‖q.2‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖q.2‖ := by gcongr
    _ = ‖q.2‖ := one_mul _

/--
@isnad1 id=le.0h2v.s7.d9a199496348 from=translated src=- shape=bbcf685c vocab=2bcd9268
-/
theorem norm_sndL_le : ‖(ContinuousLinearMap.snd ℂ P E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_snd_le x)

/--
@isnad1 id=mem.2h7v.s8.4d6c470209ee from=translated src=- shape=62f8b273 vocab=3b5f80c8
-/
theorem seg_mem_prod {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    ((q.1, (t : ℂ) • q.2) : P × E) ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R :=
  ⟨hq.1, seg_mem hq.2 ht⟩

def LOG (W : P × E → (E →L[ℂ] E)) (q : P × E) : E := lineInt (fun x => W (q.1, x)) q.2

def LOG' (W : P × E → (E →L[ℂ] E)) (W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))) (q : P × E) (t : ℝ) :
    P × E →L[ℂ] E :=
  (W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E) +
    ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2

/--
@isnad1 id=continuo.0h4v.s7.0e470bbeabfc from=translated src=- shape=1fc1ad88 vocab=ac558ffa
-/
theorem continuousOn_path_prod (q : P × E) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => ((q.1, (t : ℂ) • q.2) : P × E)) s :=
  (continuous_const.prodMk (Complex.continuous_ofReal.smul continuous_const)).continuousOn

/--
@isnad1 id=continuo.2h8v.s8.780cf8214199 from=translated src=- shape=ba521b0e vocab=07ff6eb4
-/
theorem continuousOn_comp_path_prod {X : Type*} [TopologicalSpace X] {W : P × E → X}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => W (q.1, (t : ℂ) • q.2)) (Icc (0 : ℝ) 1) :=
  hWc.comp (continuousOn_path_prod q _) (fun _ ht => seg_mem_prod hq (abs_le_one_of_mem_Icc ht))

/--
@isnad1 id=continuo.2h7v.s9.5b038e434fc0 from=translated src=- shape=6dc13f8a vocab=fd5c9175
-/
theorem continuousOn_LOG_integrand {W : P × E → (E →L[ℂ] E)}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => W (q.1, (t : ℂ) • q.2) q.2) (Icc (0 : ℝ) 1) :=
  (continuousOn_comp_path_prod hWc hq).clm_apply continuousOn_const

/--
@isnad1 id=continuo.3h8v.s10.45d249cbc9ff from=translated src=- shape=66eac0d6 vocab=998ef69a
-/
theorem continuousOn_LOG' {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousOn (LOG' W W' q) (Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)) (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path_prod hWc hq).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun t : ℝ => (W' (q.1, (t : ℂ) • q.2)).comp (πt t)) (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path_prod hW'c hq).clm_comp continuous_πt.continuousOn
  have h3 : ContinuousOn (fun t : ℝ => ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2) (Icc (0 : ℝ) 1) :=
    ((ContinuousLinearMap.flipₗᵢ ℂ (P × E) E E).continuous.comp_continuousOn h2).clm_apply continuousOn_const
  exact h1.add h3

/--
@isnad1 id=hasfderi.3h9v.s10.77f8493fc5de from=translated src=- shape=77f682ac vocab=8f4b6a03
-/
theorem hasFDerivAt_LOG_integrand {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    (hWd : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, HasFDerivAt W (W' q) q)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    HasFDerivAt (fun q' : P × E => W (q'.1, (t : ℂ) • q'.2) q'.2) (LOG' W W' q t) q := by
  have hpath : HasFDerivAt (fun q' : P × E => ((q'.1, (t : ℂ) • q'.2) : P × E)) (πt t) q := by
    have h := (hasFDerivAt_fst (𝕜 := ℂ) (p := q)).prodMk ((hasFDerivAt_snd (𝕜 := ℂ) (p := q)).const_smul (t : ℂ))
    refine h.congr_fderiv ?_
    ext q' <;> simp [πt]
  have hc : HasFDerivAt (fun q' : P × E => W (q'.1, (t : ℂ) • q'.2)) ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)) q :=
    HasFDerivAt.comp (f := fun q' : P × E => ((q'.1, (t : ℂ) • q'.2) : P × E)) q (hWd _ (seg_mem_prod hq ht)) hpath
  exact hc.clm_apply (hasFDerivAt_snd (𝕜 := ℂ) (p := q))

/--
@isnad1 id=le.4h10v.s10.8905e1dc1c05 from=translated src=- shape=e1a52fda vocab=318483bf
-/
theorem norm_LOG'_le {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))} {C : ℝ}
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W' q‖ ≤ C)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    ‖LOG' W W' q t‖ ≤ C + C * R := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbW q hq)
  have hmem := seg_mem_prod hq ht
  have hqR : ‖q.2‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hq.2)
  have h1 : ‖(W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)‖ ≤ C := by
    calc ‖(W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)‖
        ≤ ‖W (q.1, (t : ℂ) • q.2)‖ * ‖ContinuousLinearMap.snd ℂ P E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by gcongr; exacts [hbW _ hmem, norm_sndL_le]
      _ = C := mul_one C
  have h2 : ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2‖ ≤ C * R := by
    calc ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2‖
        ≤ ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip‖ * ‖q.2‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖(W' (q.1, (t : ℂ) • q.2)).comp (πt t)‖ * ‖q.2‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖W' (q.1, (t : ℂ) • q.2)‖ * ‖(πt t : P × E →L[ℂ] P × E)‖) * ‖q.2‖ := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * 1) * R := by gcongr; exacts [hbW' _ hmem, norm_πt_le ht]
      _ = C * R := by ring
  calc ‖LOG' W W' q t‖ ≤ ‖(W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)‖ +
        ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2‖ := norm_add_le _ _
    _ ≤ C + C * R := add_le_add h1 h2

/--
@isnad1 id=hasfderi.6h9v.s11.cd1355daaee6 from=translated src=- shape=cd0450f3 vocab=4657d3c8
-/
theorem hasFDerivAt_LOG {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))} {C : ℝ}
    (hWd : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, HasFDerivAt W (W' q) q)
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W' q‖ ≤ C)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    HasFDerivAt (LOG W) (∫ t in (0 : ℝ)..1, LOG' W W' q t) q := by
  obtain ⟨ε, hεpos, hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.prod isOpen_ball) q hq
  have hs : ball q ε ∈ 𝓝 q := ball_mem_nhds q hεpos
  have hIcc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨le_of_lt ht.1, ht.2⟩
  show HasFDerivAt (fun q' : P × E => ∫ t in (0 : ℝ)..1, W (q'.1, (t : ℂ) • q'.2) q'.2)
    (∫ t in (0 : ℝ)..1, LOG' W W' q t) q
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := MeasureTheory.volume) (F := fun (q' : P × E) t => W (q'.1, (t : ℂ) • q'.2) q'.2) (F' := LOG' W W')
    (bound := fun _ => C + C * R) hs ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs] with q' hq'
    exact ((continuousOn_LOG_integrand hWc (hsub hq')).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  · exact ((continuousOn_LOG_integrand hWc hq).mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  · exact ((continuousOn_LOG' hWc hW'c hq).mono (fun t ht => hIcc t ht)).aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall fun t ht q' hq' => ?_
    exact norm_LOG'_le hbW hbW' (hsub hq') (abs_le_one_of_mem_uIoc ht)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht q' hq' => ?_
    exact hasFDerivAt_LOG_integrand hWd (hsub hq') (abs_le_one_of_mem_uIoc ht)

/--
@isnad1 id=continuo.3h8v.s10.87862a2ecffb from=translated src=- shape=22295316 vocab=2fadbf81
-/
theorem continuousOn_LOG'_param {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    {t : ℝ} (ht : |t| ≤ 1) :
    ContinuousOn (fun q : P × E => LOG' W W' q t) (ball z₀ σ₂ ×ˢ ball (0 : E) R) := by
  have hp : ContinuousOn (fun q : P × E => ((q.1, (t : ℂ) • q.2) : P × E)) (ball z₀ σ₂ ×ˢ ball (0 : E) R) :=
    (continuous_fst.prodMk (continuous_snd.const_smul (t : ℂ))).continuousOn
  have hmaps : MapsTo (fun q : P × E => ((q.1, (t : ℂ) • q.2) : P × E)) (ball z₀ σ₂ ×ˢ ball (0 : E) R)
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) := fun q hq => seg_mem_prod hq ht
  have h1 : ContinuousOn (fun q : P × E => (W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E))
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) := (hWc.comp hp hmaps).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun q : P × E => (W' (q.1, (t : ℂ) • q.2)).comp (πt t))
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) := (hW'c.comp hp hmaps).clm_comp continuousOn_const
  have h3 : ContinuousOn (fun q : P × E => ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2)
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) :=
    ((ContinuousLinearMap.flipₗᵢ ℂ (P × E) E E).continuous.comp_continuousOn h2).clm_apply
      continuous_snd.continuousOn
  exact h1.add h3

/--
@isnad1 id=continuo.5h9v.s11.7b00b51316b7 from=translated src=- shape=750b617b vocab=364db489
-/
theorem continuousAt_LOG'_integral {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    {C : ℝ} (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W' q‖ ≤ C)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousAt (fun q' : P × E => ∫ t in (0 : ℝ)..1, LOG' W W' q' t) q := by
  obtain ⟨ε, hεpos, hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.prod isOpen_ball) q hq
  have hs : ball q ε ∈ 𝓝 q := ball_mem_nhds q hεpos
  have hIcc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨le_of_lt ht.1, ht.2⟩
  refine intervalIntegral.continuousAt_of_dominated_interval (μ := MeasureTheory.volume)
    (bound := fun _ => C + C * R) ?_ ?_ ?_ ?_
  · filter_upwards [hs] with q' hq'
    exact ((continuousOn_LOG' hWc hW'c (hsub hq')).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [hs] with q' hq'
    exact Filter.Eventually.of_forall fun t ht => norm_LOG'_le hbW hbW' (hsub hq') (abs_le_one_of_mem_uIoc ht)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    exact (continuousOn_LOG'_param hWc hW'c (abs_le_one_of_mem_uIoc ht)).continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hq)

/--
@isnad1 id=contdiff.3h7v.s10.8392f934d6b1 from=translated src=- shape=3ba6f38d vocab=5c78fed5
-/
theorem contDiffOn_LOG {W : P × E → (E →L[ℂ] E)} {C : ℝ}
    (hW : ContDiffOn ℂ 1 W (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖fderiv ℂ W q‖ ≤ C) :
    ContDiffOn ℂ 1 (LOG W) (ball z₀ σ₂ ×ˢ ball (0 : E) R) := by
  have hO : IsOpen (ball z₀ σ₂ ×ˢ ball (0 : E) R) := isOpen_ball.prod isOpen_ball
  have hWd : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, HasFDerivAt W (fderiv ℂ W q) q := fun q hq =>
    (((hW.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hq))).hasFDerivAt
  have hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R) := hW.continuousOn
  have hW'c : ContinuousOn (fderiv ℂ W) (ball z₀ σ₂ ×ˢ ball (0 : E) R) := hW.continuousOn_fderiv_of_isOpen hO le_rfl
  have hL : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R,
      HasFDerivAt (LOG W) (∫ t in (0 : ℝ)..1, LOG' W (fderiv ℂ W) q t) q := fun q hq =>
    hasFDerivAt_LOG hWd hWc hW'c hbW hbW' hq
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 0) (f := LOG W) hO).mpr
    ⟨fun q hq => (hL q hq).differentiableAt.differentiableWithinAt,
     fun h => absurd h (by simp),
     contDiffOn_zero.mpr (ContinuousOn.congr
       (fun q hq => (continuousAt_LOG'_integral hWc hW'c hbW hbW' hq).continuousWithinAt)
       (fun q hq => (hL q hq).fderiv))⟩
  simpa using h

end paramlog
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b

section main

variable {F : P → E → E → E} {z₀ : P} {σ ρ : ℝ}

/--
@isnad1 id=mem.2h5v.s7.1dfe971f8937 from=translated src=- shape=fab59f6c vocab=ea56bf5a
-/
theorem mem_ball_prod' {q : P × E} {ε : ℝ} (h1 : q.1 ∈ ball z₀ ε) (h2 : q.2 ∈ ball (0 : E) ε) :
    q ∈ ball ((z₀, (0 : E)) : P × E) ε := by
  rw [mem_ball, Prod.dist_eq]; exact max_lt h1 h2

/--
@isnad1 id=mem.1h5v.s7.c8dc9627791d from=translated src=- shape=bc636504 vocab=1d173124
-/
theorem snd_mem_ball {q : P × E} {ε : ℝ} (h : q ∈ ball ((z₀, (0 : E)) : P × E) ε) : q.2 ∈ ball (0 : E) ε := by
  rw [mem_ball, Prod.dist_eq] at h; exact lt_of_le_of_lt (le_max_right _ _) h

/--
@isnad1 id=ex.5h7v.s8.32753de690b6 from=translated src=- shape=e4bf0737 vocab=aaef8c45
-/
theorem exists_uniform_mul_mem (hσ : 0 < σ) (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ))
    (hzero_left : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z 0 v = v) {T : Set E} (hT : T ∈ 𝓝 (0 : E)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ σ ∧ a ≤ ρ ∧
      ∀ z ∈ ball z₀ a, ∀ x y : E, x ∈ ball (0 : E) a → y ∈ ball (0 : E) a → F z x y ∈ T := by
  have hc : ContinuousAt (F3 F) (z₀, ((0 : E), (0 : E))) :=
    hF3.continuousOn.continuousAt ((isOpen_N z₀ σ ρ).mem_nhds
      ⟨mem_ball_self hσ, mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)⟩)
  have h00 : F3 F (z₀, ((0 : E), (0 : E))) = 0 := by
    show F z₀ 0 0 = 0
    exact hzero_left z₀ (mem_ball_self hσ) 0 (zero_mem_ball hρ)
  rw [← h00] at hT
  obtain ⟨a, ha, hb⟩ := Metric.mem_nhds_iff.mp (hc.preimage_mem_nhds hT)
  refine ⟨min a (min σ ρ), lt_min ha (lt_min hσ hρ), le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (min_le_right _ _), fun z hz x y hx hy => ?_⟩
  have hz' := ball_subset_ball (min_le_left a (min σ ρ)) hz
  have hx' := ball_subset_ball (min_le_left a (min σ ρ)) hx
  have hy' := ball_subset_ball (min_le_left a (min σ ρ)) hy
  have hmem : ((z, (x, y)) : P × (E × E)) ∈ ball ((z₀, ((0 : E), (0 : E))) : P × (E × E)) a :=
    mem_ball_prod hz' (mem_ball_prod hx' hy')
  exact hb hmem

def Lam (W : P × E → (E →L[ℂ] E)) (q : P × E) : P × E := (q.1, LOG W q)

/--
@isnad1 id=eq.0h4v.s6.ee655131fd49 from=translated src=- shape=8b4abb86 vocab=4914f6a6
-/
@[scoped simp] theorem Lam_fst (W : P × E → (E →L[ℂ] E)) (q : P × E) : (Lam W q).1 = q.1 := rfl
/--
@isnad1 id=eq.0h4v.s7.e5ce5b3e8ef5 from=translated src=- shape=b63e5e3e vocab=11309920
-/
@[scoped simp] theorem Lam_snd (W : P × E → (E →L[ℂ] E)) (q : P × E) : (Lam W q).2 = LOG W q := rfl

/--
@isnad1 id=ex.7h6v.s10.c7e3a03db58e from=translated src=- shape=a4778d6c vocab=077b696b
-/
theorem coreB1 (hσ : 0 < σ) (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ))
    (hzero_left : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z 0 v = v)
    (hzero_right : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z v 0 = v)
    (hcomm : ∀ z ∈ ball z₀ σ, ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F z v w = F z w v)
    (hassoc : ∀ z ∈ ball z₀ σ, ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ →
      w ∈ ball (0 : E) ρ → F z u v ∈ ball (0 : E) ρ → F z v w ∈ ball (0 : E) ρ →
      F z (F z u v) w = F z u (F z v w)) :
    ∃ (σ' r δ : ℝ) (e ℓ : P → E → E), 0 < σ' ∧ σ' ≤ σ ∧ 0 < r ∧ 0 < δ ∧
      DifferentiableOn ℂ (fun q : P × E => e q.1 q.2) (ball z₀ σ' ×ˢ ball (0 : E) r) ∧
      DifferentiableOn ℂ (fun q : P × E => ℓ q.1 q.2) (ball z₀ σ' ×ˢ ball (0 : E) δ) ∧
      ∀ z ∈ ball z₀ σ',
        e z 0 = 0 ∧
        HasFDerivAt (e z) (ContinuousLinearMap.id ℂ E) 0 ∧
        InjOn (e z) (ball (0 : E) r) ∧
        MapsTo (e z) (ball (0 : E) r) (ball (0 : E) ρ) ∧
        (∀ v w : E, v ∈ ball (0 : E) r → w ∈ ball (0 : E) r → v + w ∈ ball (0 : E) r →
          e z (v + w) = F z (e z v) (e z w)) ∧
        (∀ x ∈ ball (0 : E) δ, ∃ v ∈ ball (0 : E) r, e z v = x) ∧
        (∀ v ∈ ball (0 : E) r, ℓ z (e z v) = v) ∧
        (∀ x ∈ ball (0 : E) δ, ℓ z x ∈ ball (0 : E) r ∧ e z (ℓ z x) = x) := by

  obtain ⟨σ₁, r₀, hσ₁p, hσ₁, hr₀p, hr₀, hunit⟩ := exists_uniform_units hσ hρ hF3 hzero_left
  have hfib : ∀ z ∈ ball z₀ σ, ContDiffOn ℂ 2 (uc (F z)) (S ρ) := fun z hz => contDiffOn_fibre hF3 hz
  have hωt : ContDiffOn ℂ 1 (ωt F) (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := contDiffOn_ωt hρ hF3 hσ₁ hr₀ hunit
  have hO₁ : IsOpen (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := isOpen_ball.prod isOpen_ball
  have h0mem : ((z₀, (0 : E)) : P × E) ∈ ball z₀ σ₁ ×ˢ ball (0 : E) r₀ := ⟨mem_ball_self hσ₁p, mem_ball_self hr₀p⟩

  obtain ⟨ε₁, hε₁, hb₁⟩ := exists_ball_norm_le' (f := ωt F) (hωt.continuousOn.continuousAt (hO₁.mem_nhds h0mem))
  obtain ⟨ε₂, hε₂, hb₂⟩ := exists_ball_norm_le' (f := fderiv ℂ (ωt F))
    ((hωt.continuousOn_fderiv_of_isOpen hO₁ le_rfl).continuousAt (hO₁.mem_nhds h0mem))
  obtain ⟨ε₃, hε₃, hb₃⟩ := exists_ball_norm_le' (f := ωt' F)
    ((continuousOn_ωt' hρ hF3 hσ₁ hr₀ hunit).continuousAt (hO₁.mem_nhds h0mem))
  set R : ℝ := min (min ε₁ (min ε₂ ε₃)) (min σ₁ r₀) with hRdef
  have hRp : 0 < R := lt_min (lt_min hε₁ (lt_min hε₂ hε₃)) (lt_min hσ₁p hr₀p)
  have hRσ₁ : R ≤ σ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRr₀ : R ≤ r₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hRε₁ : R ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRε₂ : R ≤ ε₂ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRε₃ : R ≤ ε₃ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hRρ : R ≤ ρ := le_trans hRr₀ hr₀
  have hRσ : R ≤ σ := le_trans hRσ₁ hσ₁
  set C : ℝ := max (max (‖ωt F (z₀, 0)‖ + 1) (‖fderiv ℂ (ωt F) (z₀, 0)‖ + 1)) (‖ωt' F (z₀, 0)‖ + 1) with hCdef
  have hsubO : ball z₀ R ×ˢ ball (0 : E) R ⊆ ball z₀ σ₁ ×ˢ ball (0 : E) r₀ :=
    prod_mono (ball_subset_ball hRσ₁) (ball_subset_ball hRr₀)
  have hbW : ∀ q ∈ ball z₀ R ×ˢ ball (0 : E) R, ‖ωt F q‖ ≤ C := fun q hq =>
    le_trans (hb₁ q (mem_ball_prod' (ball_subset_ball hRε₁ hq.1) (ball_subset_ball hRε₁ hq.2)))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hbW' : ∀ q ∈ ball z₀ R ×ˢ ball (0 : E) R, ‖fderiv ℂ (ωt F) q‖ ≤ C := fun q hq =>
    le_trans (hb₂ q (mem_ball_prod' (ball_subset_ball hRε₂ hq.1) (ball_subset_ball hRε₂ hq.2)))
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hbω' : ∀ q ∈ ball z₀ R ×ˢ ball (0 : E) R, ‖ωt' F q‖ ≤ C := fun q hq =>
    le_trans (hb₃ q (mem_ball_prod' (ball_subset_ball hRε₃ hq.1) (ball_subset_ball hRε₃ hq.2))) (le_max_right _ _)

  have hO : IsOpen (ball z₀ R ×ˢ ball (0 : E) R) := isOpen_ball.prod isOpen_ball
  have h0O : ((z₀, (0 : E)) : P × E) ∈ ball z₀ R ×ˢ ball (0 : E) R := ⟨mem_ball_self hRp, mem_ball_self hRp⟩
  have hLOG : ContDiffOn ℂ 1 (LOG (ωt F)) (ball z₀ R ×ˢ ball (0 : E) R) := contDiffOn_LOG (hωt.mono hsubO) hbW hbW'
  have hLOG0 : ∀ z : P, LOG (ωt F) (z, 0) = 0 := fun z => lineInt_zero _

  have hlogfib : ∀ z ∈ ball z₀ R, ∀ x ∈ ball (0 : E) R,
      HasFDerivAt (fun x => LOG (ωt F) (z, x)) (ω (F z) x) x := by
    intro z hz x hx
    have hzσ₁ : z ∈ ball z₀ σ₁ := ball_subset_ball hRσ₁ hz
    have hzσ : z ∈ ball z₀ σ := ball_subset_ball hσ₁ hzσ₁
    have hunitz : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u) := hunit z hzσ₁
    show HasFDerivAt (lineInt (ω (F z))) (ω (F z) x) x
    exact hasFDerivAt_lineInt (R := R) (C := C) (w' := ω' (F z))
      (fun u hu => hasFDerivAt_ω (hfib z hzσ) hr₀ hunitz (ball_subset_ball hRr₀ hu))
      ((continuousOn_ω (hfib z hzσ) hr₀ hunitz).mono (ball_subset_ball hRr₀))
      ((continuousOn_ω' (hfib z hzσ) hr₀ hunitz).mono (ball_subset_ball hRr₀))
      (fun u hu => hbW (z, u) ⟨hz, hu⟩) (fun u hu => hbω' (z, u) ⟨hz, hu⟩)
      (fun u hu a b => ω'_symm hρ (hfib z hzσ) (hzero_left z hzσ) (hzero_right z hzσ) (hcomm z hzσ)
        (hassoc z hzσ) hr₀p hr₀ hunitz (ball_subset_ball hRr₀ hu) a b) hx

  obtain ⟨a, hap, haσ, haρ, hamul⟩ := exists_uniform_mul_mem hσ hρ hF3 hzero_left (ball_mem_nhds (0 : E) hRp)
  have hadd : ∀ z ∈ ball z₀ (min a R), ∀ x y : E, x ∈ ball (0 : E) (min a R) → y ∈ ball (0 : E) (min a R) →
      LOG (ωt F) (z, F z x y) = LOG (ωt F) (z, x) + LOG (ωt F) (z, y) := by
    intro z hz x y hx hy
    have hzR : z ∈ ball z₀ R := ball_subset_ball (min_le_right _ _) hz
    have hza : z ∈ ball z₀ a := ball_subset_ball (min_le_left _ _) hz
    have hzσ₁ : z ∈ ball z₀ σ₁ := ball_subset_ball hRσ₁ hzR
    have hzσ : z ∈ ball z₀ σ := ball_subset_ball hσ₁ hzσ₁
    exact log_add hρ (hfib z hzσ) (hzero_right z hzσ) (hassoc z hzσ) hr₀ (hunit z hzσ₁) hRp hRr₀
      (log := fun x => LOG (ωt F) (z, x)) (hlogfib z hzR) (hLOG0 z) hap
      (fun x y hx hy => hamul z hza x y hx hy) hx hy

  have hΛC : ContDiffAt ℂ 1 (Lam (ωt F)) (z₀, 0) := by
    show ContDiffAt ℂ 1 (fun q : P × E => (q.1, LOG (ωt F) q)) (z₀, 0)
    exact contDiffAt_fst.prodMk (hLOG.contDiffAt (hO.mem_nhds h0O))
  set L' : P × E →L[ℂ] E := fderiv ℂ (LOG (ωt F)) (z₀, 0) with hL'def
  have hL' : HasFDerivAt (LOG (ωt F)) L' (z₀, 0) :=
    (((hLOG.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds h0O))).hasFDerivAt
  have hL'inr : L'.comp (ContinuousLinearMap.inr ℂ P E) = 1 := by
    have h1 : HasFDerivAt (fun x : E => LOG (ωt F) (z₀, x)) (L'.comp (ContinuousLinearMap.inr ℂ P E)) 0 :=
      HasFDerivAt.comp (f := fun x : E => ((z₀, x) : P × E)) 0 hL' (hasFDerivAt_prodMk_right (𝕜 := ℂ) z₀ (0 : E))
    have h2 := hlogfib z₀ (mem_ball_self hRp) 0 (mem_ball_self hRp)
    rw [ω_zero hρ (hfib z₀ (mem_ball_self hσ)) (hzero_left z₀ (mem_ball_self hσ))] at h2
    exact h1.unique h2
  let D : (P × E) ≃L[ℂ] (P × E) :=
    (ContinuousLinearEquiv.refl ℂ P).skewProd (ContinuousLinearEquiv.refl ℂ E) (L'.comp (ContinuousLinearMap.inl ℂ P E))
  have hΛD : HasFDerivAt (Lam (ωt F)) (D : P × E →L[ℂ] P × E) (z₀, 0) := by
    show HasFDerivAt (fun q : P × E => (q.1, LOG (ωt F) q)) (D : P × E →L[ℂ] P × E) (z₀, 0)
    have h := (hasFDerivAt_fst (𝕜 := ℂ) (p := ((z₀, (0 : E)) : P × E))).prodMk hL'
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    rintro ⟨ζ, k⟩
    have hsplit : L' (ζ, k) = L' (ζ, 0) + L' (0, k) := by
      rw [← L'.map_add]; simp
    have hk : L' (0, k) = k := by
      have := congrArg (fun T : E →L[ℂ] E => T k) hL'inr
      simpa using this
    simp [D, hsplit, hk, add_comm]
  set H := hΛC.toOpenPartialHomeomorph (Lam (ωt F)) hΛD one_ne_zero with hHdef
  have hHcoe : (H : P × E → P × E) = Lam (ωt F) := rfl
  have hΛ0 : Lam (ωt F) (z₀, 0) = (z₀, 0) := Prod.ext rfl (hLOG0 z₀)
  have h0s : ((z₀, (0 : E)) : P × E) ∈ H.source := hΛC.mem_toOpenPartialHomeomorph_source hΛD one_ne_zero
  have h0t : ((z₀, (0 : E)) : P × E) ∈ H.target := by
    have := hΛC.image_mem_toOpenPartialHomeomorph_target hΛD one_ne_zero
    rwa [hΛ0] at this
  have hsymmC : ContDiffAt ℂ 1 H.symm (z₀, 0) := by
    have := hΛC.to_localInverse hΛD one_ne_zero
    rwa [hΛ0] at this
  have hsymm0 : H.symm (z₀, 0) = (z₀, 0) := by
    have := H.left_inv h0s
    rwa [hHcoe, hΛ0] at this

  have K1 : ∀ q ∈ H.target, (H.symm q).1 = q.1 := fun q hq => by
    have h := H.right_inv hq
    rw [hHcoe] at h
    have h2 := congrArg Prod.fst h
    rwa [Lam_fst] at h2
  have K2 : ∀ (z : P) (y : E), ((z, y) : P × E) ∈ H.target → LOG (ωt F) (z, (H.symm (z, y)).2) = y := fun z y hq => by
    have h := H.right_inv hq
    rw [hHcoe] at h
    have h1 : H.symm (z, y) = (z, (H.symm (z, y)).2) := Prod.ext (K1 _ hq) rfl
    rw [h1] at h
    have h2 := congrArg Prod.snd h
    rwa [Lam_snd] at h2
  have K3 : ∀ (z : P) (x : E), ((z, x) : P × E) ∈ H.source → (H.symm (z, LOG (ωt F) (z, x))).2 = x := fun z x hp => by
    have h := H.left_inv hp
    rw [hHcoe] at h
    exact congrArg Prod.snd h

  obtain ⟨ε₅, hε₅, hsrc⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0s)
  obtain ⟨b, hbp, hbσ, hbρ, hbmul⟩ := exists_uniform_mul_mem hσ hρ hF3 hzero_left (ball_mem_nhds (0 : E) hε₅)
  set b' : ℝ := min b (min a R) with hb'def
  have hb'p : 0 < b' := lt_min hbp (lt_min hap hRp)
  have hN : H.target ∩ H.source ∩ {q : P × E | ContDiffAt ℂ 1 H.symm q} ∩
      H.symm ⁻¹' ball ((z₀, (0 : E)) : P × E) b' ∈ 𝓝 ((z₀, (0 : E)) : P × E) := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (H.open_target.mem_nhds h0t)
      (H.open_source.mem_nhds h0s)) (hsymmC.eventually (by simp))) ?_
    exact hsymmC.continuousAt.preimage_mem_nhds (by rw [hsymm0]; exact ball_mem_nhds _ hb'p)
  obtain ⟨ε₆, hε₆, hsub6⟩ := Metric.mem_nhds_iff.mp hN
  set r : ℝ := min ε₆ R with hrdef
  have hrp : 0 < r := lt_min hε₆ hRp
  have hΛpre : (Lam (ωt F)) ⁻¹' ball ((z₀, (0 : E)) : P × E) r ∈ 𝓝 ((z₀, (0 : E)) : P × E) :=
    hΛC.continuousAt.preimage_mem_nhds (by rw [hΛ0]; exact ball_mem_nhds _ hrp)
  obtain ⟨ε₇, hε₇, hsub7⟩ := Metric.mem_nhds_iff.mp hΛpre
  set σ' : ℝ := min (min ε₆ ε₇) (min (min b ε₅) (min a R)) with hσ'def
  have hσ'p : 0 < σ' := lt_min (lt_min hε₆ hε₇) (lt_min (lt_min hbp hε₅) (lt_min hap hRp))
  have hσ'ε₆ : σ' ≤ ε₆ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hσ'ε₇ : σ' ≤ ε₇ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hσ'b : σ' ≤ b := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hσ'ε₅ : σ' ≤ ε₅ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hσ'aR : σ' ≤ min a R := le_trans (min_le_right _ _) (min_le_right _ _)
  have hσ'R : σ' ≤ R := le_trans hσ'aR (min_le_right _ _)
  have hσ'σ : σ' ≤ σ := le_trans hσ'R hRσ
  set δ : ℝ := min ε₇ r with hδdef
  have hδp : 0 < δ := lt_min hε₇ hrp
  have hδr : δ ≤ r := min_le_right _ _

  have hT₀ : ∀ z ∈ ball z₀ σ', ∀ y ∈ ball (0 : E) r,
      ((z, y) : P × E) ∈ H.target ∧ ((z, y) : P × E) ∈ H.source ∧ ContDiffAt ℂ 1 H.symm (z, y) ∧
        H.symm (z, y) ∈ ball ((z₀, (0 : E)) : P × E) b' := by
    intro z hz y hy
    have hmem : ((z, y) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε₆ :=
      mem_ball_prod (ball_subset_ball hσ'ε₆ hz) (ball_subset_ball (min_le_left _ _) hy)
    have h := hsub6 hmem
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have heb' : ∀ z ∈ ball z₀ σ', ∀ y ∈ ball (0 : E) r, (H.symm (z, y)).2 ∈ ball (0 : E) b' := fun z hz y hy =>
    snd_mem_ball (hT₀ z hz y hy).2.2.2

  refine ⟨σ', r, δ, fun z y => (H.symm (z, y)).2, fun z x => LOG (ωt F) (z, x), hσ'p, hσ'σ, hrp, hδp,
    ?_, ?_, fun z hz => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro q hq
    have hcd : ContDiffAt ℂ 1 H.symm q := by
      have := (hT₀ q.1 hq.1 q.2 hq.2).2.2.1
      simpa using this
    exact ((hcd.differentiableAt (by simp)).snd).differentiableWithinAt
  ·
    refine ((hLOG.differentiableOn one_ne_zero).mono ?_).congr (fun q hq => rfl)
    exact prod_mono (ball_subset_ball hσ'R) (ball_subset_ball (le_trans hδr (min_le_right _ _)))
  ·
    have := K3 z 0 (hT₀ z hz 0 (mem_ball_self hrp)).2.1
    rwa [hLOG0] at this
  ·
    have hzR : z ∈ ball z₀ R := ball_subset_ball hσ'R hz
    have he0 : (H.symm (z, 0)).2 = 0 := by
      have := K3 z 0 (hT₀ z hz 0 (mem_ball_self hrp)).2.1
      rwa [hLOG0] at this
    have hg : ContinuousAt (fun y : E => (H.symm (z, y)).2) 0 := by
      have h1 : ContinuousAt (fun y : E => H.symm (z, y)) 0 :=
        ContinuousAt.comp (hT₀ z hz 0 (mem_ball_self hrp)).2.2.1.continuousAt
          (continuous_const.prodMk continuous_id).continuousAt
      exact h1.snd
    have hf : HasFDerivAt (fun x : E => LOG (ωt F) (z, x))
        ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) ((fun y : E => (H.symm (z, y)).2) 0) := by
      show HasFDerivAt (fun x : E => LOG (ωt F) (z, x)) _ (H.symm (z, 0)).2
      rw [he0]
      have := hlogfib z hzR 0 (mem_ball_self hRp)
      rw [ω_zero hρ (hfib z (ball_subset_ball hRσ hzR)) (hzero_left z (ball_subset_ball hRσ hzR)),
        ContinuousLinearMap.one_def] at this
      simpa using this
    have hfg : ∀ᶠ y in 𝓝 (0 : E), LOG (ωt F) (z, (H.symm (z, y)).2) = y := by
      filter_upwards [ball_mem_nhds (0 : E) hrp] with y hy
      exact K2 z y (hT₀ z hz y hy).1
    have := HasFDerivAt.of_local_left_inverse hg hf hfg
    simpa using this
  ·
    intro y hy y' hy' h
    have h1 := K2 z y (hT₀ z hz y hy).1
    have h2 := K2 z y' (hT₀ z hz y' hy').1
    have h' : (H.symm (z, y)).2 = (H.symm (z, y')).2 := h
    rw [← h1, ← h2, h']
  ·
    intro y hy
    exact ball_subset_ball (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hRρ) (heb' z hz y hy)
  ·
    intro v w hv hw hvw
    show (H.symm (z, v + w)).2 = F z (H.symm (z, v)).2 (H.symm (z, w)).2
    have hzaR : z ∈ ball z₀ (min a R) := ball_subset_ball hσ'aR hz
    have hev : (H.symm (z, v)).2 ∈ ball (0 : E) (min a R) := ball_subset_ball (min_le_right _ _) (heb' z hz v hv)
    have hew : (H.symm (z, w)).2 ∈ ball (0 : E) (min a R) := ball_subset_ball (min_le_right _ _) (heb' z hz w hw)
    have h1 : LOG (ωt F) (z, F z (H.symm (z, v)).2 (H.symm (z, w)).2) = v + w := by
      rw [hadd z hzaR _ _ hev hew, K2 z v (hT₀ z hz v hv).1, K2 z w (hT₀ z hz w hw).1]
    have h2 : LOG (ωt F) (z, (H.symm (z, v + w)).2) = v + w := K2 z (v + w) (hT₀ z hz _ hvw).1
    have hs1 : ((z, F z (H.symm (z, v)).2 (H.symm (z, w)).2) : P × E) ∈ H.source := by
      apply hsrc
      exact mem_ball_prod (ball_subset_ball hσ'ε₅ hz)
        (hbmul z (ball_subset_ball hσ'b hz) _ _ (ball_subset_ball (min_le_left _ _) (heb' z hz v hv))
          (ball_subset_ball (min_le_left _ _) (heb' z hz w hw)))
    have hs2 : ((z, (H.symm (z, v + w)).2) : P × E) ∈ H.source := by
      have hm := H.map_target (hT₀ z hz _ hvw).1
      have h1' : H.symm (z, v + w) = (z, (H.symm (z, v + w)).2) := Prod.ext (K1 _ (hT₀ z hz _ hvw).1) rfl
      rwa [h1'] at hm
    have heq : H (z, F z (H.symm (z, v)).2 (H.symm (z, w)).2) = H (z, (H.symm (z, v + w)).2) := by
      rw [hHcoe]
      exact Prod.ext rfl (h1.trans h2.symm)
    exact (congrArg Prod.snd (H.injOn hs1 hs2 heq)).symm
  ·
    intro x hx
    have hmem7 : ((z, x) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε₇ :=
      mem_ball_prod (ball_subset_ball hσ'ε₇ hz) (ball_subset_ball (min_le_left _ _) hx)
    have hΛr : Lam (ωt F) (z, x) ∈ ball ((z₀, (0 : E)) : P × E) r := hsub7 hmem7
    exact ⟨LOG (ωt F) (z, x), snd_mem_ball hΛr, K3 z x (hT₀ z hz x (ball_subset_ball hδr hx)).2.1⟩
  ·
    intro v hv
    exact K2 z v (hT₀ z hz v hv).1
  ·
    intro x hx
    have hmem7 : ((z, x) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε₇ :=
      mem_ball_prod (ball_subset_ball hσ'ε₇ hz) (ball_subset_ball (min_le_left _ _) hx)
    have hΛr : Lam (ωt F) (z, x) ∈ ball ((z₀, (0 : E)) : P × E) r := hsub7 hmem7
    exact ⟨snd_mem_ball hΛr, K3 z x (hT₀ z hz x (ball_subset_ball hδr hx)).2.1⟩

end main
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b

section glue

open scoped ContDiff

/--
@isnad1 id=contdiff.1h6v.s8.6b6305406043 from=translated src=- shape=812a2c37 vocab=b67ec4f2
-/
theorem contDiffOn_two_of_differentiableOn_family {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {z₀ : P} {σ ρ : ℝ} (F : P → E → E → E)
    (hF : DifferentiableOn ℂ (fun q : P × (E × E) => F q.1 q.2.1 q.2.2)
      (Metric.ball z₀ σ ×ˢ (Metric.ball (0 : E) ρ ×ˢ Metric.ball (0 : E) ρ))) :
    ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ) := by
  set n : ℕ := Module.finrank ℂ (P × (E × E)) with hn
  have hrank : Module.finrank ℂ (P × (E × E)) = Module.finrank ℂ (Fin n → ℂ) := by
    rw [Module.finrank_fin_fun]
  let Λ : (P × (E × E)) ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofFinrankEq hrank
  set U' : Set (Fin n → ℂ) := Λ.symm ⁻¹' (N z₀ σ ρ) with hU'
  have hU'open : IsOpen U' := (isOpen_N z₀ σ ρ).preimage Λ.symm.continuous
  have hf' : DifferentiableOn ℂ (F3 F ∘ Λ.symm) U' :=
    DifferentiableOn.comp (hg := hF) Λ.symm.differentiableOn (fun u hu => hu)
  have hC : ContDiffOn ℂ ∞ (F3 F ∘ Λ.symm) U' :=
    Complex.contDiffOn_infty_of_differentiableOn_pi hU'open hf'
  have hC2 : ContDiffOn ℂ 2 (F3 F ∘ Λ.symm) U' := hC.of_le (WithTop.coe_le_coe.mpr le_top)
  have hback : ContDiffOn ℂ 2 ((F3 F ∘ Λ.symm) ∘ Λ) (N z₀ σ ρ) :=
    hC2.comp Λ.contDiff.contDiffOn (fun p hp => by
      show Λ.symm (Λ p) ∈ N z₀ σ ρ
      rw [Λ.symm_apply_apply]; exact hp)
  refine hback.congr fun p hp => ?_
  simp [Function.comp]

end glue
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b

end LocalGroupLawB1
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawB1

end
open scoped _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b _root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawB1

open LocalGroupLawK3b LocalGroupLawB1 in
/--
@isnad1 id=ex.7h6v.s10.175f8561214e from=translated src=- shape=52cc99c7 vocab=1af1289e
-/
theorem solution
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (z₀ : P) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (F : P → E → E → E)
    (hF : DifferentiableOn ℂ (fun q : P × (E × E) => F q.1 q.2.1 q.2.2)
      (Metric.ball z₀ σ ×ˢ (Metric.ball (0 : E) ρ ×ˢ Metric.ball (0 : E) ρ)))
    (hzero_left : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z 0 v = v)
    (hzero_right : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z v 0 = v)
    (hcomm : ∀ z ∈ Metric.ball z₀ σ, ∀ v w : E, v ∈ Metric.ball (0 : E) ρ → w ∈ Metric.ball (0 : E) ρ →
      F z v w = F z w v)
    (hassoc : ∀ z ∈ Metric.ball z₀ σ, ∀ u v w : E, u ∈ Metric.ball (0 : E) ρ → v ∈ Metric.ball (0 : E) ρ →
      w ∈ Metric.ball (0 : E) ρ → F z u v ∈ Metric.ball (0 : E) ρ → F z v w ∈ Metric.ball (0 : E) ρ →
      F z (F z u v) w = F z u (F z v w)) :
    ∃ (σ' r δ : ℝ) (e ℓ : P → E → E), 0 < σ' ∧ σ' ≤ σ ∧ 0 < r ∧ 0 < δ ∧
      DifferentiableOn ℂ (fun q : P × E => e q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) r) ∧
      DifferentiableOn ℂ (fun q : P × E => ℓ q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) δ) ∧
      ∀ z ∈ Metric.ball z₀ σ',
        e z 0 = 0 ∧
        HasFDerivAt (e z) (ContinuousLinearMap.id ℂ E) 0 ∧
        Set.InjOn (e z) (Metric.ball (0 : E) r) ∧
        Set.MapsTo (e z) (Metric.ball (0 : E) r) (Metric.ball (0 : E) ρ) ∧
        (∀ v w : E, v ∈ Metric.ball (0 : E) r → w ∈ Metric.ball (0 : E) r → v + w ∈ Metric.ball (0 : E) r →
          e z (v + w) = F z (e z v) (e z w)) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ∃ v ∈ Metric.ball (0 : E) r, e z v = x) ∧
        (∀ v ∈ Metric.ball (0 : E) r, ℓ z (e z v) = v) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ℓ z x ∈ Metric.ball (0 : E) r ∧ e z (ℓ z x) = x) := by
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  exact coreB1 hσ hρ (contDiffOn_two_of_differentiableOn_family F hF) hzero_left hzero_right hcomm hassoc
