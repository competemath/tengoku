import Tengoku.Lmlf.LMLF.ODE.LinearSecondOrder
import Tengoku.Lmlf.LMLF.ODE.Wronskian
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fundamental pairs for second-order linear equations

Olver's characterization of a fundamental pair by a nowhere-vanishing
Wronskian and by linear independence of the scalar solutions on the interval.
-/

open Function Set

namespace LMLF.ODE

/-- The functions `y₁, y₂` span the scalar coordinates of all phase solutions on `I`.

This proposition asserts spanning only. That the fixed pairs themselves solve
the equation is deliberately supplied as an external hypothesis to the
fundamental-pair theorems below.-/
def SpansSecondOrderLinearSolutionsOn {𝕂 : Type*} [RCLike 𝕂]
    (I : Set ℝ) (f g y₁ y₂ : ℝ → 𝕂) : Prop :=
  ∀ (y v : ℝ → 𝕂),
    (∀ x ∈ I, HasDerivAt y (v x) x) →
    (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) →
    ∃ A B : 𝕂, EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I

/-- Linear independence of two restrictions is exactly absence of a
nontrivial constant scalar relation on the set.
@isnad1 id=iff.0h5v.s7.90bd0a5df615 from=translated src=- shape=9452e286 vocab=12a9da23
-/
theorem linearIndependent_restrict_pair_iff
    {X 𝕂 : Type*} [Ring 𝕂] (I : Set X) (y₁ y₂ : X → 𝕂) :
    LinearIndependent 𝕂
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] ↔
      ∀ A B : 𝕂,
        EqOn (fun x ↦ A * y₁ x + B * y₂ x) 0 I → A = 0 ∧ B = 0 := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h A B hzero
    apply h A B
    funext x
    exact hzero x.2
  · intro h A B hab
    apply h A B
    intro x hx
    have := congrFun hab ⟨x, hx⟩
    exact this

private theorem phaseSolution_eqOn
    {𝕂 : Type*} [RCLike 𝕂]
    {I : Set ℝ} (_hI : IsOpen I) (_hIc : IsPreconnected I)
    {f g : ℝ → 𝕂} (_hf : ContinuousOn f I) (_hg : ContinuousOn g I)
    {x₀ : ℝ} (_hx₀ : x₀ ∈ I)
    (hIVP : ∀ y₀ v₀ : 𝕂, ∃ s r : ℝ → 𝕂,
      s x₀ = y₀ ∧ r x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt s (r x) x) ∧
      (∀ x ∈ I, HasDerivAt r (-f x * r x - g x * s x) x) ∧
      ContDiffOn ℝ 2 s I ∧
      ∀ y' v' : ℝ → 𝕂,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn s y' I ∧ EqOn r v' I)
    {y v z q : ℝ → 𝕂}
    (hy : ∀ x ∈ I, HasDerivAt y (v x) x)
    (hv : ∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x)
    (hz : ∀ x ∈ I, HasDerivAt z (q x) x)
    (hq : ∀ x ∈ I, HasDerivAt q (-f x * q x - g x * z x) x)
    (hyz : y x₀ = z x₀) (hvq : v x₀ = q x₀) :
    EqOn y z I ∧ EqOn v q I := by
  obtain ⟨s, r, hs₀, hr₀, hs, hr, hsC2, hu⟩ := hIVP (y x₀) (v x₀)
  have huy := hu y v rfl rfl hy hv
  have huz := hu z q hyz.symm hvq.symm hz hq
  exact ⟨huy.1.symm.trans huz.1, huy.2.symm.trans huz.2⟩

private theorem linearCombination_phase
    {𝕂 : Type*} [RCLike 𝕂] {I : Set ℝ}
    {f g y₁ v₁ y₂ v₂ : ℝ → 𝕂} (A B : 𝕂)
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) :
    (∀ x ∈ I, HasDerivAt (fun t ↦ A * y₁ t + B * y₂ t)
      (A * v₁ x + B * v₂ x) x) ∧
    (∀ x ∈ I, HasDerivAt (fun t ↦ A * v₁ t + B * v₂ t)
      (-f x * (A * v₁ x + B * v₂ x) -
        g x * (A * y₁ x + B * y₂ x)) x) := by
  constructor
  · intro x hx
    exact ((hy₁ x hx).const_mul A).add ((hy₂ x hx).const_mul B)
  · intro x hx
    exact (((hv₁ x hx).const_mul A).add ((hv₂ x hx).const_mul B)).congr_deriv (by ring)

private theorem linearSolution_eqOn_cramer
    {𝕂 : Type*} [RCLike 𝕂]
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝕂} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I)
    (hIVP : ∀ y₀ v₀ : 𝕂, ∃ s r : ℝ → 𝕂,
      s x₀ = y₀ ∧ r x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt s (r x) x) ∧
      (∀ x ∈ I, HasDerivAt r (-f x * r x - g x * s x) x) ∧
      ContDiffOn ℝ 2 s I ∧
      ∀ y' v' : ℝ → 𝕂,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn s y' I ∧ EqOn r v' I)
    {y₁ v₁ y₂ v₂ y v : ℝ → 𝕂}
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x)
    (hy : ∀ x ∈ I, HasDerivAt y (v x) x)
    (hv : ∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x)
    (hW : wronskian y₁ v₁ y₂ v₂ x₀ ≠ 0) :
    let Δ := wronskian y₁ v₁ y₂ v₂ x₀
    let A := (y x₀ * v₂ x₀ - y₂ x₀ * v x₀) / Δ
    let B := (y₁ x₀ * v x₀ - y x₀ * v₁ x₀) / Δ
    EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I ∧
      EqOn v (fun x ↦ A * v₁ x + B * v₂ x) I := by
  dsimp only
  let A := (y x₀ * v₂ x₀ - y₂ x₀ * v x₀) /
    wronskian y₁ v₁ y₂ v₂ x₀
  let B := (y₁ x₀ * v x₀ - y x₀ * v₁ x₀) /
    wronskian y₁ v₁ y₂ v₂ x₀
  have hphase := linearCombination_phase A B hy₁ hv₁ hy₂ hv₂
  have hy₀ : y x₀ = A * y₁ x₀ + B * y₂ x₀ := by
    dsimp [A, B, wronskian]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hW).2
    simp only [wronskian]
    ring
  have hv₀ : v x₀ = A * v₁ x₀ + B * v₂ x₀ := by
    dsimp [A, B, wronskian]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hW).2
    simp only [wronskian]
    ring
  exact phaseSolution_eqOn hI hIc hf hg hx₀ hIVP hy hv hphase.1 hphase.2 hy₀ hv₀

/-- Cramer's formulas represent both coordinates of a complex phase solution.
@isnad1 id=other.12h10v.s9.40e9c1d48f99 from=translated src=- shape=c64d71b2 vocab=86347bfb
-/
theorem complexLinearSolution_eqOn_cramer
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) {y₁ v₁ y₂ v₂ y v : ℝ → ℂ}
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x)
    (hy : ∀ x ∈ I, HasDerivAt y (v x) x)
    (hv : ∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x)
    (hW : wronskian y₁ v₁ y₂ v₂ x₀ ≠ 0) :
    let Δ := wronskian y₁ v₁ y₂ v₂ x₀
    let A := (y x₀ * v₂ x₀ - y₂ x₀ * v x₀) / Δ
    let B := (y₁ x₀ * v x₀ - y x₀ * v₁ x₀) / Δ
    EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I ∧
      EqOn v (fun x ↦ A * v₁ x + B * v₂ x) I := by
  exact linearSolution_eqOn_cramer hI hIc hf hg hx₀
    (exists_unique_complexLinearIVP hI hIc hf hg hx₀) hy₁ hv₁ hy₂ hv₂ hy hv hW

/-- Cramer's formulas represent both coordinates of a real phase solution.
@isnad1 id=other.12h10v.s9.473b7eef7a8a from=translated src=- shape=22b4d9b0 vocab=832fd32c
-/
theorem realLinearSolution_eqOn_cramer
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) {y₁ v₁ y₂ v₂ y v : ℝ → ℝ}
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x)
    (hy : ∀ x ∈ I, HasDerivAt y (v x) x)
    (hv : ∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x)
    (hW : realWronskian y₁ v₁ y₂ v₂ x₀ ≠ 0) :
    let Δ := realWronskian y₁ v₁ y₂ v₂ x₀
    let A := (y x₀ * v₂ x₀ - y₂ x₀ * v x₀) / Δ
    let B := (y₁ x₀ * v x₀ - y x₀ * v₁ x₀) / Δ
    EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I ∧
      EqOn v (fun x ↦ A * v₁ x + B * v₂ x) I := by
  exact linearSolution_eqOn_cramer hI hIc hf hg hx₀
    (exists_unique_realLinearIVP hI hIc hf hg hx₀) hy₁ hv₁ hy₂ hv₂ hy hv hW

private theorem velocity_eq_of_scalar_eqOn
    {𝕂 : Type*} [RCLike 𝕂] {I : Set ℝ} (hI : IsOpen I)
    {y v z q : ℝ → 𝕂} {x : ℝ} (hx : x ∈ I)
    (hy : HasDerivAt y (v x) x) (hz : HasDerivAt z (q x) x)
    (hEq : EqOn y z I) : v x = q x := by
  have heq : y =ᶠ[nhds x] z := hEq.eventuallyEq_of_mem (hI.mem_nhds hx)
  exact hy.unique (hz.congr_of_eventuallyEq heq)

private theorem fundamentalPair_iff_aux
    {𝕂 : Type*} [RCLike 𝕂]
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝕂} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hIVP : ∀ (x₀ : ℝ), x₀ ∈ I → ∀ y₀ v₀ : 𝕂, ∃ s r : ℝ → 𝕂,
      s x₀ = y₀ ∧ r x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt s (r x) x) ∧
      (∀ x ∈ I, HasDerivAt r (-f x * r x - g x * s x) x) ∧
      ContDiffOn ℝ 2 s I ∧
      ∀ y' v' : ℝ → 𝕂,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn s y' I ∧ EqOn r v' I)
    {y₁ v₁ y₂ v₂ : ℝ → 𝕂}
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x)
    (hCramer : ∀ {x₀ : ℝ}, x₀ ∈ I → ∀ {y v : ℝ → 𝕂},
      (∀ x ∈ I, HasDerivAt y (v x) x) →
      (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) →
      wronskian y₁ v₁ y₂ v₂ x₀ ≠ 0 →
      let Δ := wronskian y₁ v₁ y₂ v₂ x₀
      let A := (y x₀ * v₂ x₀ - y₂ x₀ * v x₀) / Δ
      let B := (y₁ x₀ * v x₀ - y x₀ * v₁ x₀) / Δ
      EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I ∧
        EqOn v (fun x ↦ A * v₁ x + B * v₂ x) I) :
    (SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ↔
      ∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) ∧
    ((∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) ↔
      LinearIndependent 𝕂
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)]) := by
  have hspanW : SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ →
      ∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0 := by
    intro hspan x hx hzero
    obtain ⟨u₁, r₁, hu₁₀, hr₁₀, hu₁, hr₁, hu₁C2, hu₁uniq⟩ :=
      hIVP x hx 1 0
    obtain ⟨u₂, r₂, hu₂₀, hr₂₀, hu₂, hr₂, hu₂C2, hu₂uniq⟩ :=
      hIVP x hx 0 1
    obtain ⟨A, B, hAB⟩ := hspan u₁ r₁ hu₁ hr₁
    obtain ⟨C, D, hCD⟩ := hspan u₂ r₂ hu₂ hr₂
    have hABphase := linearCombination_phase A B hy₁ hv₁ hy₂ hv₂
    have hCDphase := linearCombination_phase C D hy₁ hv₁ hy₂ hv₂
    have hABv : r₁ x = A * v₁ x + B * v₂ x :=
      velocity_eq_of_scalar_eqOn (y := u₁) (v := r₁)
        (z := fun t ↦ A * y₁ t + B * y₂ t) (q := fun t ↦ A * v₁ t + B * v₂ t)
        hI hx (hu₁ x hx) (hABphase.1 x hx) hAB
    have hCDv : r₂ x = C * v₁ x + D * v₂ x :=
      velocity_eq_of_scalar_eqOn (y := u₂) (v := r₂)
        (z := fun t ↦ C * y₁ t + D * y₂ t) (q := fun t ↦ C * v₁ t + D * v₂ t)
        hI hx (hu₂ x hx) (hCDphase.1 x hx) hCD
    have hABx : A * y₁ x + B * y₂ x = 1 := by
      simpa [hu₁₀] using (hAB hx).symm
    have hCDx : C * y₁ x + D * y₂ x = 0 := by
      simpa [hu₂₀] using (hCD hx).symm
    have hABvel : A * v₁ x + B * v₂ x = 0 := by
      simpa [hr₁₀] using hABv.symm
    have hCDvel : C * v₁ x + D * v₂ x = 1 := by
      simpa [hr₂₀] using hCDv.symm
    have hdet : (1 : 𝕂) = wronskian y₁ v₁ y₂ v₂ x * (A * D - B * C) := by
      rw [wronskian]
      calc
        (1 : 𝕂) = (A * y₁ x + B * y₂ x) * (C * v₁ x + D * v₂ x) -
            (C * y₁ x + D * y₂ x) * (A * v₁ x + B * v₂ x) := by
              rw [hABx, hCDx, hABvel, hCDvel]
              simp
        _ = (y₁ x * v₂ x - y₂ x * v₁ x) * (A * D - B * C) := by ring
    rw [hzero, zero_mul] at hdet
    exact one_ne_zero hdet
  have hWspan : (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) →
      SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ := by
    intro hW
    obtain ⟨x₀, hx₀⟩ := hIne
    intro y v hy hv
    refine ⟨(y x₀ * v₂ x₀ - y₂ x₀ * v x₀) /
        wronskian y₁ v₁ y₂ v₂ x₀,
      (y₁ x₀ * v x₀ - y x₀ * v₁ x₀) /
        wronskian y₁ v₁ y₂ v₂ x₀, ?_⟩
    exact (hCramer hx₀ hy hv (hW x₀ hx₀)).1
  have hWind : (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) →
      LinearIndependent 𝕂
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] := by
    intro hW
    rw [linearIndependent_restrict_pair_iff]
    intro A B hzero
    obtain ⟨x₀, hx₀⟩ := hIne
    have hphase := linearCombination_phase A B hy₁ hv₁ hy₂ hv₂
    have hvel : A * v₁ x₀ + B * v₂ x₀ = 0 :=
      velocity_eq_of_scalar_eqOn
        (y := fun t ↦ A * y₁ t + B * y₂ t) (v := fun t ↦ A * v₁ t + B * v₂ t)
        (z := fun _ : ℝ ↦ (0 : 𝕂)) (q := fun _ : ℝ ↦ (0 : 𝕂))
        hI hx₀ (hphase.1 x₀ hx₀) (hasDerivAt_const x₀ (0 : 𝕂)) hzero
    have hval : A * y₁ x₀ + B * y₂ x₀ = 0 := by
      simpa using hzero hx₀
    have hA : A = 0 := by
      have hmul : A * wronskian y₁ v₁ y₂ v₂ x₀ = 0 := by
        rw [wronskian]
        calc
          A * (y₁ x₀ * v₂ x₀ - y₂ x₀ * v₁ x₀) =
              (A * y₁ x₀ + B * y₂ x₀) * v₂ x₀ -
                y₂ x₀ * (A * v₁ x₀ + B * v₂ x₀) := by ring
          _ = 0 := by rw [hval, hvel]; simp
      exact (mul_eq_zero.mp hmul).resolve_right (hW x₀ hx₀)
    have hB : B = 0 := by
      have hmul : B * wronskian y₁ v₁ y₂ v₂ x₀ = 0 := by
        rw [wronskian]
        calc
          B * (y₁ x₀ * v₂ x₀ - y₂ x₀ * v₁ x₀) =
              y₁ x₀ * (A * v₁ x₀ + B * v₂ x₀) -
                (A * y₁ x₀ + B * y₂ x₀) * v₁ x₀ := by ring
          _ = 0 := by rw [hval, hvel]; simp
      exact (mul_eq_zero.mp hmul).resolve_right (hW x₀ hx₀)
    exact ⟨hA, hB⟩
  have hindW : LinearIndependent 𝕂
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] →
      ∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0 := by
    intro hind x hx hzero
    rw [linearIndependent_restrict_pair_iff] at hind
    have zeroFirst : ∀ z ∈ I, HasDerivAt (fun _ : ℝ ↦ (0 : 𝕂)) 0 z := by
      intro z hz
      exact hasDerivAt_const z 0
    have zeroSecond : ∀ z ∈ I, HasDerivAt (fun _ : ℝ ↦ (0 : 𝕂))
        (-f z * 0 - g z * 0) z := by
      intro z hz
      simpa using (hasDerivAt_const z (0 : 𝕂))
    have contradict (A B : 𝕂)
        (hval : A * y₁ x + B * y₂ x = 0)
        (hvel : A * v₁ x + B * v₂ x = 0)
        (hnonzero : A ≠ 0 ∨ B ≠ 0) : False := by
      have hphase := linearCombination_phase A B hy₁ hv₁ hy₂ hv₂
      have hEq := phaseSolution_eqOn hI hIc hf hg hx (hIVP x hx)
        hphase.1 hphase.2 zeroFirst zeroSecond hval hvel
      have hcoeff := hind A B hEq.1
      exact hnonzero.elim (fun h ↦ h hcoeff.1) (fun h ↦ h hcoeff.2)
    by_cases hab : y₁ x ≠ 0 ∨ y₂ x ≠ 0
    · apply contradict (y₂ x) (-y₁ x)
      · ring
      · rw [wronskian] at hzero
        calc
          y₂ x * v₁ x + -y₁ x * v₂ x =
              -(y₁ x * v₂ x - y₂ x * v₁ x) := by ring
          _ = 0 := by rw [hzero]; simp
      · rcases hab with hy₁x | hy₂x
        · exact Or.inr (neg_ne_zero.mpr hy₁x)
        · exact Or.inl hy₂x
    · simp only [not_or, not_ne_iff] at hab
      by_cases hv12 : v₁ x ≠ 0 ∨ v₂ x ≠ 0
      · apply contradict (v₂ x) (-v₁ x)
        · simp [hab.1, hab.2]
        · ring
        · rcases hv12 with hv₁x | hv₂x
          · exact Or.inr (neg_ne_zero.mpr hv₁x)
          · exact Or.inl hv₂x
      · simp only [not_or, not_ne_iff] at hv12
        apply contradict 1 0
        · simp [hab.1]
        · simp [hv12.1]
        · exact Or.inl one_ne_zero
  exact ⟨⟨hspanW, hWspan⟩, ⟨hWind, hindW⟩⟩

/-- A complex pair of phase solutions spans exactly when its Wronskian is
nowhere zero, equivalently when its scalar restrictions are independent.
@isnad1 id=and.9h7v.s9.7e7e00e03124 from=translated src=- shape=b347134c vocab=1cd1beb1
-/
theorem complexFundamentalPair_iff
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g y₁ v₁ y₂ v₂ : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) :
    (SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ↔
      ∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) ∧
    ((∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) ↔
      LinearIndependent ℂ
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)]) := by
  exact fundamentalPair_iff_aux hIne hI hIc hf hg
    (fun x₀ hx₀ ↦ exists_unique_complexLinearIVP hI hIc hf hg hx₀)
    hy₁ hv₁ hy₂ hv₂
    (fun {x₀} hx₀ {y v} hy hv hW ↦ complexLinearSolution_eqOn_cramer hI hIc hf hg hx₀
      hy₁ hv₁ hy₂ hv₂ hy hv hW)

/-- A real pair of phase solutions spans exactly when its Wronskian is
nowhere zero, equivalently when its scalar restrictions are independent.
@isnad1 id=and.9h7v.s8.a949424255e4 from=translated src=- shape=495ddb9f vocab=ed824675
-/
theorem realFundamentalPair_iff
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g y₁ v₁ y₂ v₂ : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hy₁ : ∀ x ∈ I, HasDerivAt y₁ (v₁ x) x)
    (hv₁ : ∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x)
    (hy₂ : ∀ x ∈ I, HasDerivAt y₂ (v₂ x) x)
    (hv₂ : ∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) :
    (SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ↔
      ∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x ≠ 0) ∧
    ((∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x ≠ 0) ↔
      LinearIndependent ℝ
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)]) := by
  exact fundamentalPair_iff_aux hIne hI hIc hf hg
    (fun x₀ hx₀ ↦ exists_unique_realLinearIVP hI hIc hf hg hx₀)
    hy₁ hv₁ hy₂ hv₂
    (fun {x₀} hx₀ {y v} hy hv hW ↦ realLinearSolution_eqOn_cramer hI hIc hf hg hx₀
      hy₁ hv₁ hy₂ hv₂ hy hv hW)

private theorem phaseSolution_contDiffOn_and_sourceEquation
    {𝕂 : Type*} [RCLike 𝕂]
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (_hIc : IsPreconnected I)
    {f g : ℝ → 𝕂} (_hf : ContinuousOn f I) (_hg : ContinuousOn g I)
    (hIVP : ∀ (x₀ : ℝ), x₀ ∈ I → ∀ y₀ v₀ : 𝕂, ∃ s r : ℝ → 𝕂,
      s x₀ = y₀ ∧ r x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt s (r x) x) ∧
      (∀ x ∈ I, HasDerivAt r (-f x * r x - g x * s x) x) ∧
      ContDiffOn ℝ 2 s I ∧
      ∀ y' v' : ℝ → 𝕂,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn s y' I ∧ EqOn r v' I)
    {y v : ℝ → 𝕂}
    (hy : ∀ x ∈ I, HasDerivAt y (v x) x)
    (hv : ∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) :
    ContDiffOn ℝ 2 y I ∧
      ∀ x ∈ I, HasDerivAt (deriv y) (-f x * deriv y x - g x * y x) x := by
  obtain ⟨x₀, hx₀⟩ := hIne
  obtain ⟨s, r, hs₀, hr₀, hs, hr, hsC2, hu⟩ := hIVP x₀ hx₀ (y x₀) (v x₀)
  have hsy := hu y v rfl rfl hy hv
  have hyC2 : ContDiffOn ℝ 2 y I := hsC2.congr fun x hx ↦ (hsy.1 hx).symm
  have hdy : EqOn (deriv y) v I := fun x hx ↦ (hy x hx).deriv
  refine ⟨hyC2, ?_⟩
  intro x hx
  have hev : deriv y =ᶠ[nhds x] v := hdy.eventuallyEq_of_mem (hI.mem_nhds hx)
  exact ((hv x hx).congr_of_eventuallyEq hev).congr_deriv (by rw [hdy hx])

private theorem firstDerivative_of_contDiffOn_two
    {𝕂 : Type*} [RCLike 𝕂] {I : Set ℝ} (hI : IsOpen I)
    {y : ℝ → 𝕂} (hyC2 : ContDiffOn ℝ 2 y I) :
    ∀ x ∈ I, HasDerivAt y (deriv y x) x := by
  intro x hx
  exact (((hyC2.differentiableOn (by norm_num)) x hx).differentiableAt
    (hI.mem_nhds hx)).hasDerivAt

private theorem secondOrderFundamentalPair_iff_aux
    {𝕂 : Type*} [RCLike 𝕂]
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝕂} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hIVP : ∀ (x₀ : ℝ), x₀ ∈ I → ∀ y₀ v₀ : 𝕂, ∃ s r : ℝ → 𝕂,
      s x₀ = y₀ ∧ r x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt s (r x) x) ∧
      (∀ x ∈ I, HasDerivAt r (-f x * r x - g x * s x) x) ∧
      ContDiffOn ℝ 2 s I ∧
      ∀ y' v' : ℝ → 𝕂,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn s y' I ∧ EqOn r v' I)
    {y₁ y₂ : ℝ → 𝕂} (hy₁C2 : ContDiffOn ℝ 2 y₁ I)
    (hy₁Eq : ∀ x ∈ I, HasDerivAt (deriv y₁)
      (-f x * deriv y₁ x - g x * y₁ x) x)
    (hy₂C2 : ContDiffOn ℝ 2 y₂ I)
    (hy₂Eq : ∀ x ∈ I, HasDerivAt (deriv y₂)
      (-f x * deriv y₂ x - g x * y₂ x) x)
    (hCramer : ∀ {x₀ : ℝ}, x₀ ∈ I → ∀ {y v : ℝ → 𝕂},
      (∀ x ∈ I, HasDerivAt y (v x) x) →
      (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) →
      wronskian y₁ (deriv y₁) y₂ (deriv y₂) x₀ ≠ 0 →
      let Δ := wronskian y₁ (deriv y₁) y₂ (deriv y₂) x₀
      let A := (y x₀ * deriv y₂ x₀ - y₂ x₀ * v x₀) / Δ
      let B := (y₁ x₀ * v x₀ - y x₀ * deriv y₁ x₀) / Δ
      EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I ∧
        EqOn v (fun x ↦ A * deriv y₁ x + B * deriv y₂ x) I) :
    ((∀ y : ℝ → 𝕂, ContDiffOn ℝ 2 y I →
        (∀ x ∈ I, HasDerivAt (deriv y)
          (-f x * deriv y x - g x * y x) x) →
        ∃ A B : 𝕂, EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I) ↔
      ∀ x ∈ I, wronskian y₁ (deriv y₁) y₂ (deriv y₂) x ≠ 0) ∧
    ((∀ x ∈ I, wronskian y₁ (deriv y₁) y₂ (deriv y₂) x ≠ 0) ↔
      LinearIndependent 𝕂
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)]) := by
  have hy₁ := firstDerivative_of_contDiffOn_two hI hy₁C2
  have hy₂ := firstDerivative_of_contDiffOn_two hI hy₂C2
  have hphase := fundamentalPair_iff_aux hIne hI hIc hf hg hIVP
    hy₁ hy₁Eq hy₂ hy₂Eq hCramer
  have hsource_phase :
      (∀ y : ℝ → 𝕂, ContDiffOn ℝ 2 y I →
          (∀ x ∈ I, HasDerivAt (deriv y)
            (-f x * deriv y x - g x * y x) x) →
          ∃ A B : 𝕂, EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I) ↔
        SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ := by
    constructor
    · intro hsource y v hy hv
      obtain ⟨hyC2, hyEq⟩ := phaseSolution_contDiffOn_and_sourceEquation
        hIne hI hIc hf hg hIVP hy hv
      exact hsource y hyC2 hyEq
    · intro hspan y hyC2 hyEq
      exact hspan y (deriv y) (firstDerivative_of_contDiffOn_two hI hyC2) hyEq
  exact ⟨hsource_phase.trans hphase.1, hphase.2⟩

/-- Olver's source-`C²` complex fundamental-pair characterization.
@isnad1 id=and.9h5v.s10.bb384eb2ba41 from=translated src=- shape=173c14a7 vocab=1c394ae1
-/
theorem complexSecondOrderFundamentalPair_iff
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g y₁ y₂ : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hy₁C2 : ContDiffOn ℝ 2 y₁ I)
    (hy₁Eq : ∀ x ∈ I, HasDerivAt (deriv y₁)
      (-f x * deriv y₁ x - g x * y₁ x) x)
    (hy₂C2 : ContDiffOn ℝ 2 y₂ I)
    (hy₂Eq : ∀ x ∈ I, HasDerivAt (deriv y₂)
      (-f x * deriv y₂ x - g x * y₂ x) x) :
    ((∀ y : ℝ → ℂ, ContDiffOn ℝ 2 y I →
        (∀ x ∈ I, HasDerivAt (deriv y)
          (-f x * deriv y x - g x * y x) x) →
        ∃ A B : ℂ, EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I) ↔
      ∀ x ∈ I, wronskian y₁ (deriv y₁) y₂ (deriv y₂) x ≠ 0) ∧
    ((∀ x ∈ I, wronskian y₁ (deriv y₁) y₂ (deriv y₂) x ≠ 0) ↔
      LinearIndependent ℂ
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)]) := by
  exact secondOrderFundamentalPair_iff_aux hIne hI hIc hf hg
    (fun x₀ hx₀ ↦ exists_unique_complexLinearIVP hI hIc hf hg hx₀)
    hy₁C2 hy₁Eq hy₂C2 hy₂Eq
    (fun {x₀} hx₀ {y v} hy hv hW ↦ complexLinearSolution_eqOn_cramer hI hIc hf hg hx₀
      (firstDerivative_of_contDiffOn_two hI hy₁C2) hy₁Eq
      (firstDerivative_of_contDiffOn_two hI hy₂C2) hy₂Eq hy hv hW)

/-- Olver's source-`C²` real fundamental-pair characterization.
@isnad1 id=and.9h5v.s9.b44de96640f8 from=translated src=- shape=4dc2d074 vocab=fc491517
-/
theorem realSecondOrderFundamentalPair_iff
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g y₁ y₂ : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hy₁C2 : ContDiffOn ℝ 2 y₁ I)
    (hy₁Eq : ∀ x ∈ I, HasDerivAt (deriv y₁)
      (-f x * deriv y₁ x - g x * y₁ x) x)
    (hy₂C2 : ContDiffOn ℝ 2 y₂ I)
    (hy₂Eq : ∀ x ∈ I, HasDerivAt (deriv y₂)
      (-f x * deriv y₂ x - g x * y₂ x) x) :
    ((∀ y : ℝ → ℝ, ContDiffOn ℝ 2 y I →
        (∀ x ∈ I, HasDerivAt (deriv y)
          (-f x * deriv y x - g x * y x) x) →
        ∃ A B : ℝ, EqOn y (fun x ↦ A * y₁ x + B * y₂ x) I) ↔
      ∀ x ∈ I, realWronskian y₁ (deriv y₁) y₂ (deriv y₂) x ≠ 0) ∧
    ((∀ x ∈ I, realWronskian y₁ (deriv y₁) y₂ (deriv y₂) x ≠ 0) ↔
      LinearIndependent ℝ
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)]) := by
  exact secondOrderFundamentalPair_iff_aux hIne hI hIc hf hg
    (fun x₀ hx₀ ↦ exists_unique_realLinearIVP hI hIc hf hg hx₀)
    hy₁C2 hy₁Eq hy₂C2 hy₂Eq
    (fun {x₀} hx₀ {y v} hy hv hW ↦ realLinearSolution_eqOn_cramer hI hIc hf hg hx₀
      (firstDerivative_of_contDiffOn_two hI hy₁C2) hy₁Eq
      (firstDerivative_of_contDiffOn_two hI hy₂C2) hy₂Eq hy hv hW)

/-- The two normalized complex IVPs form a canonical fundamental pair.
@isnad1 id=ex.5h4v.s9.5675f6cc3d31 from=translated src=- shape=d46c041a vocab=e38e04ed
-/
theorem exists_complexCanonicalFundamentalPair
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ y₁ v₁ y₂ v₂ : ℝ → ℂ,
      y₁ x₀ = 1 ∧ v₁ x₀ = 0 ∧ y₂ x₀ = 0 ∧ v₂ x₀ = 1 ∧
      (∀ x ∈ I, HasDerivAt y₁ (v₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt y₂ (v₂ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) ∧
      ContDiffOn ℝ 2 y₁ I ∧ ContDiffOn ℝ 2 y₂ I ∧
      (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) ∧
      SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ∧
      LinearIndependent ℂ
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] ∧
      ∀ (y v : ℝ → ℂ),
        (∀ x ∈ I, HasDerivAt y (v x) x) →
        (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) →
        EqOn y (fun x ↦ y x₀ * y₁ x + v x₀ * y₂ x) I ∧
          EqOn v (fun x ↦ y x₀ * v₁ x + v x₀ * v₂ x) I := by
  obtain ⟨y₁, v₁, hy₁₀, hv₁₀, hy₁, hv₁, hy₁C2, hu₁⟩ :=
    exists_unique_complexLinearIVP hI hIc hf hg hx₀ 1 0
  obtain ⟨y₂, v₂, hy₂₀, hv₂₀, hy₂, hv₂, hy₂C2, hu₂⟩ :=
    exists_unique_complexLinearIVP hI hIc hf hg hx₀ 0 1
  have hW₀ : wronskian y₁ v₁ y₂ v₂ x₀ ≠ 0 := by
    simp [wronskian, hy₁₀, hv₁₀, hy₂₀, hv₂₀]
  have hW : ∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0 := by
    intro x hx hzero
    have hbase := (wronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).1 hzero
    exact hW₀ hbase
  have hequiv := complexFundamentalPair_iff ⟨x₀, hx₀⟩ hI hIc hf hg hy₁ hv₁ hy₂ hv₂
  have hspan := hequiv.1.2 hW
  have hind := hequiv.2.1 hW
  refine ⟨y₁, v₁, y₂, v₂, hy₁₀, hv₁₀, hy₂₀, hv₂₀,
    hy₁, hv₁, hy₂, hv₂, hy₁C2, hy₂C2, hW, hspan, hind, ?_⟩
  intro y v hy hv
  have hcr := complexLinearSolution_eqOn_cramer hI hIc hf hg hx₀
    hy₁ hv₁ hy₂ hv₂ hy hv hW₀
  simpa [wronskian, hy₁₀, hv₁₀, hy₂₀, hv₂₀] using hcr

/-- The two normalized real IVPs form a canonical fundamental pair.
@isnad1 id=ex.5h4v.s9.95238804736c from=translated src=- shape=652e680b vocab=1f113b87
-/
theorem exists_realCanonicalFundamentalPair
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ y₁ v₁ y₂ v₂ : ℝ → ℝ,
      y₁ x₀ = 1 ∧ v₁ x₀ = 0 ∧ y₂ x₀ = 0 ∧ v₂ x₀ = 1 ∧
      (∀ x ∈ I, HasDerivAt y₁ (v₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₁ (-f x * v₁ x - g x * y₁ x) x) ∧
      (∀ x ∈ I, HasDerivAt y₂ (v₂ x) x) ∧
      (∀ x ∈ I, HasDerivAt v₂ (-f x * v₂ x - g x * y₂ x) x) ∧
      ContDiffOn ℝ 2 y₁ I ∧ ContDiffOn ℝ 2 y₂ I ∧
      (∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x ≠ 0) ∧
      SpansSecondOrderLinearSolutionsOn I f g y₁ y₂ ∧
      LinearIndependent ℝ
        ![(fun x : I ↦ y₁ x.1), (fun x : I ↦ y₂ x.1)] ∧
      ∀ (y v : ℝ → ℝ),
        (∀ x ∈ I, HasDerivAt y (v x) x) →
        (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) →
        EqOn y (fun x ↦ y x₀ * y₁ x + v x₀ * y₂ x) I ∧
          EqOn v (fun x ↦ y x₀ * v₁ x + v x₀ * v₂ x) I := by
  obtain ⟨y₁, v₁, hy₁₀, hv₁₀, hy₁, hv₁, hy₁C2, hu₁⟩ :=
    exists_unique_realLinearIVP hI hIc hf hg hx₀ 1 0
  obtain ⟨y₂, v₂, hy₂₀, hv₂₀, hy₂, hv₂, hy₂C2, hu₂⟩ :=
    exists_unique_realLinearIVP hI hIc hf hg hx₀ 0 1
  have hW₀ : realWronskian y₁ v₁ y₂ v₂ x₀ ≠ 0 := by
    simp [realWronskian, wronskian, hy₁₀, hv₁₀, hy₂₀, hv₂₀]
  have hW : ∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x ≠ 0 := by
    intro x hx hzero
    have hbase :=
      (realWronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).1 hzero
    exact hW₀ hbase
  have hequiv := realFundamentalPair_iff ⟨x₀, hx₀⟩ hI hIc hf hg hy₁ hv₁ hy₂ hv₂
  have hspan := hequiv.1.2 hW
  have hind := hequiv.2.1 hW
  refine ⟨y₁, v₁, y₂, v₂, hy₁₀, hv₁₀, hy₂₀, hv₂₀,
    hy₁, hv₁, hy₂, hv₂, hy₁C2, hy₂C2, hW, hspan, hind, ?_⟩
  intro y v hy hv
  have hcr := realLinearSolution_eqOn_cramer hI hIc hf hg hx₀
    hy₁ hv₁ hy₂ hv₂ hy hv hW₀
  simpa [realWronskian, wronskian, hy₁₀, hv₁₀, hy₂₀, hv₂₀] using hcr

end LMLF.ODE
