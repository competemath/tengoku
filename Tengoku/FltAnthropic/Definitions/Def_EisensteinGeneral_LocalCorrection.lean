import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace EisensteinGeneral.LocalCorrection

def geomSum (χϖ : ℂ) (N : ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k

def ramSum (N : ℕ) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k

def corrOff (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) : ℂ :=
  if e ≤ 0 then geomSum χϖ N (-e).toNat s else 0

def corrOn (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  if e ≤ n + (max m c : ℕ) then
    (μ𝒪 : ℂ)⁻¹ * ramSum N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
  else 0

/--
@isnad1 id=eq.0h4v.s6.477cf8e476a0 from=translated src=- shape=e3608109 vocab=a201254a
-/
theorem geomSum_def (χϖ : ℂ) (N M : ℕ) (s : ℂ) :
    geomSum χϖ N M s = ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k := rfl

/--
@isnad1 id=eq.0h5v.s6.9536930d9170 from=translated src=- shape=53fe8f63 vocab=87227ab5
-/
theorem ramSum_def (N K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) :
    ramSum N K c₀ sh s = c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k := rfl

/--
@isnad1 id=eq.0h4v.s5.0f30ff6f3669 from=translated src=- shape=51332479 vocab=ef49ecef
-/
theorem corrOff_def (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) :
    corrOff χϖ N e s = if e ≤ 0 then geomSum χϖ N (-e).toNat s else 0 := rfl

/--
@isnad1 id=eq.0h9v.s7.8b7e22a10dbd from=translated src=- shape=339f816e vocab=acebe8ad
-/
theorem corrOn_def (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) :
    corrOn N n c m e μ𝒪 c₀ sh s =
      if e ≤ n + (max m c : ℕ) then (μ𝒪 : ℂ)⁻¹ * ramSum N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
      else 0 := rfl

/--
@isnad1 id=differen.1h1v.s6.529dbfb72605 from=translated src=- shape=4bcaebd1 vocab=03518b6e
-/
theorem differentiable_cpow_neg_two_mul {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s))) :=
  Differentiable.const_cpow (differentiable_id.const_mul (2 : ℂ)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

/--
@isnad1 id=differen.1h1v.s6.d8668e7a8057 from=translated src=- shape=b667d1fe vocab=9908f8b8
-/
theorem differentiable_cpow_neg_two_mul_add_one {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s + 1))) :=
  Differentiable.const_cpow ((differentiable_id.const_mul (2 : ℂ)).add (differentiable_const 1)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

/--
@isnad1 id=differen.1h3v.s6.de5286df6242 from=translated src=- shape=e9efed19 vocab=943ed495
-/
theorem geomSum_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    Differentiable ℂ (geomSum χϖ N M) := by
  unfold geomSum
  exact Differentiable.fun_sum fun k _ => ((differentiable_cpow_neg_two_mul hN).const_mul χϖ).pow k

/--
@isnad1 id=differen.1h4v.s6.4e0a4b6a00d5 from=translated src=- shape=019f2f76 vocab=f215c519
-/
theorem ramSum_differentiable {N : ℕ} (hN : 0 < N) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) :
    Differentiable ℂ (ramSum N K c₀ sh) := by
  unfold ramSum
  exact (differentiable_const c₀).add
    (Differentiable.fun_sum fun k _ => ((differentiable_cpow_neg_two_mul_add_one hN).pow k).mul_const (sh k))

/--
@isnad1 id=differen.1h3v.s6.e0ab9fdb7186 from=translated src=- shape=c78c2093 vocab=7c74e2a8
-/
theorem corrOff_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (e : ℤ) :
    Differentiable ℂ (corrOff χϖ N e) := by
  unfold corrOff
  by_cases he : e ≤ 0
  · simp only [he, ↓reduceIte]
    exact geomSum_differentiable χϖ hN _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

/--
@isnad1 id=differen.1h8v.s6.c438bdb9c72e from=translated src=- shape=b7897ab2 vocab=50964881
-/
theorem corrOn_differentiable {N : ℕ} (hN : 0 < N) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ)
    (sh : ℕ → ℂ) : Differentiable ℂ (corrOn N n c m e μ𝒪 c₀ sh) := by
  unfold corrOn
  by_cases he : e ≤ n + (max m c : ℕ)
  · simp only [he, ↓reduceIte]
    exact (ramSum_differentiable hN _ c₀ sh).const_mul _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

end EisensteinGeneral.LocalCorrection

end
