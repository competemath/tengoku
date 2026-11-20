import Tengoku.Hellingerrepolean4.Hellinger.F2Model
import Tengoku.Hellingerrepolean4.Hellinger.FourierProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Boolean/F₂ model bridges for objectives, translations, and flatness. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.F2Model
open ChannelSections

/--
@isnad1 id=eq.0h4v.s5.9bfbb33f678b from=translated src=- shape=72282452 vocab=fbf3e373
-/
theorem objective_comp_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (f : Λ → ℝ) : objective (f ∘ e) = objective f := by
  have hm := mean_comp_equiv e f
  have hr := mean_comp_equiv e (fun x => root (f x))
  unfold objective
  rw [hm]
  exact congrArg (root (mean f) - ·) hr

/--
@isnad1 id=eq.1h3v.s7.bbb2587ed62e from=translated src=- shape=808f2fb4 vocab=3ebe2208
-/
theorem noise_objective_bits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : (ι → F2) → ℝ) :
    objective ((noise ι ρ hρ).apply f) =
      objective ((indexedBSC ι ρ hρ).apply (f ∘ bitsEquiv ι)) := by
  have hfun : ((noise ι ρ hρ).apply f) ∘ bitsEquiv ι =
      (indexedBSC ι ρ hρ).apply (f ∘ bitsEquiv ι) := by
    funext x
    exact noise_apply_bits ρ hρ f x
  rw [← hfun, objective_comp_equiv]

/--
@isnad1 id=eq.0h2v.s6.9aea898b0d34 from=translated src=- shape=371ffd5a vocab=9caba52f
-/
@[simp] theorem bitEquiv_xor (x y : Bool) :
    bitEquiv (Bool.xor x y) = bitEquiv x + bitEquiv y := by
  cases x <;> cases y <;> simp [show (1 : F2) + 1 = 0 from rfl]

/--
@isnad1 id=eq.0h1v.s6.3383bd7e56dc from=translated src=- shape=c477b57d vocab=c18020c1
-/
@[simp] theorem bitsEquiv_zero (n : ℕ) : bitsEquiv (Fin n) (fun _ => false) = 0 := by
  funext i
  rfl

/--
@isnad1 id=eq.0h3v.s7.cfa7e041bc63 from=translated src=- shape=38c90416 vocab=4c50a5c9
-/
theorem bitsEquiv_translate (n : ℕ) (x v : Fourier.Cube n) :
    bitsEquiv (Fin n) (Fourier.translate x v) = bitsEquiv (Fin n) x + bitsEquiv (Fin n) v := by
  funext i
  simpa only [Fourier.translate, bitsEquiv_apply, Pi.add_apply, Bool.xor_comm] using
    bitEquiv_xor (x i) (v i)

/--
@isnad1 id=eq.0h3v.s7.6d80ef496c68 from=translated src=- shape=9b52181c vocab=93e528d0
-/
theorem autocorrelation_bits (n : ℕ) (f : Cube n → ℝ) (v : Fourier.Cube n) :
    Fourier.autocorrelation (f ∘ bitsEquiv (Fin n)) v =
      mean (fun x : Cube n => f x * f (x + bitsEquiv (Fin n) v)) := by
  unfold Fourier.autocorrelation
  simp only [Function.comp_apply, bitsEquiv_translate]
  simpa only [Function.comp_def, add_comm] using mean_comp_equiv (bitsEquiv (Fin n))
    (fun x => f x * f (x + bitsEquiv (Fin n) v))

/--
@isnad1 id=eq.0h3v.s5.d49f0ac0dccd from=translated src=- shape=f6e25da1 vocab=f0e55828
-/
theorem walsh_autocorrelation {n : ℕ} (f : Fourier.Cube n → ℝ) (t : Fourier.Cube n) :
    Fourier.walsh (Fourier.autocorrelation f) t = Fourier.walsh f t ^ 2 := by
  unfold Fourier.walsh
  simp_rw [Fourier.autocorrelation_formula]
  have hswap :
      (fun x => (∑ s, Fourier.walsh f s ^ 2 * Fourier.phase s x) * Fourier.phase t x) =
      (fun x => Fourier.phase t x * (∑ s, Fourier.walsh f s ^ 2 * Fourier.phase s x)) := by
    funext x
    ring
  rw [hswap, Fourier.mean_mul_expansion]
  have ho (s : Fourier.Cube n) : Fourier.walsh (Fourier.phase t) s = if t = s then 1 else 0 :=
    Fourier.orthogonality t s
  simp [ho]
  rfl

/--
@isnad1 id=isbent.2h2v.s7.8f4f0a4a5df1 from=translated src=- shape=2e523b9e vocab=05c158a3
-/
theorem bent_of_autocorrelation (n : ℕ) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hc : ∀ v : Cube n, v ≠ 0 → mean (fun x => f x * f (x + v)) = 0) :
    Flatness.IsBent (f ∘ bitsEquiv (Fin n)) := by
  have hcorr (v : Fourier.Cube n) :
      Fourier.autocorrelation (f ∘ bitsEquiv (Fin n)) v =
        if v = (fun _ => false) then 1 else 0 := by
    rw [autocorrelation_bits]
    by_cases hv : v = (fun _ => false)
    · rw [ite_eq_left hv, hv, bitsEquiv_zero]
      have hsq (x : Cube n) : f x * f (x + 0) = 1 := by
        rcases hf x with hx | hx <;> simp [hx]
      simp only [hsq, mean_const]
    · rw [ite_eq_right hv]
      apply hc
      intro hz
      exact hv ((bitsEquiv (Fin n)).injective (hz.trans (bitsEquiv_zero n).symm))
  intro s
  rw [← walsh_autocorrelation]
  simp only [Fourier.walsh, hcorr, mean]
  simp [Fourier.phase, boolSign]

/--
@isnad1 id=eq.2h3v.s7.1761a12135f7 from=translated src=- shape=73504986 vocab=a990e649
-/
theorem bent_autocorrelation (n : ℕ) (f : Cube n → ℝ)
    (hf : Flatness.IsBent (f ∘ bitsEquiv (Fin n))) (v : Cube n) (hv : v ≠ 0) :
    mean (fun x => f x * f (x + v)) = 0 := by
  obtain ⟨w, rfl⟩ := (bitsEquiv (Fin n)).surjective v
  rw [← autocorrelation_bits]
  apply Flatness.autocorrelation_zero hf
  intro hw
  exact hv (hw ▸ bitsEquiv_zero n)

/--
@isnad1 id=isbent.2h3v.s10.055f611dc733 from=translated src=- shape=3d3fa439 vocab=81f76c67
-/
theorem bent_linearEquiv (n : ℕ) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hb : Flatness.IsBent (f ∘ bitsEquiv (Fin n))) (M : Cube n ≃ₗ[F2] Cube n) :
    Flatness.IsBent ((f ∘ M) ∘ bitsEquiv (Fin n)) := by
  apply bent_of_autocorrelation n (f ∘ M) (fun x => hf _)
  intro v hv
  have hmv : M v ≠ 0 := by
    intro h
    exact hv (M.injective (h.trans M.map_zero.symm))
  have hm := mean_comp_equiv M.toEquiv (fun x => f x * f (x + M v))
  dsimp only [Function.comp_def] at hm
  simp only [Function.comp_apply, map_add]
  exact hm.trans (bent_autocorrelation n f hb (M v) hmv)

end Hellinger.F2Model
