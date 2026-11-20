import Tengoku.Hellingerrepolean4.Hellinger.Flatness
import Tengoku.Hellingerrepolean4.Hellinger.TwoBitCase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms bent_two_hellinger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bent_two_hellinger_strict` (it only prints; the queue checks the axioms of every declaration). -/

/-! Definition bridges for the actual normalized Walsh conventions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.BentSmall

/--
@isnad1 id=eq.0h2v.s5.3d0171868242 from=translated src=- shape=4de382bb vocab=f47bb6a3
-/
theorem normalizedWalsh_eq (f : Fourier.Cube 2 → ℝ) (s : Bool × Bool) :
    TwoBitCase.normalizedWalsh f s = Fourier.walsh f ![s.1, s.2] := by
  unfold TwoBitCase.normalizedWalsh Fourier.walsh
  congr 1
  funext x
  congr 1
  rcases s with ⟨s₀, s₁⟩
  cases s₀ <;> cases s₁ <;> cases hx₀ : x 0 <;> cases hx₁ : x 1 <;>
    norm_num [Fourier.phase, Fin.prod_univ_two, boolSign, hx₀, hx₁]

/--
@isnad1 id=isbent2.1h1v.s4.7374e0fe3f10 from=translated src=- shape=2b0e8086 vocab=a23f7a51
-/
theorem flatness_implies_isBent2 (f : Fourier.Cube 2 → ℝ) (hb : Flatness.IsBent f) :
    TwoBitCase.IsBent2 f := by
  intro s
  rw [normalizedWalsh_eq, hb]
  norm_num

/--
@isnad1 id=le.3h2v.s7.12d156dc461b from=translated src=- shape=8448ce89 vocab=6b22d922
-/
theorem bent_two_hellinger (f : Fourier.Cube 2 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply f) ≤ 1 - root ρ :=
  TwoBitCase.bent2_hellinger f hf (flatness_implies_isBent2 f hb) ρ hρ

/--
@isnad1 id=lt.4h2v.s7.4748d2a03083 from=translated src=- shape=168adadd vocab=bce66604
-/
theorem bent_two_hellinger_strict (f : Fourier.Cube 2 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply f) < 1 - root ρ :=
  TwoBitCase.bent2_hellinger_strict f hf (flatness_implies_isBent2 f hb) ρ hρ hρpos

end Hellinger.BentSmall
