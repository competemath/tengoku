import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KatzLevelP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

variable {A B : Type*} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

def smulX (a : ℤ) (x : A) : A :=
  (W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)

/--
@isnad1 id=eq.0h3v.s4.caecc5e44817 from=translated src=- shape=a83319ae vocab=47be2f62
-/
@[simp] theorem smulX_one (x : A) : smulX W 1 x = x := by
  simp [smulX, WeierstrassCurve.Φ_one, WeierstrassCurve.ΨSq_one]

/--
@isnad1 id=eq.1h6v.s7.2c0c1ab5b4e8 from=translated src=- shape=025442f1 vocab=3b18cced
-/
theorem map_smulX (f : A →+* B) {a : ℤ} {x : A} (h : IsUnit ((W.ΨSq a).eval x)) :
    f (smulX W a x) = smulX (W.map f) a (f x) := by
  obtain ⟨u, hu⟩ := h
  rw [smulX, smulX, WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, Polynomial.eval_map,
    Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply, map_mul, ← hu,
    Ring.inverse_unit]
  change _ = _ * Ring.inverse ((Units.map (f : A →* B) u : Bˣ) : B)
  rw [Ring.inverse_unit]
  rfl

variable (p : ℕ)

def veluTLine (x : A) : A :=
  ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), (6 * smulX W a x ^ 2 + W.b₂ * smulX W a x + W.b₄)

def veluWLine (x : A) : A :=
  ∑ a ∈ Finset.Icc 1 ((p - 1) / 2),
    (W.Ψ₂Sq.eval (smulX W a x) + smulX W a x * (6 * smulX W a x ^ 2 + W.b₂ * smulX W a x + W.b₄))

def quotientByLine (x : A) : WeierstrassCurve A where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * veluTLine W p x
  a₆ := W.a₆ - W.b₂ * veluTLine W p x - 7 * veluWLine W p x

variable (x : A)

/--
@isnad1 id=eq.0h4v.s4.6e5f1f45dd52 from=translated src=- shape=229ced54 vocab=ec2c8300
-/
@[simp] theorem quotientByLine_a₁ : (quotientByLine W p x).a₁ = W.a₁ := rfl
/--
@isnad1 id=eq.0h4v.s4.2baa68edf011 from=translated src=- shape=229ced54 vocab=cb257115
-/
@[simp] theorem quotientByLine_a₂ : (quotientByLine W p x).a₂ = W.a₂ := rfl
/--
@isnad1 id=eq.0h4v.s4.570904109201 from=translated src=- shape=229ced54 vocab=a3c0f004
-/
@[simp] theorem quotientByLine_a₃ : (quotientByLine W p x).a₃ = W.a₃ := rfl
/--
@isnad1 id=eq.0h4v.s6.64399617fc49 from=translated src=- shape=715ca472 vocab=9d105a43
-/
theorem quotientByLine_a₄ : (quotientByLine W p x).a₄ = W.a₄ - 5 * veluTLine W p x := rfl
/--
@isnad1 id=eq.0h4v.s6.eeb24c43f658 from=translated src=- shape=8b6a7626 vocab=d44e6a3f
-/
theorem quotientByLine_a₆ :
    (quotientByLine W p x).a₆ = W.a₆ - W.b₂ * veluTLine W p x - 7 * veluWLine W p x := rfl

/--
@isnad1 id=eq.1h4v.s5.0ed36a814163 from=translated src=- shape=24208cfd vocab=b19909c2
-/
theorem quotientByLine_of_le_two (hp : p ≤ 2) : quotientByLine W p x = W := by
  have h0 : (p - 1) / 2 = 0 := by omega
  ext <;> simp [quotientByLine, veluTLine, veluWLine, h0]

/--
@isnad1 id=eq.1h6v.s7.8c0d7a39deba from=translated src=- shape=8803864d vocab=88a7d1a4
-/
theorem quotientByLine_map (f : A →+* B)
    (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    (quotientByLine W p x).map f = quotientByLine (W.map f) p (f x) := by
  have hT : f (veluTLine W p x) = veluTLine (W.map f) p (f x) := by
    simp only [veluTLine, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_smulX W f (h a ha), WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, map_ofNat]
  have hW : f (veluWLine W p x) = veluWLine (W.map f) p (f x) := by
    simp only [veluWLine, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hx := map_smulX W f (h a ha)
    simp only [map_add, map_mul, map_pow, hx, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
      map_ofNat, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.map_b₆, eval_add, eval_mul, eval_pow,
      eval_C, eval_X, eval_ofNat]
  ext
  · simp [quotientByLine]
  · simp [quotientByLine]
  · simp [quotientByLine]
  · simp [quotientByLine, hT, map_ofNat]
  · simp [quotientByLine, hT, hW, map_ofNat]

end LevelP

namespace LevelPData

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) (D : LevelPData A)

def quotientBySndLine : WeierstrassCurve A := LevelP.quotientByLine W p D.xQ

def quotientByFstLine : WeierstrassCurve A := LevelP.quotientByLine W p D.xP

/--
@isnad1 id=eq.0h4v.s4.8151c0b7fff3 from=translated src=- shape=9852fccc vocab=0fd47fb4
-/
@[simp] theorem quotientBySndLine_swap : D.swap.quotientBySndLine W p = D.quotientByFstLine W p := rfl

/--
@isnad1 id=eq.0h4v.s4.36fd883b203b from=translated src=- shape=9852fccc vocab=0fd47fb4
-/
@[simp] theorem quotientByFstLine_swap : D.swap.quotientByFstLine W p = D.quotientBySndLine W p := rfl

/--
@isnad1 id=eq.0h4v.s4.2a18bace8b46 from=translated src=- shape=5bbab7f5 vocab=663c2344
-/
theorem quotientBySndLine_eq : D.quotientBySndLine W p = LevelP.quotientByLine W p D.xQ := rfl

/--
@isnad1 id=eq.0h4v.s4.caaf2754d1ad from=translated src=- shape=5bbab7f5 vocab=69ac3cb3
-/
theorem quotientByFstLine_eq : D.quotientByFstLine W p = LevelP.quotientByLine W p D.xP := rfl

end LevelPData

end ModularCurve

end
