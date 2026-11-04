import Tengoku.ErdosLean.ErdosLean.Erdos1199.Parts.UltraBasics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #1199 — Part 2: algebraic laws of the `βℕ`-action

Paper: arXiv:2607.17333, eq. (2.2) `(p+q)x = p(qx)`, eq. (2.3) for the factor map `J`,
Lemma 3.1 (properties of `Δ₂`), and continuity of `p ↦ p x`.
-/

namespace Erdos1199

open Filter

open Classical in
/--
@isnad1 id=iff.0h3v.s5.e57390e153ab from=translated src=- shape=7eb29bab vocab=255e1d2d
-/
theorem act_apply_eq_true_iff (p : Ultrafilter ℕ) (x : Pt) (i : Idx) :
    act p x i = true ↔ {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ p := by
  unfold act; exact decide_eq_true_iff

/-- Eq. (2.2): `(p + q) · x = p · (q · x)`.
@isnad1 id=eq.0h3v.s5.5361c16833f5 from=translated src=- shape=96a587c4 vocab=346867d2
-/
theorem act_add (p q : Ultrafilter ℕ) (x : Pt) : act (p + q) x = act p (act q x) := by
  funext i
  rw [Bool.eq_iff_iff, act_apply_eq_true_iff, act_apply_eq_true_iff, mem_add_iff]
  have hset : {m : ℕ | {m' : ℕ | m + m' ∈
        {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}} ∈ q} =
      {m : ℕ | act q x (i.1, i.2 + stride i * (m : ℤ)) = true} := by
    ext m
    show {m' : ℕ | m + m' ∈ {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}} ∈ q ↔
      act q x (i.1, i.2 + stride i * (m : ℤ)) = true
    rw [act_apply_eq_true_iff]
    have : {m' : ℕ | m + m' ∈ {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}} =
        {m' : ℕ | x ((i.1, i.2 + stride i * (m : ℤ)).1, (i.1, i.2 + stride i * (m : ℤ)).2 +
          stride (i.1, i.2 + stride i * (m : ℤ)) * (m' : ℤ)) = true} := by
      ext m'
      change x _ = true ↔ x _ = true
      have h2 : i.2 + stride i * ((m + m' : ℕ) : ℤ) =
          i.2 + stride i * (m : ℤ) + stride (i.1, i.2 + stride i * (m : ℤ)) * (m' : ℤ) := by
        simp only [stride]; push_cast; ring
      rw [h2]
    rw [this]
  rw [hset]

/-- The principal ultrafilter acts as the shift `Tⁿ`.
@isnad1 id=eq.0h3v.s5.681f7e88c254 from=translated src=- shape=7e4865fa vocab=7ea3e310
-/
theorem act_pure_apply (n : ℕ) (x : Pt) (i : Idx) :
    act (pure n) x i = x (i.1, i.2 + stride i * (n : ℤ)) := by
  rw [Bool.eq_iff_iff, act_apply_eq_true_iff, Ultrafilter.mem_pure]
  exact Iff.rfl

/-- Eq. (2.3) for `J`: `p · (J x) = J (p · x)`.
@isnad1 id=eq.0h2v.s3.cf39790ea77c from=translated src=- shape=70fad52e vocab=c6c458fc
-/
theorem act_cmpl (p : Ultrafilter ℕ) (x : Pt) : act p (cmpl x) = cmpl (act p x) := by
  funext i
  have e : cmpl (act p x) i = !(act p x i) := rfl
  rw [e, Bool.eq_iff_iff, act_apply_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    act_apply_eq_true_iff, ← Ultrafilter.compl_mem_iff_notMem]
  have : {n : ℕ | cmpl x (i.1, i.2 + stride i * (n : ℤ)) = true} =
      {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}ᶜ := by
    ext n; simp [cmpl]
  rw [this]

/--
@isnad1 id=eq.0h1v.s3.499bac4464f4 from=translated src=- shape=47dcad53 vocab=d7edaacd
-/
theorem cmpl_cmpl (x : Pt) : cmpl (cmpl x) = x := by
  funext i; simp [cmpl]

/-- `J` has no fixed points.
@isnad1 id=ne.0h1v.s2.b44bea4b4d94 from=translated src=- shape=a365602c vocab=d7edaacd
-/
theorem cmpl_ne_self (x : Pt) : cmpl x ≠ x := by
  intro h
  have := congrFun h (0, 0)
  simp [cmpl] at this

/-- Lemma 3.1, eq. (3.4): `Δ₂ (p · x) = (D p) · (Δ₂ x)`.
@isnad1 id=eq.0h2v.s4.0ea20e32dee9 from=translated src=- shape=7b83e782 vocab=9bfa1761
-/
theorem dil_act (p : Ultrafilter ℕ) (x : Pt) : dil (act p x) = act (dbl p) (dil x) := by
  funext i
  have e : dil (act p x) i = act p x (2 * i.1 + 1, i.2) := rfl
  rw [e, Bool.eq_iff_iff, act_apply_eq_true_iff, act_apply_eq_true_iff, mem_dbl_iff]
  have : {n : ℕ | x (((2 * i.1 + 1, i.2) : Idx).1, ((2 * i.1 + 1, i.2) : Idx).2 +
        stride ((2 * i.1 + 1, i.2) : Idx) * (n : ℤ)) = true} =
      {n : ℕ | 2 * n ∈ {n : ℕ | dil x (i.1, i.2 + stride i * (n : ℤ)) = true}} := by
    ext n
    change x _ = true ↔ x _ = true
    have h2 : i.2 + stride ((2 * i.1 + 1, i.2) : Idx) * (n : ℤ) =
        i.2 + stride i * ((2 * n : ℕ) : ℤ) := by
      simp only [stride]; push_cast; ring
    simp only [h2]
  rw [this]

/-- Lemma 3.1: `Δ₂ J = J Δ₂`.
@isnad1 id=eq.0h1v.s3.5b3f35cc38f3 from=translated src=- shape=2e76f3a7 vocab=19e6aeca
-/
theorem dil_cmpl (x : Pt) : dil (cmpl x) = cmpl (dil x) := rfl

/-- Lemma 3.1: `Δ₂ 𝐜 = 𝐜`.
@isnad1 id=eq.0h1v.s3.95f9d1492e15 from=translated src=- shape=e343f8de vocab=2ec7bb48
-/
theorem dil_encode (c : ℤ → Bool) : dil (encode c) = encode c := rfl

/-- `p ↦ p · x` is continuous from `βℕ` to `Pt` (product topology).
@isnad1 id=continuo.0h1v.s4.27544f6d4037 from=translated src=- shape=e9ba6edb vocab=c7435fd6
-/
theorem continuous_act (x : Pt) : Continuous (fun p : Ultrafilter ℕ => act p x) := by
  refine continuous_pi fun i => ?_
  rw [continuous_bool_rng true]
  have : ((fun p : Ultrafilter ℕ => act p x i) ⁻¹' {true}) =
      {u : Ultrafilter ℕ | {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ u} := by
    ext u
    exact act_apply_eq_true_iff u x i
  rw [this]
  exact ⟨ultrafilter_isClosed_basic _, ultrafilter_isOpen_basic _⟩

end Erdos1199
