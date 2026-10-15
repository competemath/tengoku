/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/
module

public import Tengoku.LeanPool.LeanPool.Monsky.Square
public import Tengoku

/-!
# LeanPool.Monsky.MonskyEven

Imported Lean Pool material for `LeanPool.Monsky.MonskyEven`.
-/

@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Finset

/- This rewriting is for convenience. -/
/-- `disjointSet X f` states that `f` sends distinct elements of `X` to disjoint sets. -/
def disjointSet {α β : Type} (X : Set α) (f : α → Set β) :=
  ∀ a₁ a₂, a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ → Disjoint (f a₁) (f a₂)
/-- `covers X Y f` states that `Y` is the union of `f a` over `a ∈ X`. -/
def covers {α β} (X : Set α) (Y : Set β) (f : α → Set β) := Y = ⋃ a ∈ X, f a

/--
@isnad1 id=iff.0h2v.s6.acd0d4eb0c9f from=translated src=- shape=c099e532 vocab=80ed5e7a
-/
lemma isCover_iff (X : Set ℝ²) (S : Set Triangle)
    : isDisjointCover X S ↔ covers S X closedHull ∧ disjointSet S openHull := by
  simp only [isDisjointCover, isCover, isDisjointPolygonSet, ne_eq, covers, disjointSet,
    and_congr_right_iff]
  intro _
  exact ⟨fun h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq ↦ h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq,
    fun h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq ↦ h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq⟩

/--
@isnad1 id=disjoint.3h5v.s6.7c66dd6673b1 from=translated src=- shape=4ce42b5b vocab=92170ce8
-/
lemma disjoint_aux {α β : Type} (S₁ S₂ : Set α) (f : α → Set β) (h₁ : disjointSet S₁ f)
    (h₂ : disjointSet S₂ f)
    (h₃ : ∀ a₁ a₂, a₁ ∈ S₁ → a₂ ∈ S₂ → Disjoint (f a₁) (f a₂)) :
    disjointSet (S₁ ∪ S₂) f := by
  intro a₁ a₂ ha₁ ha₂ hneq
  obtain ha₁ | ha₁ := ha₁ <;> obtain ha₂ | ha₂ := ha₂
  · exact h₁ a₁ a₂ ha₁ ha₂ hneq
  · exact h₃ a₁ a₂ ha₁ ha₂
  · exact (h₃ a₂ a₁ ha₂ ha₁ ).symm
  · exact h₂ a₁ a₂ ha₁ ha₂ hneq

/-
  The square can be covered by an even number of triangles.
-/

/- These two triangles dissect the square and have equal area.-/
/-- The lower triangle of the standard two-triangle dissection of the unit square. -/
def Δ₀ : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
/-- The upper triangle of the standard two-triangle dissection of the unit square. -/
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)

/--
@isnad1 id=eq.0h0v.s4.8ba0eb5c9aad from=translated src=- shape=c29dca45 vocab=3bbec836
-/
lemma areaΔ₀ : triangleArea Δ₀ = 1 / 2 := by
  simp [triangleArea, det, Δ₀]

/--
@isnad1 id=eq.0h0v.s4.1bff3214a691 from=translated src=- shape=c29dca45 vocab=b1165636
-/
lemma areaΔ₀' : triangleArea Δ₀' = 1 / 2 := by
  simp [triangleArea, det, Δ₀']

/- Now we show how a cover of size two implies a cover of any even size.-/

/- Elementary stuff about scaling (only in the y direction).-/

/-- Scales the second coordinate of a plane vector by `a`. -/
def scaleVector (a : ℝ) (y : ℝ²) : ℝ² := !₂[y 0, a * y 1]

/-- Applies `scaleVector a` to every vertex of a triangle. -/
def scaleTriangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ scaleVector a (T i)

/--
@isnad1 id=eq.0h2v.s5.621d756eb9eb from=translated src=- shape=7d46aa24 vocab=71d44d20
-/
lemma scaleTriangle_det (a : ℝ) (T : Triangle) :
    det (scaleTriangle a T) = a * det T := by
  simp [det, scaleTriangle, scaleVector]
  ring

/--
@isnad1 id=eq.0h2v.s5.1a3d4217ee33 from=translated src=- shape=8dc79a9e vocab=21c707ee
-/
lemma scaleTriangle_area (a : ℝ) (T : Triangle)
    : triangleArea (scaleTriangle a T) = |a| * (triangleArea T) := by
  simp only [triangleArea, scaleTriangle_det a T, abs_mul, mul_div_assoc]

/- Elementary stuff about translating (only in the y direction).-/

/-- Translates the second coordinate of a plane vector by `a`. -/
def translateVector (a : ℝ) (x : ℝ²) : ℝ² := !₂[x 0, a + x 1]
/-- Applies `translateVector a` to every vertex of a triangle. -/
def translateTriangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ translateVector a (T i)

/--
@isnad1 id=eq.0h2v.s4.15efb0fa1a60 from=translated src=- shape=375580be vocab=d3b74525
-/
lemma translateTriangle_det (a : ℝ) (T : Triangle) :
    det (translateTriangle a T) = det T := by
  simp [det, translateTriangle, translateVector]
  ring

/--
@isnad1 id=eq.0h2v.s4.3d4739b422b2 from=translated src=- shape=375580be vocab=41758abd
-/
lemma translateTriangle_area (a : ℝ) (T : Triangle)
    : triangleArea (translateTriangle a T) = (triangleArea T) := by
  simp only [triangleArea, translateTriangle_det]

/--
@isnad1 id=injectiv.0h1v.s5.6886f8ef9c5a from=translated src=- shape=d3b6fea7 vocab=178594da
-/
lemma translate_injective {T : Triangle} :
    Function.Injective (fun (a : ℝ) ↦ translateTriangle a T) := by
  intro _ _ hsame
  have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
  simp [translateTriangle, translateVector] at hsame
  assumption

-- Here a different try. Just give a very explicit cover.
/-- The `n` translated copies of the scaled lower triangle `Δ₀` covering the square. -/
noncomputable def zigPartCover (n : ℕ)
  := Finset.image
    (fun (s : Fin n) ↦
      translateTriangle ((s : ℝ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀)) univ

/-- The `n` translated copies of the scaled upper triangle `Δ₀'` covering the square. -/
noncomputable def zagPartCover (n : ℕ)
  := Finset.image
    (fun (s : Fin n) ↦
      translateTriangle ((s : ℝ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀')) univ

/--
@isnad1 id=and.0h1v.s5.3e484e4eea47 from=translated src=- shape=4ccec5e6 vocab=fc486226
-/
lemma zig_zag_cover_size_aux (n : ℕ) :
    (zigPartCover n).card = n ∧ (zagPartCover n).card = n := by
  rw [zigPartCover, zagPartCover]
  constructor <;> (
    rw [Finset.card_image_of_injective]
    · exact card_fin n
    · intro s s' hsame
      have hn : (n : ℝ) ≠ 0 := fun h ↦ Fin.elim0 (Fin.cast ((Nat.cast_eq_zero).1 h) s)
      have hsame := translate_injective hsame
      simp_all only [div_eq_div_iff hn hn, mul_eq_mul_right_iff, or_false, Nat.cast_inj]
      exact Fin.eq_of_val_eq hsame
    )

/--
@isnad1 id=eq.0h1v.s8.c1a2b43e7bdd from=translated src=- shape=fd1fd6cb vocab=4aa4fa79
-/
lemma zig_zag_cover_size (n : ℕ) : (zigPartCover n ∪ zagPartCover n).card = 2 * n := by
  have h : (zigPartCover n ∩ zagPartCover n).card = 0 := by
    rw [card_eq_zero, ←disjoint_iff_inter_eq_empty, disjoint_left]
    intro _ h₁ h₂
    simp only [zigPartCover, one_div, mem_image, mem_univ, true_and, zagPartCover] at h₁ h₂
    have ⟨s₁,hs₁⟩ := h₁
    have ⟨s₂,hs₂⟩ := h₂
    rw [←hs₂] at hs₁
    have hsame := congrArg (fun Δ ↦ Δ 0 0) hs₁
    simp [translateTriangle, translateVector, scaleTriangle, scaleVector, Δ₀, Δ₀'] at hsame
  simp_rw [card_union, zig_zag_cover_size_aux, h, tsub_zero, two_mul]

/--
@isnad1 id=eq.1h2v.s7.5822bbf699e2 from=translated src=- shape=1cc64ccc vocab=1f1d9445
-/
lemma zig_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zigPartCover n → triangleArea Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zigPartCover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translateTriangle_area, scaleTriangle_area, areaΔ₀]
  simp

/--
@isnad1 id=eq.1h2v.s7.092ba8e70aa2 from=translated src=- shape=1cc64ccc vocab=3d759525
-/
lemma zag_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zagPartCover n → triangleArea Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zagPartCover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translateTriangle_area, scaleTriangle_area, areaΔ₀']
  simp

/--
@isnad1 id=eq.4h4v.s6.332c6b47b54d from=translated src=- shape=cba655c2 vocab=0ba01250
-/
lemma fin_el_bound {n : ℕ} {x : ℝ} {s₁ s₂ : Fin n} (h₁l : x - 1 < s₁) (h₁u : s₁ < x)
    (h₂l : x - 1 < s₂) (h₂u : s₂ < x) : s₁ = s₂ := by
  wlog hl : s₁ ≤ s₂
  · refine (this h₂l h₂u h₁l h₁u (le_of_not_ge hl)).symm
  · refine Fin.le_antisymm_iff.mpr ⟨hl, ?_⟩
    by_contra hc
    rw [not_le, @Fin.lt_def, @Nat.lt_iff_add_one_le,
        ←Nat.cast_le (α := ℝ), @Nat.cast_add, @Nat.cast_one] at hc
    linarith

/--
@isnad1 id=disjoint.0h1v.s6.fe0c6b405fb0 from=translated src=- shape=a73f2b07 vocab=cd5df55e
-/
lemma zig_open_disjoint {n : ℕ} : disjointSet ((zigPartCover n) : Set Triangle) openHull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp only [zigPartCover, one_div, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by simp [det, translateTriangle, scaleTriangle, Δ₀,
      translateVector, scaleVector, Nat.ne_zero_of_lt nsign])] at hx₁
    rw [←hs₂, open_triangle_iff (by simp [det, translateTriangle, scaleTriangle, Δ₀,
      translateVector, scaleVector, Nat.ne_zero_of_lt nsign])] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    refine hΔneq ?_
    simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
      translateVector, Tside, scaleVector, Δ₀] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    rw [←hs₁, ←hs₂, fin_el_bound (x := ↑n * x.ofLp 1) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp [Nat.eq_zero_of_not_pos nsign, zigPartCover, disjointSet]

/--
@isnad1 id=disjoint.0h1v.s6.7e2695bd81a7 from=translated src=- shape=a73f2b07 vocab=4224a386
-/
lemma zag_open_disjoint {n : ℕ} : disjointSet ((zagPartCover n) : Set Triangle) openHull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp only [zagPartCover, one_div, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by
      simp [det, translateTriangle, scaleTriangle, Δ₀', translateVector, scaleVector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₁
    rw [←hs₂, open_triangle_iff (by
      simp [det, translateTriangle, scaleTriangle, Δ₀', translateVector, scaleVector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    refine hΔneq ?_
    simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
      translateVector, Tside, scaleVector, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    rw [←hs₁, ←hs₂, fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp [Nat.eq_zero_of_not_pos nsign, zagPartCover, disjointSet]

/--
@isnad1 id=disjoint.2h3v.s8.bf138688af9f from=translated src=- shape=8065dfea vocab=187fd75a
-/
lemma zig_zag_open_disjoint {n : ℕ}
    : ∀ a₁ a₂, a₁ ∈ (zigPartCover n) → a₂ ∈ (zagPartCover n) →
      Disjoint (openHull a₁) (openHull a₂) := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂
    simp only [zigPartCover, one_div, mem_image, mem_univ, true_and, zagPartCover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by simp [det, translateTriangle, scaleTriangle, Δ₀,
      translateVector, scaleVector, Nat.ne_zero_of_lt nsign])] at hx₁
    rw [←hs₂, open_triangle_iff (by
      simp [det, translateTriangle, scaleTriangle, Δ₀', translateVector, scaleVector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₁ := hx₂ 1
    have hx₂₂ := hx₂ 2
    simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
      translateVector, Tside, scaleVector, Δ₀, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    have l := fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)
    rw [l] at hx₁₀ hx₁₂
    linarith
  · simp [Nat.eq_zero_of_not_pos nsign, zagPartCover]

end Monsky
end LeanPool
