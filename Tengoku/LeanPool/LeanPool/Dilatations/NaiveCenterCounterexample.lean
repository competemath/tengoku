/-
Copyright (c) 2026 Arnaud Mayeux, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux, Jujian Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.Dilatations.RingComparison
public import Tengoku

/-!
# A counterexample to the naive ring comparison

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
The ring construction includes work by Arnaud Mayeux and Jujian Zhang from
`ProjConstruction/Proj` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open CategoryTheory Finset
open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)

/-! ### Erratum to Proposition 5.1 : the naive `I`-indexed center is *not* the right one

The printed `\citep[Proposition~5.1]{Mayeux}` identifies `𝒞[{(aᵢ)⁻¹∘Mᵢ}ᵢ∈I]` (dilating by the
center indexed directly by `i ∈ I`, one generator per index) with `A[M]`. This identification is
false : composition in `SingleObj A'` is multiplication, so the image of every morphism of this
naive center's dilatation is a product `c·∏ⱼ(mⱼ/aᵢⱼ)`, and not every element of `A[M]` has this
form. The concrete witness below : `A = ℤ[X]`, `a = 2`, `M = (X)`, and `(X+2)/2 ∈ A[M]` is not
reachable. See `\S`10.2 of the paper for the informal argument this formalizes. -/
namespace NaiveCenterCounterexample

open Family Polynomial Multicenter

/-- The single-center example with ideal `(X)` and denominator `2` in `ℤ[X]`. -/
abbrev CEx : Multicenter (Polynomial ℤ) where
  index := Unit
  ideal _ := Ideal.span {X}
  elem _ := 2

/-- The localization of the integers obtained by inverting `2`. -/
abbrev Target := Localization (Submonoid.powers (2 : ℤ))

open Family in
lemma CEx_elem_pow_eval (ν : CEx^ℕ) : (CEx.elem ^ ν).eval 0 = 2 ^ (ν ()) := by
  have hν : ν = Finsupp.single () (ν ()) := by
    apply Finsupp.ext; intro i; cases i; simp
  erw [hν, familyPow_def, Finsupp.prod_single_index (by simp)]
  simp [CEx]

/-- Evaluate a fraction representative at `X = 0` in the localization of `ℤ`. -/
def psiPreDil (x : CEx.PreDil) : Target :=
  IsLocalization.mk' Target (x.num.eval 0) (⟨2 ^ (x.pow ()), x.pow (), rfl⟩ : Submonoid.powers
    (2 : ℤ))

lemma psiPreDil_respects {x y : CEx.PreDil} (h : CEx.r x y) : psiPreDil x = psiPreDil y := by
  obtain ⟨β, hβ⟩ := h
  have hβ' := congrArg (Polynomial.eval 0) hβ
  simp only [eval_mul] at hβ'
  change x.num.eval 0 * (CEx.elem ^ (β + y.pow)).eval 0 =
    y.num.eval 0 * (CEx.elem ^ (β + x.pow)).eval 0 at hβ'
  rw [CEx_elem_pow_eval, CEx_elem_pow_eval] at hβ'
  simp only [Finsupp.add_apply] at hβ'
  refine IsLocalization.eq.mpr ⟨⟨2 ^ (β ()), β (), rfl⟩, ?_⟩
  change (2 : ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0) =
    2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0)
  calc (2 : ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0)
      = (2 ^ (β ()) * 2 ^ (y.pow ())) * x.num.eval 0 := by ring
    _ = 2 ^ (β () + y.pow ()) * x.num.eval 0 := by rw [pow_add]
    _ = x.num.eval 0 * 2 ^ (β () + y.pow ()) := by ring
    _ = y.num.eval 0 * 2 ^ (β () + x.pow ()) := hβ'
    _ = 2 ^ (β () + x.pow ()) * y.num.eval 0 := by ring
    _ = (2 ^ (β ()) * 2 ^ (x.pow ())) * y.num.eval 0 := by rw [pow_add]
    _ = 2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0) := by ring

/-- **The evaluation-at-`X=0` invariant `ψ`.** Descends to the dilatation ring because it kills
exactly what fraction-composition can produce from `(X)`-numerators. -/
def psi : (Polynomial ℤ)[CEx] → Target :=
  Multicenter.Dilatation.descFun psiPreDil (fun _ _ h => psiPreDil_respects h)

open Multicenter.Dilatation in
lemma psi_mul (x y : (Polynomial ℤ)[CEx]) : psi (x * y) = psi x * psi y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      change psi (mk (Dilatation.mul' x y)) = psi (mk x) * psi (mk y)
      change psiPreDil (Dilatation.mul' x y) = psiPreDil x * psiPreDil y
      unfold psiPreDil Dilatation.mul'
      simp only [Finsupp.add_apply, eval_mul, pow_add]
      rw [← IsLocalization.mk'_mul]
      congr 1

open Multicenter.Dilatation in
lemma X_add_two_mem :
    (X + 2 : Polynomial ℤ) ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  simp only [pow_one]
  change (X + 2 : Polynomial ℤ) ∈ Ideal.span {X} + Ideal.span {(2 : Polynomial ℤ)}
  apply Submodule.add_mem_sup
  · exact Ideal.mem_span_singleton_self X
  · exact Ideal.mem_span_singleton_self 2

open Multicenter.Dilatation in
/-- The target element `(X+2)/2 ∈ A[M]`, which we show is unreachable. -/
noncomputable def targetElement : (Polynomial ℤ)[CEx] :=
  Dilatation.frac (Finsupp.single () 1 : CEx^ℕ) ⟨X + 2, X_add_two_mem⟩

open Multicenter.Dilatation in
lemma psi_target : psi targetElement = 1 := by
  change psiPreDil ⟨_, _, _⟩ = 1
  unfold psiPreDil
  simp only [eval_add, eval_X, eval_ofNat, Finsupp.single_eq_same]
  norm_num

open Multicenter.Dilatation in
lemma psi_frac_eq_zero (m : Polynomial ℤ) (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ)))
    (hL : m ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ)) :
    psi (Dilatation.frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, hL⟩) = 0 := by
  change psiPreDil ⟨_, _, _⟩ = 0
  unfold psiPreDil
  have : m.eval 0 = 0 := by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    simp
  simp only [this]
  exact IsLocalization.mk'_zero _

/-- The naive `I`-indexed center `{(a_i, M_i)}` (here a single index): index `Unit`, morphism
`2`, sieve generated by `(X)` directly (not the large ideal). -/
def centerNaive : Center (CategoryTheory.SingleObj (Polynomial ℤ)) where
  I := Unit
  nonempty := ⟨()⟩
  dom _ := CategoryTheory.SingleObj.star (Polynomial ℤ)
  cod _ := CategoryTheory.SingleObj.star (Polynomial ℤ)
  mor _ := (2 : Polynomial ℤ)
  N _ := CategoryTheory.Dilatations.Prop51.Sieve.ofIdeal (Ideal.span {X})

/-- `CEx.elem ^ ν = 2 ^ (ν ())` as a polynomial identity (no evaluation), for arbitrary `ν`. -/
lemma CEx_elem_pow (ν : CEx^ℕ) : CEx.elem ^ ν = (2 : Polynomial ℤ) ^ (ν ()) := by
  have hν : ν = Finsupp.single () (ν ()) := by apply Finsupp.ext; intro i; cases i; simp
  erw [hν, familyPow_def, Finsupp.prod_single_index (by simp)]
  simp [CEx]

/-- `c·Xᵏ` always lies in the `k`-th large-ideal power, for every `c` and every `k`. -/
lemma cXk_mem (c : Polynomial ℤ) (k : ℕ) :
    c * X ^ k ∈ CEx.LargeIdeal ^ (Finsupp.single () k : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  have hXmem : (X : Polynomial ℤ) ∈ CEx.LargeIdeal () := by
    simp only [Multicenter.LargeIdeal, Submodule.add_eq_sup]
    exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self X)
  exact Ideal.mul_mem_left _ c (Ideal.pow_mem_pow hXmem k)

/-- `ψ` kills every fraction `(c·Xᵏ)/2ᵏ` with `k ≥ 1` (numerator divisible by `X`). -/
lemma psi_cXk_eq_zero (c : Polynomial ℤ) (k : ℕ) (hk : 1 ≤ k) :
    psi (Multicenter.Dilatation.frac (Finsupp.single () k : CEx^ℕ) ⟨c * X ^ k, cXk_mem c k⟩) =
      0 := by
  change psiPreDil ⟨_, _, _⟩ = 0
  unfold psiPreDil
  have : (c * X ^ k).eval 0 = 0 := by
    have : (0 : ℤ) ^ k = 0 := zero_pow (by omega)
    simp [this]
  simp only [this]
  exact IsLocalization.mk'_zero _

lemma mem_LargeIdeal_single1_of_mem_ideal {m : Polynomial ℤ}
    (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ))) :
    m ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  simp only [pow_one, Multicenter.LargeIdeal, Submodule.add_eq_sup]
  exact Submodule.mem_sup_left (M := Polynomial ℤ) hm

end NaiveCenterCounterexample

end CategoryTheory.Dilatations
