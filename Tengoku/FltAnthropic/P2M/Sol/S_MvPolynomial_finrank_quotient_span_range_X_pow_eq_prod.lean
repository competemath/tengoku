import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod

set_option autoImplicit false

noncomputable section

open _root_.MvPolynomial

universe u v

namespace MvPolynomial
export _root_.MvPolynomial (X restrictSupport funext ext support basisRestrictSupport mem_ideal_span_monomial_image monomial coeff_zero mem_support_iff mem_supported mem_restrictSupport_iff X_pow_eq_monomial)
namespace TruncatedBox
open _root_.MvPolynomial

variable (k : Type u) [CommRing k] {ι : Type v} (N : ι → ℕ)

def box : Set (ι →₀ ℕ) := {m | ∀ i, m i < N i}

def K : Ideal (MvPolynomial ι k) :=
  Ideal.span (Set.range fun i : ι => (X i : MvPolynomial ι k) ^ N i)

/--
@isnad1 id=eq.0h3v.s8.24e38d5f786a from=translated src=- shape=353e4e3e vocab=5716a9fa
-/
theorem K_eq : K k N = Ideal.span ((fun s => monomial s (1 : k)) ''
    Set.range fun i : ι => Finsupp.single i (N i)) := by
  rw [K, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range ?_)
  funext i
  exact X_pow_eq_monomial

variable {k N}

/--
@isnad1 id=iff.0h4v.s7.4774dd0393dc from=translated src=- shape=3cb5c2f2 vocab=7803c620
-/
theorem mem_K_iff (P : MvPolynomial ι k) : P ∈ K k N ↔ ∀ m ∈ P.support, m ∉ box N := by
  rw [K_eq, mem_ideal_span_monomial_image]
  refine forall₂_congr fun m _ => ?_
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hle⟩ hm
    have := hm i
    rw [Finsupp.single_le_iff] at hle
    omega
  · intro hm
    simp only [box, Set.mem_ofPred_eq, not_forall, not_lt] at hm
    obtain ⟨i, hi⟩ := hm
    exact ⟨_, ⟨i, rfl⟩, Finsupp.single_le_iff.2 hi⟩

/--
@isnad1 id=iff.0h4v.s8.d2b02d17e3fc from=translated src=- shape=45d0cfb6 vocab=f03503ce
-/
theorem mem_restrictSupport_iff (P : MvPolynomial ι k) :
    P ∈ restrictSupport k (box N) ↔ ∀ m ∈ P.support, m ∈ box N :=
  (MvPolynomial.mem_restrictSupport_iff k).trans Iff.rfl

/--
@isnad1 id=iscompl.0h3v.s8.41a4d2b06e06 from=translated src=- shape=24d26adc vocab=3e176532
-/
theorem isCompl : IsCompl ((K k N).restrictScalars k) (restrictSupport k (box N)) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro P hK hbox
    rw [Submodule.restrictScalars_mem, mem_K_iff] at hK
    rw [mem_restrictSupport_iff] at hbox
    ext m
    rw [coeff_zero]
    by_contra hne
    have hm : m ∈ P.support := by rwa [MvPolynomial.mem_support_iff]
    exact hK m hm (hbox m hm)
  · rw [codisjoint_iff, eq_top_iff]
    rintro P -

    set P₁ : MvPolynomial ι k :=
      AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun m => m ∈ box N) (AddMonoidAlgebra.coeff P)) with hP₁
    set P₂ : MvPolynomial ι k :=
      AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun m => m ∉ box N) (AddMonoidAlgebra.coeff P)) with hP₂
    have hsum : P₁ + P₂ = P := by
      apply AddMonoidAlgebra.coeff_injective
      rw [AddMonoidAlgebra.coeff_add]
      exact Finsupp.filter_add_filter_not (AddMonoidAlgebra.coeff P) _
    rw [← hsum, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [Submodule.restrictScalars_mem, mem_K_iff]
      intro m hm
      have hm' : m ∈ (Finsupp.filter (fun m => m ∉ box N) (AddMonoidAlgebra.coeff P)).support := hm
      rw [Finsupp.support_filter, Finset.mem_filter] at hm'
      exact hm'.2
    · rw [mem_restrictSupport_iff]
      intro m hm
      have hm' : m ∈ (Finsupp.filter (fun m => m ∈ box N) (AddMonoidAlgebra.coeff P)).support := hm
      rw [Finsupp.support_filter, Finset.mem_filter] at hm'
      exact hm'.2

def boxEquiv [Fintype ι] : box N ≃ (∀ i, Fin (N i)) where
  toFun m := fun i => ⟨m.1 i, m.2 i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ), fun i => by
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact (f i).isLt⟩
  left_inv m := by
    ext i
    exact congrFun (Finsupp.coe_equivFunOnFinite_symm _) i
  right_inv f := by
    funext i
    exact Fin.ext (congrFun (Finsupp.coe_equivFunOnFinite_symm _) i)

variable (k N) in
/--
@isnad1 id=eq.0h3v.s8.848de8d761df from=translated src=- shape=b2e82797 vocab=ae44d89e
-/
theorem finrank_quotient [Nontrivial k] [Fintype ι] :
    Module.finrank k (MvPolynomial ι k ⧸ K k N) = ∏ i, N i := by
  have e₁ : (MvPolynomial ι k ⧸ (K k N).restrictScalars k) ≃ₗ[k] MvPolynomial ι k ⧸ K k N :=
    Submodule.Quotient.restrictScalarsEquiv k (K k N)
  have e₂ : (MvPolynomial ι k ⧸ (K k N).restrictScalars k) ≃ₗ[k] restrictSupport k (box N) :=
    Submodule.quotientEquivOfIsCompl _ _ isCompl
  rw [← e₁.finrank_eq, e₂.finrank_eq, Module.finrank_eq_nat_card_basis (basisRestrictSupport k (box N)),
    Nat.card_congr (boxEquiv (N := N)), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_fin (N i)

end MvPolynomial.TruncatedBox

/--
@isnad1 id=eq.0h3v.s9.c3db6f6a5561 from=translated src=- shape=f882727f vocab=dab7e1a3
-/
theorem solution
    (k : Type u) [CommRing k] [Nontrivial k] {ι : Type v} [Fintype ι] (N : ι → ℕ) :
    Module.finrank k (MvPolynomial ι k ⧸
      Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k) ^ N i)) = ∏ i, N i :=
  MvPolynomial.TruncatedBox.finrank_quotient k N
