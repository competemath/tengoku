import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
set_option autoImplicit false

namespace FltWs21
namespace DepthSum

open Finset

/--
@isnad1 id=eq.1h5v.s6.736f8ad10e6b from=translated src=- shape=356ff759 vocab=b6283782
-/
theorem finsum_cond_eq_sum_filter {α M : Type*} [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (f : α → M)
    (F : Finset α) (hF : ∀ a, P a → f a ≠ 0 → a ∈ F) :
    (∑ᶠ (a : α) (_ : P a), f a) = ∑ a ∈ F.filter P, f a := by
  have h : (∑ᶠ (a : α) (_ : P a), f a) = ∑ᶠ a ∈ {a | P a}, f a := rfl
  rw [h]
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext a
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, coe_filter]
  constructor
  · rintro ⟨hP, hf⟩; exact ⟨⟨hF a hP hf, hP⟩, hf⟩
  · rintro ⟨⟨-, hP⟩, hf⟩; exact ⟨hP, hf⟩

end FltWs21.DepthSum

open FltWs21.DepthSum in
/--
@isnad1 id=and.4h13v.s9.0e6b5d1fd9b6 from=translated src=- shape=44ab64db vocab=bf744612
-/
theorem solution
    {Pl Pr : Type*} (E r : ℕ)
    (Ttot : Finset Pl) (ordZ : Pl → ℤ)
    (dep : Pl → ℕ) (hdep : ∀ V ∈ Ttot, 1 ≤ dep V ∧ dep V + 1 ≤ r * E)
    (T : ℕ → Finset Pl) (hT : ∀ p V, V ∈ T p ↔ V ∈ Ttot ∧ dep V = p)
    (horiz : Pr → Prop) (rk : Pr → ℕ) (lenU mult : Pr → ℕ∞) (depQ : Pr → ℕ)
    (hdepQ : ∀ Q, horiz Q → mult Q ≠ 0 →
      1 ≤ depQ Q ∧ depQ Q + 1 ≤ r * E ∧ (r : ℕ∞) * lenU Q = ((depQ Q * rk Q : ℕ) : ℕ∞) ∧
        1 ≤ rk Q ∧ lenU Q ≠ ⊤)
    (hfin : {Q : Pr | horiz Q ∧ mult Q ≠ 0}.Finite) :
    ((∑ V ∈ Ttot, (ordZ V).toNat : ℕ) : ℕ∞) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1), ((∑ V ∈ T p, (ordZ V).toNat : ℕ) : ℕ∞) ∧
    (∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1),
          ∑ᶠ (Q : Pr) (_ : horiz Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q := by
  classical
  refine ⟨?_, ?_⟩
  ·
    have hTf : ∀ p, T p = Ttot.filter (fun V => dep V = p) := by
      intro p; ext V; rw [hT, Finset.mem_filter]
    have hmaps : ∀ V ∈ Ttot, dep V ∈ Finset.Icc 1 (r * E - 1) := by
      intro V hV
      obtain ⟨h1, h2⟩ := hdep V hV
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    have hsplit : (∑ V ∈ Ttot, (ordZ V).toNat) = ∑ p ∈ Finset.Icc 1 (r * E - 1), ∑ V ∈ T p, (ordZ V).toNat := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hTf p]
    rw [hsplit, Nat.cast_sum]
  ·
    set F := hfin.toFinset with hFdef
    have hmemF : ∀ Q, Q ∈ F ↔ horiz Q ∧ mult Q ≠ 0 := fun Q => by rw [hFdef, Set.Finite.mem_toFinset]; rfl
    have hsupp : ∀ Q, (rk Q : ℕ∞) * mult Q ≠ 0 → mult Q ≠ 0 := fun Q h hm => h (by rw [hm, mul_zero])
    have hL : (∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q) = ∑ Q ∈ F.filter horiz, (rk Q : ℕ∞) * mult Q :=
      finsum_cond_eq_sum_filter horiz _ F (fun Q hQ hf => (hmemF Q).mpr ⟨hQ, hsupp Q hf⟩)
    have hFh : F.filter horiz = F := by
      ext Q; rw [Finset.mem_filter]; exact ⟨fun h => h.1, fun h => ⟨h, ((hmemF Q).mp h).1⟩⟩
    have hP : ∀ p ∈ Finset.Icc 1 (r * E - 1),
        (∑ᶠ (Q : Pr) (_ : horiz Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q)
          = ∑ Q ∈ F.filter (fun Q => depQ Q = p), (rk Q : ℕ∞) * mult Q := by
      intro p hp
      rw [finsum_cond_eq_sum_filter (fun Q => horiz Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)) _ F
        (fun Q hQ hf => (hmemF Q).mpr ⟨hQ.1, hsupp Q hf⟩)]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext Q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hQF, hQh, hcond⟩
        obtain ⟨hh, hm⟩ := (hmemF Q).mp hQF
        obtain ⟨-, -, heq, hrk, -⟩ := hdepQ Q hh hm
        refine ⟨hQF, ?_⟩
        rw [heq] at hcond
        have h' : depQ Q * rk Q = p * rk Q := by exact_mod_cast hcond
        exact Nat.eq_of_mul_eq_mul_right hrk h'
      · rintro ⟨hQF, rfl⟩
        obtain ⟨hh, hm⟩ := (hmemF Q).mp hQF
        obtain ⟨-, -, heq, -, -⟩ := hdepQ Q hh hm
        exact ⟨hQF, hh, heq⟩
    have hmaps : ∀ Q ∈ F, depQ Q ∈ Finset.Icc 1 (r * E - 1) := by
      intro Q hQ
      obtain ⟨hh, hm⟩ := (hmemF Q).mp hQ
      obtain ⟨h1, h2, -⟩ := hdepQ Q hh hm
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    rw [hL, hFh, Finset.sum_congr rfl hP, Finset.sum_fiberwise_of_maps_to hmaps]
