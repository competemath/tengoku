import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Multipeak
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Periodization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators
open Finset Set

namespace Erdos1133

private theorem sixth_tail_product_bound {C D a b d : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : D * (a+b) ≤ d) :
    C / (1+d)^6 ≤ (C / D^2) * (1/a^2) * (1/b^2) := by
  have hDp : 0 < D := by linarith
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hDa : D*a ≤ d := by nlinarith
  have hDb : b ≤ d := by nlinarith
  have hdp : 0 ≤ d := hbp.le.trans hDb
  have hsq1 := pow_le_pow_left₀ (by positivity : 0 ≤ D*a) hDa 2
  have hsq2 := pow_le_pow_left₀ hbp.le hDb 2
  have hden : D^2*a^2*b^2 ≤ (1+d)^6 := by
    calc
      D^2*a^2*b^2 = (D*a)^2*b^2 := by ring
      _ ≤ d^2*d^2 := mul_le_mul hsq1 hsq2 (by positivity) (by positivity)
      _ = d^4 := by ring
      _ ≤ (1+d)^4 := pow_le_pow_left₀ hdp (by linarith) 4
      _ ≤ (1+d)^6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc
    C / (1+d)^6 ≤ C/(D^2*a^2*b^2) :=
      div_le_div_of_nonneg_left hC (by positivity) hden
    _ = (C / D^2) * (1/a^2) * (1/b^2) := by field_simp

/-- Every positive period translate is far from the rightmost packet, with
an additional distance proportional to the index gap.-/
private theorem packet_positive_shift_distance (s : Finset ℤ) (hs : s.Nonempty)
    (c : ℤ → ℝ) {N D x : ℝ} (hD : 0 < D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hx : |x| ≤ N) (k : ℤ) (hk : 0 < k) (j : ℤ) (hj : j ∈ s) :
    D*((k:ℝ)+((s.max' hs-j+1:ℤ):ℝ)) ≤ |x+2*N*k-c j| := by
  let m := s.max' hs
  have hm : m ∈ s := s.max'_mem hs
  have hjm : j ≤ m := s.le_max' j hj
  have hN : 2*D ≤ N := by
    have hb := hbound m hm
    rcases hb with ⟨h1,h2⟩
    linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hor := horder j hj m hm hjm
  have hb := (hbound m hm).2
  have hxr := (abs_le.mp hx).1
  have hgap : 0 ≤ ((m-j:ℤ):ℝ) := by exact_mod_cast sub_nonneg.mpr hjm
  have hdist : D*((k:ℝ)+((m-j+1:ℤ):ℝ)) ≤ x+2*N*k-c j := by
    push_cast at hor hgap ⊢
    nlinarith [mul_nonneg (show 0 ≤ 2*N-D by linarith) (show 0 ≤ (k:ℝ)-1 by linarith)]
  exact hdist.trans (le_abs_self _)

private theorem packet_negative_shift_distance (s : Finset ℤ) (hs : s.Nonempty)
    (c : ℤ → ℝ) {N D x : ℝ} (hD : 0 < D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hx : |x| ≤ N) (k : ℤ) (hk : k < 0) (j : ℤ) (hj : j ∈ s) :
    D*((-(k:ℝ))+((j-s.min' hs+1:ℤ):ℝ)) ≤ |x+2*N*k-c j| := by
  let m := s.min' hs
  have hm : m ∈ s := s.min'_mem hs
  have hmj : m ≤ j := s.min'_le j hj
  have hN : 2*D ≤ N := by
    have hb := hbound m hm
    rcases hb with ⟨h1,h2⟩
    linarith
  have hk1 : (1:ℝ) ≤ -(k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ -k by omega)
  have hor := horder m hm j hj hmj
  have hb := (hbound m hm).1
  have hxr := (abs_le.mp hx).2
  have hgap : 0 ≤ ((j-m:ℤ):ℝ) := by exact_mod_cast sub_nonneg.mpr hmj
  have hdist : D*((-(k:ℝ))+((j-m+1:ℤ):ℝ)) ≤ -(x+2*N*k-c j) := by
    push_cast at hor hgap ⊢
    nlinarith [mul_nonneg (show 0 ≤ 2*N-D by linarith) (show 0 ≤ -(k:ℝ)-1 by linarith)]
  exact hdist.trans (neg_le_abs _)

/-- A bound for each nonzero period translate of all packets, independent
of both the number of packets and the period length.
@isnad1 id=le.7h8v.s8.7a00c2c1e4b2 from=translated src=- shape=55db2b77 vocab=e8320028
-/
theorem multipeak_shift_norm_bound (s : Finset ℤ) (c : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C D N : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hdecay : ∀ j ∈ s, ∀ t : ℝ, ‖g j t‖ ≤ C/(1+|t-c j|)^6)
    (x : ℝ) (hx : |x| ≤ N) (k : ℤ) (hk : k ≠ 0) :
    ∑ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ ≤
      ((C/D^2)*squareTailMass)*(1/(k:ℝ)^2) := by
  classical
  by_cases hs : s.Nonempty
  · have hDp : 0 < D := by linarith
    rcases lt_or_gt_of_ne hk with hkneg | hkpos
    · let m := s.min' hs
      have hpoint : ∀ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ ≤
          ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m-1):ℤ):ℝ)^2)) := by
        intro j hj
        have hb : (1:ℝ) ≤ ((j-s.min' hs+1:ℤ):ℝ) := by
          exact_mod_cast (show (1:ℤ) ≤ j-s.min' hs+1 by have := s.min'_le j hj; omega)
        have hp := sixth_tail_product_bound hC hD
          (show (1:ℝ) ≤ -(k:ℝ) by exact_mod_cast (show (1:ℤ) ≤ -k by omega)) hb
          (packet_negative_shift_distance s hs c hDp hbound horder hx k hkneg j hj)
        have he : ((j-s.min' hs+1:ℤ):ℝ) = ((j-(m-1):ℤ):ℝ) := by dsimp [m]; push_cast; ring
        rw [he, neg_sq] at hp
        exact (hdecay j hj _).trans hp
      calc
        _ ≤ ∑ j ∈ s, ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m-1):ℤ):ℝ)^2)) := sum_le_sum hpoint
        _ = ((C/D^2)*(1/(k:ℝ)^2))*(∑ j ∈ s, 1/(((j-(m-1):ℤ):ℝ)^2)) := by rw [mul_sum]
        _ ≤ ((C/D^2)*(1/(k:ℝ)^2))*squareTailMass :=
          mul_le_mul_of_nonneg_left (shifted_square_sum_le s (m-1)) (by positivity)
        _ = _ := by ring
    · let m := s.max' hs
      have hpoint : ∀ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ ≤
          ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m+1):ℤ):ℝ)^2)) := by
        intro j hj
        have hb : (1:ℝ) ≤ ((s.max' hs-j+1:ℤ):ℝ) := by
          exact_mod_cast (show (1:ℤ) ≤ s.max' hs-j+1 by have := s.le_max' j hj; omega)
        have hp := sixth_tail_product_bound hC hD
          (show (1:ℝ) ≤ k by exact_mod_cast hkpos) hb
          (packet_positive_shift_distance s hs c hDp hbound horder hx k hkpos j hj)
        have he : ((s.max' hs-j+1:ℤ):ℝ) = -((j-(m+1):ℤ):ℝ) := by dsimp [m]; push_cast; ring
        rw [he, neg_sq] at hp
        exact (hdecay j hj _).trans hp
      calc
        _ ≤ ∑ j ∈ s, ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m+1):ℤ):ℝ)^2)) := sum_le_sum hpoint
        _ = ((C/D^2)*(1/(k:ℝ)^2))*(∑ j ∈ s, 1/(((j-(m+1):ℤ):ℝ)^2)) := by rw [mul_sum]
        _ ≤ ((C/D^2)*(1/(k:ℝ)^2))*squareTailMass :=
          mul_le_mul_of_nonneg_left (shifted_square_sum_le s (m+1)) (by positivity)
        _ = _ := by ring
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp only [he, sum_empty]
    exact mul_nonneg (mul_nonneg (by positivity) squareTailMass_nonneg) (by positivity)

/-- The whole real tail of the periodized packet family. Its constant does
not depend on the number of centers or on their locations.
@isnad1 id=and.6h7v.s9.1d5ab75ac35b from=translated src=- shape=7671abaf vocab=43166fb3
-/
theorem multipeak_period_tail_bound (s : Finset ℤ) (c : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C D N : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hdecay : ∀ j ∈ s, ∀ t : ℝ, ‖g j t‖ ≤ C/(1+|t-c j|)^6)
    (x : ℝ) (hx : |x| ≤ N) :
    (Summable fun k : ℤ => if k=0 then 0 else ∑ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖) ∧
    (∑' k : ℤ, if k=0 then 0 else ∑ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖) ≤
      (C/D^2)*squareTailMass^2 := by
  let A := (C/D^2)*squareTailMass
  have hA : 0 ≤ A := mul_nonneg (by positivity) squareTailMass_nonneg
  have hmaj := summable_squareTail.mul_left A
  have hp : ∀ k : ℤ,
      (if k=0 then 0 else ∑ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖) ≤ A*(1/(k:ℝ)^2) := by
    intro k
    by_cases hk : k=0
    · simp [hk]
    · simpa [hk, A] using multipeak_shift_norm_bound s c g hC hD hbound horder hdecay x hx k hk
  have hn : Summable fun k : ℤ => if k=0 then 0 else ∑ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) hp hmaj
  refine ⟨hn, ?_⟩
  calc
    _ ≤ ∑' k : ℤ, A*(1/(k:ℝ)^2) := hn.tsum_le_tsum hp hmaj
    _ = A*squareTailMass := by rw [tsum_mul_left]; rfl
    _ = _ := by dsimp [A]; ring

/-- The signed sum incurs only a uniformly small real error when periodized.
Only the centered real-axis decay enters this bound.
@isnad1 id=le.7h8v.s8.a951c1e860d3 from=translated src=- shape=3059202b vocab=5834597d
-/
theorem multipeak_periodize_error (s : Finset ℤ) (c ψ : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C D N : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hψ : ∀ j ∈ s, |ψ j|=1)
    (hdecay : ∀ j ∈ s, ∀ t : ℝ, ‖g j t‖ ≤ C/(1+|t-c j|)^6)
    (x : ℝ) (hx : |x| ≤ N) :
    ‖periodize (signedPacketSum s ψ g) (2*N) x - signedPacketSum s ψ g x‖ ≤
      (C/D^2)*squareTailMass^2 := by
  let G := signedPacketSum s ψ g
  let r : ℤ → ℂ := fun k => if k=0 then 0 else G ((x+2*N*k:ℝ):ℂ)
  let A := (C/D^2)*squareTailMass
  have hA : 0 ≤ A := mul_nonneg (by positivity) squareTailMass_nonneg
  have hnorm (t : ℝ) : ‖G (t:ℂ)‖ ≤ ∑ j ∈ s, ‖g j t‖ := by
    calc
      _ ≤ ∑ j ∈ s, ‖(ψ j:ℂ)*g j t‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hψ j hj, one_mul]
  have hp : ∀ k : ℤ, ‖r k‖ ≤ A*(1/(k:ℝ)^2) := by
    intro k
    by_cases hk : k=0
    · simp [r, hk]
    · simpa [r, hk, A] using (hnorm (x+2*N*k)).trans
        (multipeak_shift_norm_bound s c g hC hD hbound horder hdecay x hx k hk)
  have hmaj := summable_squareTail.mul_left A
  have hn : Summable fun k : ℤ => ‖r k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hp hmaj
  have hs0 : Summable fun k : ℤ => if k=0 then G (x:ℂ) else 0 := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hs : Summable fun k : ℤ => G ((x+2*N*k:ℝ):ℂ) := by
    convert hs0.add hn.of_norm using 1
    funext k
    by_cases hk : k=0 <;> simp [r, hk]
  have hsum : periodize G (2*N) x - G x = ∑' k : ℤ, r k := by
    have heq := hs.tsum_eq_add_tsum_ite 0
    simp only [Int.cast_zero, mul_zero, add_zero] at heq
    have hre : (fun k : ℤ => G ((x+2*N*k:ℝ):ℂ)) =
        (fun k : ℤ => G ((x:ℂ)+(((2*N)*k:ℝ):ℂ))) := by
      funext k
      rw [Complex.ofReal_add]
    change (∑' k : ℤ, G ((x:ℂ)+(((2*N)*k:ℝ):ℂ))) - G x = _
    rw [← hre]
    exact sub_eq_iff_eq_add.mpr (by simpa [r, add_comm] using heq)
  change ‖periodize G (2*N) x-G x‖ ≤ _
  rw [hsum]
  calc
    ‖∑' k : ℤ, r k‖ ≤ ∑' k : ℤ, ‖r k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ, A*(1/(k:ℝ)^2) := hn.tsum_le_tsum hp hmaj
    _ = A*squareTailMass := by rw [tsum_mul_left]; rfl
    _ = _ := by dsimp [A]; ring

end Erdos1133
