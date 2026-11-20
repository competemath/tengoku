import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.SixthWindow
import Tengoku.Seed.Analysis.PSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators Real Topology
open Finset Set

namespace Erdos1133

/-- The universal summable majorant for separated translates.-/
def squareTailMass : ℝ := ∑' j : ℤ, 1 / (j : ℝ)^2

theorem summable_squareTail : Summable (fun j : ℤ => 1 / (j : ℝ)^2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

theorem squareTailMass_nonneg : 0 ≤ squareTailMass :=
  tsum_nonneg (fun _ => by positivity)

theorem shifted_square_sum_le (s : Finset ℤ) (i : ℤ) :
    ∑ j ∈ s, 1 / ((j-i : ℤ) : ℝ)^2 ≤ squareTailMass := by
  calc
    ∑ j ∈ s, 1 / ((j-i : ℤ) : ℝ)^2 =
        ∑ j ∈ s.image (fun j => j-i), 1 / (j:ℝ)^2 :=
      (Finset.sum_image (s:=s) (g:=fun j:ℤ => j-i)
        (f:=fun j:ℤ => 1/(j:ℝ)^2) (fun a _ b _ h => sub_left_inj.mp h)).symm
    _ ≤ squareTailMass :=
      summable_squareTail.sum_le_tsum _ (fun _ _ => by positivity)

theorem sixth_tail_le_square {C D d : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hd : 0 ≤ d) (j : ℤ) (hj : j ≠ 0)
    (hdist : D*|(j:ℝ)|/2 ≤ d) :
    C/(1+d)^6 ≤ (4*C/D^2) * (1/(j:ℝ)^2) := by
  have hjr : (j:ℝ) ≠ 0 := by exact_mod_cast hj
  have hb : 0 < D*|(j:ℝ)|/2 := by positivity
  have hden : (D*|(j:ℝ)|/2)^2 ≤ (1+d)^6 := by
    calc
      (D*|(j:ℝ)|/2)^2 ≤ d^2 := pow_le_pow_left₀ hb.le hdist 2
      _ ≤ (1+d)^2 := pow_le_pow_left₀ hd (by linarith) 2
      _ ≤ (1+d)^6 := pow_le_pow_right₀ (by linarith) (by omega)
  calc
    C/(1+d)^6 ≤ C/(D*|(j:ℝ)|/2)^2 :=
      div_le_div_of_nonneg_left hC (sq_pos_of_pos hb) hden
    _ = (4*C/D^2) * (1/(j:ℝ)^2) := by
      rw [div_pow,mul_pow,sq_abs]
      field_simp
      ring

/-- Uniform interference of arbitrarily many separated packets. The bound is
independent of the number of selected cells.-/
theorem packet_tail_at_nearest (s : Finset ℤ) (c : ℤ → ℝ) (u : ℤ → ℝ → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (hdecay : ∀ j ∈ s, ∀ x : ℝ, |u j x| ≤ C/(1+|x-c j|)^6)
    (x : ℝ) (i : ℤ) (hi : i ∈ s)
    (hnear : ∀ j ∈ s, |x-c i| ≤ |x-c j|) :
    ∑ j ∈ s.erase i, |u j x| ≤ (4*C/D^2)*squareTailMass := by
  have hpoint : ∀ j ∈ s.erase i,
      |u j x| ≤ (4*C/D^2) * (1/((j-i:ℤ):ℝ)^2) := by
    intro j hj
    have hjs : j ∈ s := mem_of_mem_erase hj
    have hji : j-i ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hj)
    have hdist : D*|((j-i:ℤ):ℝ)|/2 ≤ |x-c j| := by
      have ht := abs_sub_le (c j) x (c i)
      rw [abs_sub_comm (c j) x] at ht
      linarith [hsep i hi j hjs,hnear j hjs]
    exact (hdecay j hjs x).trans
      (sixth_tail_le_square hC hD (abs_nonneg _) (j-i) hji hdist)
  calc
    ∑ j ∈ s.erase i, |u j x| ≤
        ∑ j ∈ s.erase i, (4*C/D^2) * (1/((j-i:ℤ):ℝ)^2) :=
      Finset.sum_le_sum hpoint
    _ = (4*C/D^2) * (∑ j ∈ s.erase i, 1/((j-i:ℤ):ℝ)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (4*C/D^2)*squareTailMass :=
      mul_le_mul_of_nonneg_left (shifted_square_sum_le _ _) (by positivity)

theorem nearest_at_peak (s : Finset ℤ) (c : ℤ → ℝ)
    {D ρ : ℝ} (hD : 0 < D) (hgap : 2*ρ ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (x : ℝ) (i : ℤ) (hi : i ∈ s) (hx : |x-c i| ≤ ρ) :
    ∀ j ∈ s, |x-c i| ≤ |x-c j| := by
  intro j hj
  by_cases hji : j=i
  · subst j
    rfl
  have hone : (1:ℝ) ≤ |((j-i:ℤ):ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hji)
  have hDij : D ≤ |c j-c i| := by
    have h := mul_le_mul_of_nonneg_left hone hD.le
    simpa using h.trans (hsep i hi j hj)
  have ht := abs_sub_le (c j) x (c i)
  rw [abs_sub_comm (c j) x] at ht
  linarith

/-- Exact finite entire superposition; the signs remain completely free.-/
def signedPacketSum (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, (ψ i : ℂ)*g i z

theorem signedPacketSum_real (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ)
    (hr : ∀ i ∈ s, ∀ x : ℝ, (g i x).im=0) (x : ℝ) :
    (signedPacketSum s ψ g x).im=0 := by
  simp only [signedPacketSum,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hr i hi x,mul_zero]

theorem signedPacketSum_re (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ) (x : ℝ) :
    (signedPacketSum s ψ g x).re = ∑ i ∈ s, ψ i*(g i x).re := by
  simp [signedPacketSum,Complex.mul_re]

theorem signedPacketSum_entire (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ)
    (hg : ∀ i ∈ s, Differentiable ℂ (g i)) :
    Differentiable ℂ (signedPacketSum s ψ g) := by
  unfold signedPacketSum
  apply Differentiable.fun_sum
  intro i hi
  exact (hg i hi).const_mul (ψ i:ℂ)

theorem centered_decay_to_origin (g : ℂ → ℂ) {a C σ : ℝ}
    (_hC : 0 ≤ C)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C*Real.exp (σ*|z.im|)/(1+‖z-(a:ℂ)‖)^6)
    (z : ℂ) :
    ‖g z‖ ≤ (C*(1+|a|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 := by
  have hz : ‖z‖ ≤ ‖z-(a:ℂ)‖+|a| := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using norm_add_le (z-(a:ℂ)) (a:ℂ)
  have hb : 1+‖z‖ ≤ (1+|a|)*(1+‖z-(a:ℂ)‖) := by
    nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg (z-(a:ℂ)))]
  have hp := pow_le_pow_left₀ (by positivity : 0≤1+‖z‖) hb 6
  rw [mul_pow] at hp
  have hbase := (le_div_iff₀ (by positivity : 0<(1+‖z-(a:ℂ)‖)^6)).mp (hg z)
  apply (le_div_iff₀ (by positivity : 0<(1+‖z‖)^6)).mpr
  calc
    ‖g z‖*(1+‖z‖)^6 ≤ ‖g z‖*((1+|a|)^6*(1+‖z-(a:ℂ)‖)^6) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = (1+|a|)^6*(‖g z‖*(1+‖z-(a:ℂ)‖)^6) := by ring
    _ ≤ (1+|a|)^6*(C*Real.exp (σ*|z.im|)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (C*(1+|a|)^6)*Real.exp (σ*|z.im|) := by ring

/-- A genuine sixth-power bound, sufficient for analytic periodization. The
large prefactor is used only in complex analysis, never for real tail budgets.-/
theorem signedPacketSum_decay (s : Finset ℤ) (c ψ : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C σ : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ i ∈ s, |ψ i|=1)
    (hg : ∀ i ∈ s, ∀ z : ℂ, ‖g i z‖ ≤
      C*Real.exp (σ*|z.im|)/(1+‖z-(c i:ℂ)‖)^6) (z : ℂ) :
    ‖signedPacketSum s ψ g z‖ ≤
      (∑ i ∈ s, C*(1+|c i|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 := by
  calc
    ‖signedPacketSum s ψ g z‖ ≤ ∑ i ∈ s, ‖(ψ i:ℂ)*g i z‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖g i z‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hψ i hi,one_mul]
    _ ≤ ∑ i ∈ s, (C*(1+|c i|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 :=
      Finset.sum_le_sum (fun i hi => centered_decay_to_origin (g i) hC (hg i hi) z)
    _ = (∑ i ∈ s, C*(1+|c i|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 := by
      rw [←Finset.sum_div,←Finset.sum_mul]

theorem real_norm_eq_abs_re {z : ℂ} (hz : z.im=0) : ‖z‖=|z.re| := by
  rw [←Complex.re_add_im z,hz,Complex.ofReal_zero,zero_mul,add_zero,
    Complex.norm_real,Real.norm_eq_abs]
  simp only [Complex.ofReal_re]

/-- A signed sum retains a large peak if all other packets have bounded total
mass there. This is applied to actual entire packets constructed below.-/
theorem signed_sum_peak {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (hi : i ∈ s) (u ψ : ι → ℝ)
    (hψ : ∀ j ∈ s, |ψ j| = 1) {B E : ℝ}
    (hpeak : B ≤ u i) (htail : ∑ j ∈ s.erase i, |u j| ≤ E) :
    B-E ≤ ψ i * (∑ j ∈ s, ψ j * u j) := by
  have hisq : ψ i * ψ i = 1 := by
    have h := hψ i hi
    have h' := sq_abs (ψ i)
    rw [h] at h'
    nlinarith
  rw [← Finset.add_sum_erase _ _ hi, mul_add, ← mul_assoc, hisq, one_mul]
  have hnorm : |∑ j ∈ s.erase i, ψ j * u j| ≤ E := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ j ∈ s.erase i, |ψ j * u j| = ∑ j ∈ s.erase i, |u j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, hψ j (mem_of_mem_erase hj), one_mul]
      _ ≤ E := htail
  have hm : |ψ i * (∑ j ∈ s.erase i, ψ j * u j)| ≤ E := by
    rw [abs_mul, hψ i hi, one_mul]
    exact hnorm
  linarith [(abs_le.mp hm).1]

theorem signed_sum_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (hi : i ∈ s) (u ψ : ι → ℝ)
    (hψ : ∀ j ∈ s, |ψ j| = 1) {A E : ℝ}
    (hmain : |u i| ≤ A) (htail : ∑ j ∈ s.erase i, |u j| ≤ E) :
    |∑ j ∈ s, ψ j * u j| ≤ A+E := by
  rw [← Finset.add_sum_erase _ _ hi]
  apply (abs_add_le _ _).trans
  have hnorm : |∑ j ∈ s.erase i, ψ j * u j| ≤ E := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ j ∈ s.erase i, |ψ j * u j| = ∑ j ∈ s.erase i, |u j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, hψ j (mem_of_mem_erase hj), one_mul]
      _ ≤ E := htail
  rw [abs_mul, hψ i hi, one_mul]
  exact add_le_add hmain hnorm

/-- Every bound here concerns the constructed finite sum, not an assumed
interpolation operator. Separation makes the estimates uniform in `s.card`.-/
theorem signedPacketSum_estimates (s : Finset ℤ) (hs : s.Nonempty)
    (c p ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ) {B C D M ρ : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hgap : 2*ρ ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (hbudget : (4*C/D^2)*squareTailMass ≤ 1)
    (hψ : ∀ i ∈ s, |ψ i|=1)
    (hr : ∀ i ∈ s, ∀ x : ℝ, (g i x).im=0)
    (hb : ∀ i ∈ s, ∀ x : ℝ, ‖g i x‖≤M)
    (hdecay : ∀ i ∈ s, ∀ x : ℝ, ‖g i x‖≤C/(1+|x-c i|)^6)
    (hp : ∀ i ∈ s, |p i-c i|≤ρ ∧ B≤(g i (p i)).re)
    (Γ : Finset ℝ) (hnodes : ∀ i ∈ s, ∀ x ∈ Γ, ‖g i x‖≤1) :
    (∀ x : ℝ, ‖signedPacketSum s ψ g x‖≤M+1) ∧
    (∀ x ∈ Γ, ‖signedPacketSum s ψ g x‖≤2) ∧
    (∀ i ∈ s, B-1≤ψ i*(signedPacketSum s ψ g (p i)).re) := by
  let u : ℤ → ℝ → ℝ := fun i x => (g i x).re
  have hdec : ∀ i ∈ s, ∀ x : ℝ, |u i x|≤C/(1+|x-c i|)^6 := by
    intro i hi x
    exact (Complex.abs_re_le_norm _).trans (hdecay i hi x)
  have htail (x : ℝ) (i : ℤ) (hi : i ∈ s)
      (hnear : ∀ j ∈ s, |x-c i|≤|x-c j|) :
      ∑ j ∈ s.erase i, |u j x|≤1 :=
    (packet_tail_at_nearest s c u hC hD hsep hdec x i hi hnear).trans hbudget
  have hnorm (x : ℝ) : ‖signedPacketSum s ψ g x‖=
      |∑ i ∈ s, ψ i*u i x| := by
    rw [real_norm_eq_abs_re (signedPacketSum_real s ψ g hr x),signedPacketSum_re]
  refine ⟨?_,?_,?_⟩
  · intro x
    obtain ⟨i,hi,hnear⟩ := s.exists_min_image (fun i => |x-c i|) hs
    rw [hnorm]
    exact signed_sum_bound s i hi (fun i => u i x) ψ hψ
      ((Complex.abs_re_le_norm _).trans (hb i hi x)) (htail x i hi hnear)
  · intro x hx
    obtain ⟨i,hi,hnear⟩ := s.exists_min_image (fun i => |x-c i|) hs
    rw [hnorm]
    have hh := signed_sum_bound s i hi (fun i => u i x) ψ hψ
      ((Complex.abs_re_le_norm _).trans (hnodes i hi x hx)) (htail x i hi hnear)
    norm_num at hh
    exact hh
  · intro i hi
    rw [signedPacketSum_re]
    exact signed_sum_peak s i hi (fun j => u j (p i)) ψ hψ (hp i hi).2
      (htail (p i) i hi (nearest_at_peak s c hD hgap hsep (p i) i hi (hp i hi).1))

/-- The 957 packets apply to every sparse cell of the actual global node set.
They are small at every global node, including nodes outside that cell.-/
theorem sparse_cell_packets (B : ℝ) (hB : 1 < B) :
    ∃ ρ : ℕ, ∃ σ M C : ℝ,
      0 < ρ ∧ 0 < σ ∧ σ < Real.pi ∧ 0 < M ∧ 0 < C ∧
      ∀ (Γ : Finset ℝ) (a : ℝ),
        (Γ.filter (fun x => |x-a| ≤ ρ)).card ≤ 2*ρ+1 →
        ∃ g : ℂ → ℂ, ∃ p : ℝ,
          Differentiable ℂ g ∧ (∀ x : ℝ, (g x).im = 0) ∧
          (∀ x : ℝ, ‖g x‖ ≤ M) ∧
          (∀ x ∈ Γ, ‖g x‖ ≤ 1) ∧ |p-a| ≤ ρ ∧ B ≤ (g p).re ∧
          (∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ*|z.im|) /
            (1+‖z-(a:ℂ)‖)^6) := by
  obtain ⟨ρ,σ,M,ℓ,C,hρ,hσ,hσπ,hM,hℓ,hC,hdata⟩ :=
    Erdos1152.V5.local_bernstein_decay_exists B hB
  refine ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,?_⟩
  intro Γ a hcard
  let Λ := (Γ.filter (fun x => |x-a| ≤ ρ)).image (fun x => x-a)
  have hΛ : ∀ x ∈ Λ, x ∈ Icc (-(ρ:ℝ)) ρ := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact abs_le.mp (mem_filter.mp hy).2
  have hΛcard : Λ.card ≤ 2*ρ+1 := (card_image_le).trans hcard
  obtain ⟨g,l,r,hg,hr,hbound,hnodes,hext,hlr,hlen,hsub,hpeak,hdecay⟩ :=
    hdata Λ hΛ hΛcard
  have hl : l ∈ Icc (-(ρ:ℝ)) ρ := hsub ⟨le_rfl,hlr.le⟩
  refine ⟨fun z => g (z-(a:ℂ)),l+a,hg.comp (by fun_prop),?_,?_,?_,?_,?_,?_⟩
  · intro x
    simpa using hr (x-a)
  · intro x
    simpa using hbound (x-a)
  · intro x hx
    by_cases ha : |x-a| ≤ ρ
    · simpa using hnodes (x-a) (mem_image_of_mem _ (mem_filter.mpr ⟨hx,ha⟩))
    · simpa using hext (x-a) (le_of_lt (lt_of_not_ge ha))
  · simpa using (abs_le.mpr hl)
  · simpa using hpeak l ⟨le_rfl,hlr.le⟩
  · intro z
    simpa using hdecay (z-(a:ℂ))

/-- Actual entire packets, with their peak locations chosen before any signs.-/
structure SparsePacketFamily (Γ : Finset ℝ) (s : Finset ℤ) (c : ℤ → ℝ)
    (B ρ σ M C : ℝ) where
  g : ℤ → ℂ → ℂ
  p : ℤ → ℝ
  entire : ∀ i ∈ s, Differentiable ℂ (g i)
  real : ∀ i ∈ s, ∀ x : ℝ, (g i x).im=0
  bound : ∀ i ∈ s, ∀ x : ℝ, ‖g i x‖≤M
  nodes : ∀ i ∈ s, ∀ x ∈ Γ, ‖g i x‖≤1
  near : ∀ i ∈ s, |p i-c i|≤ρ
  peak : ∀ i ∈ s, B≤(g i (p i)).re
  decay : ∀ i ∈ s, ∀ z : ℂ,
    ‖g i z‖≤C*Real.exp (σ*|z.im|)/(1+‖z-(c i:ℂ)‖)^6

theorem sparse_packet_family_exists (B : ℝ) (hB : 1<B) :
    ∃ ρ : ℕ, ∃ σ M C : ℝ,
      0<ρ ∧ 0<σ ∧ σ<Real.pi ∧ 0<M ∧ 0<C ∧
      ∀ (Γ : Finset ℝ) (s : Finset ℤ) (c : ℤ → ℝ),
        (∀ i ∈ s, (Γ.filter (fun x => |x-c i|≤ρ)).card≤2*ρ+1) →
        Nonempty (SparsePacketFamily Γ s c B ρ σ M C) := by
  obtain ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,hdata⟩ := sparse_cell_packets B hB
  refine ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,?_⟩
  intro Γ s c hsparse
  have hlocal := fun i : s => hdata Γ (c i) (hsparse i i.property)
  choose g₀ p₀ hd hr hb hn hp hpk hdec using hlocal
  let g : ℤ → ℂ → ℂ := fun i => if hi:i∈s then g₀ ⟨i,hi⟩ else 0
  let p : ℤ → ℝ := fun i => if hi:i∈s then p₀ ⟨i,hi⟩ else 0
  refine ⟨⟨g,p,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i hi
    simpa [g,hi] using hd ⟨i,hi⟩
  · intro i hi x
    simpa [g,hi] using hr ⟨i,hi⟩ x
  · intro i hi x
    simpa [g,hi] using hb ⟨i,hi⟩ x
  · intro i hi x hx
    simpa [g,hi] using hn ⟨i,hi⟩ x hx
  · intro i hi
    simpa [p,hi] using hp ⟨i,hi⟩
  · intro i hi
    simpa [p,g,hi] using hpk ⟨i,hi⟩
  · intro i hi z
    simpa [g,hi] using hdec ⟨i,hi⟩ z

theorem SparsePacketFamily.real_decay
    {Γ : Finset ℝ} {s : Finset ℤ} {c : ℤ → ℝ} {B ρ σ M C : ℝ}
    (F : SparsePacketFamily Γ s c B ρ σ M C) :
    ∀ i ∈ s, ∀ x : ℝ, ‖F.g i x‖≤C/(1+|x-c i|)^6 := by
  intro i hi x
  simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using F.decay i hi (x:ℂ)

theorem SparsePacketFamily.signed_estimates
    {Γ : Finset ℝ} {s : Finset ℤ} {c : ℤ → ℝ} {B ρ σ M C D : ℝ}
    (F : SparsePacketFamily Γ s c B ρ σ M C) (hs : s.Nonempty)
    (hC : 0≤C) (hD : 0<D) (hgap : 2*ρ≤D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)|≤|c j-c i|)
    (hbudget : (4*C/D^2)*squareTailMass≤1)
    (ψ : ℤ → ℝ) (hψ : ∀i∈s,|ψ i|=1) :
    (∀ x : ℝ, ‖signedPacketSum s ψ F.g x‖≤M+1) ∧
    (∀ x ∈ Γ, ‖signedPacketSum s ψ F.g x‖≤2) ∧
    (∀ i ∈ s, B-1≤ψ i*(signedPacketSum s ψ F.g (F.p i)).re) :=
  signedPacketSum_estimates s hs c F.p ψ F.g hC hD hgap hsep hbudget hψ
    F.real F.bound F.real_decay (fun i hi => ⟨F.near i hi,F.peak i hi⟩) Γ F.nodes

end Erdos1133
