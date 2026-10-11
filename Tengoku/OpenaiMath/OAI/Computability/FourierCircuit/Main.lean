import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.ToeplitzCross

namespace OAI

section
noncomputable section
namespace ExactFourier.PrimeInventory
open Nat Real

theorem count_fourth (M : ℕ) (hM : 10≤M) : M≤Nat.primeCounting (M^4) := by
 have hm : (10:ℝ)≤M := by exact_mod_cast hM
 have hm0 : (0:ℝ)<M := by linarith
 have hs : (100:ℝ)≤(M : ℝ)^2 := by nlinarith
 have hn : (1:ℝ)<(M : ℝ)^4 := by nlinarith [sq_nonneg ((M : ℝ)^2-1)]
 have hlpos : 0<Real.log ((M : ℝ)^4) := Real.log_pos hn
 have hl : Real.log ((M : ℝ)^4)=4*Real.log M := by rw [Real.log_pow]; norm_num
 have hlog : Real.log (M : ℝ)≤M := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
 have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
 have hlog21 : Real.log 2≤1 := by linarith [Real.log_two_lt_d9]
 have hb : Real.log ((M : ℝ)^4+1)≤1+4*M := by
  have h1 := Real.log_le_log (by positivity : (0:ℝ)<(M : ℝ)^4+1)
    (show (M : ℝ)^4+1≤2*(M : ℝ)^4 by linarith)
  rw [Real.log_mul (by norm_num) (by positivity),hl] at h1
  linarith
 have hs4 : 100*(M : ℝ)^2≤(M : ℝ)^4 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (M : ℝ))]
 have hn1 : (M : ℝ)*Real.log ((M : ℝ)^4)≤(M : ℝ)^4*Real.log 2-Real.log ((M : ℝ)^4+1) := by
  rw [hl]
  have h1 := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤4*M by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ)≤(M : ℝ)^4 by positivity)
  nlinarith only [h1,h2,hb,hs4,hs,hm]
 have hh := Chebyshev.pi_ge (M^4)
 have hlower : (M : ℝ)≤((M : ℝ)^4*Real.log 2-Real.log ((M : ℝ)^4+1))/Real.log ((M : ℝ)^4) :=
  (le_div_iff₀ hlpos).mpr hn1
 have hh' : (M : ℝ)≤Nat.primeCounting (M^4) := by
  apply hlower.trans
  simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hh
 exact_mod_cast hh'

def upper (q m : ℕ) : ℕ := (m+2*q+10)^4

theorem family (q m : ℕ) : ∃ r : Fin m→ℕ,
 (∀ i,Nat.Prime (r i)) ∧ Function.Injective r ∧
 (∀ i,2*q≤r i) ∧ (∀ i,r i≤upper q m) := by
 let V := Nat.primesLE (upper q m)
 let S := V.filter (fun p=>2*q≤p)
 let T := V.filter (fun p=>¬2*q≤p)
 have hcard := Finset.card_filter_add_card_filter_not (s := V) (fun p=>2*q≤p)
 have ht : T.card≤2*q := by
  have hsub : T⊆Finset.range (2*q) := by
   intro p hp
   exact Finset.mem_range.mpr (lt_of_not_ge (Finset.mem_filter.mp hp).2)
  simpa only [Finset.card_range] using Finset.card_le_card hsub
 have hv : m+2*q≤V.card := by
  rw [show V=Nat.primesLE (upper q m) from rfl,Nat.primesLE_card_eq_primeCounting]
  have hh : m + 2*q ≤ m + 2*q + 10 := by omega
  exact hh.trans (count_fourth _ (by omega))
 have hs : m≤S.card := by change S.card+T.card=V.card at hcard; omega
 obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m) (β := S) (by simpa using hs)
 refine ⟨fun i=>(e i).val,fun i=>?_,fun i j h=>e.injective (Subtype.ext h),fun i=>?_,fun i=>?_⟩
 · exact Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (e i).property).1
 · exact (Finset.mem_filter.mp (e i).property).2
 · exact Nat.le_of_mem_primesLE (Finset.mem_filter.mp (e i).property).1

theorem family_coprime {m : ℕ} {r : Fin m→ℕ} (hr : ∀ i,Nat.Prime (r i))
 (hi : Function.Injective r) : Pairwise (fun i j=>Nat.Coprime (r i) (r j)) := by
 intro i j hij
 exact (Nat.coprime_primes (hr i) (hr j)).mpr (fun h=>hij (hi h))
end ExactFourier.PrimeInventory

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open CircuitCost

def depth (q m : ℕ) : ℕ := 8388608*(Nat.log 2 (PrimeInventory.upper q m)+2)^2+5

theorem depth_bound (q m : ℕ) :
 (depth q m : ℝ)≤536870917*(Real.log ((m:ℝ)+2*q+10)+1)^2 := by
 let x : ℝ := (m:ℝ)+2*q+10
 have hx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) q]
 have hl : 0≤Real.log x := Real.log_nonneg hx
 have hu : (PrimeInventory.upper q m : ℝ)=x^4 := by simp [PrimeInventory.upper,x]
 have hlog := Real.natLog_le_logb (PrimeInventory.upper q m) 2
 rw [hu,Real.logb,Real.log_pow] at hlog
 norm_num only [Nat.cast_ofNat] at hlog
 have h2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
 have h2p : 0<Real.log 2 := Real.log_pos (by norm_num)
 have hh : (Nat.log 2 (PrimeInventory.upper q m) : ℝ)≤8*Real.log x := by
  apply hlog.trans
  apply (div_le_iff₀ h2p).mpr
  nlinarith [mul_nonneg hl (sub_nonneg.mpr h2)]
 have hb : (Nat.log 2 (PrimeInventory.upper q m) : ℝ)+2≤8*(Real.log x+1) := by linarith
 have hb0 : 0≤(Nat.log 2 (PrimeInventory.upper q m) : ℝ)+2 := by positivity
 have hsq := sq_le_sq₀ hb0 (by positivity : 0≤8*(Real.log x+1)) |>.mpr hb
 change (depth q m : ℝ)≤536870917*(Real.log x+1)^2
 simp only [depth,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 nlinarith [sq_nonneg (Real.log x)]

end ExactFourier.FourierTransfer

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open Filter Topology Asymptotics

theorem log_square_littleO {a : ℝ} (ha : a<1) :
 (fun x : ℝ=>(Real.log x+1)^2)=o[atTop] (fun x : ℝ=>x^(1-a)) := by
 have hs : 0<1-a := by linarith
 have h2 := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hs
 have h2' : (fun x : ℝ=>(Real.log x)^2)=o[atTop] (fun x : ℝ=>x^(1-a)) := by
  simpa only [Real.rpow_two] using h2
 have h1 := (isLittleO_log_rpow_atTop hs).const_mul_left (2 : ℝ)
 have h0 : (fun _ : ℝ=>(1:ℝ))=o[atTop] (fun x : ℝ=>x^(1-a)) := by
  apply (isLittleO_const_left_of_ne one_ne_zero).mpr
  simpa only [Real.norm_eq_abs,Function.comp_def] using tendsto_abs_atTop_atTop.comp (tendsto_rpow_atTop hs)
 exact ((h2'.add h1).add h0).congr_left (fun x=>by ring)

theorem log_power_ratio {a : ℝ} (ha : a<1) :
 Tendsto (fun x : ℝ=>(Real.log x+1)^2*x^a/x) atTop (𝓝 0) := by
 have ht := (log_square_littleO ha).tendsto_div_nhds_zero
 apply ht.congr'
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
 rw [Real.rpow_sub hx,Real.rpow_one]
 field_simp

theorem shifted_log_power_ratio {a c : ℝ} (ha : a<1) :
 Tendsto (fun m : ℕ=>(Real.log ((m:ℝ)+c)+1)^2*((m:ℝ)+c)^a/(m:ℝ)) atTop (𝓝 0) := by
 have ht : Tendsto (fun m : ℕ=>(m:ℝ)+c) atTop atTop :=
  (tendsto_atTop_add_const_right atTop c tendsto_id).comp tendsto_natCast_atTop_atTop
 have h1 := (log_power_ratio ha).comp ht
 have h2 : Tendsto (fun m : ℕ=>((m:ℝ)+c)/(m:ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := c)).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply (show Tendsto (fun m : ℕ=>1+c*(m:ℝ)⁻¹) atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (ne_of_gt hm)
  field_simp
 have h := h1.mul h2
 apply (show Tendsto (fun m : ℕ=>((Real.log ((m:ℝ)+c)+1)^2*((m:ℝ)+c)^a/((m:ℝ)+c))*(((m:ℝ)+c)/(m:ℝ))) atTop (𝓝 0) by simpa using h).congr'
 filter_upwards [ht.eventually (eventually_gt_atTop (0:ℝ))] with m hm
 field_simp
end ExactFourier.FourierTransfer

end
end

section
noncomputable section
namespace ExactFourier.CircuitCost

theorem exists_circuit {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
 ∃ C : Circuit n,C.size=cost M ∧ C.Computes M := by
 obtain ⟨T,hT,ht⟩ := optimal M
 let e := Fintype.equivFin (Fin n)
 let D : LinearDAG n n := (T.circuit.withInputs e.symm).withOutputs e
 let C : Circuit n := ⟨D.size,D.program,D.outputs⟩
 refine ⟨C,?_,?_⟩
 · change D.size=cost M
   change (T.circuit.withInputs e.symm).size=cost M
   rw [LinearDAG.size_withInputs]
   exact hT
 · intro x
   change D.eval x=M.mulVec x
   rw [LinearDAG.eval_withOutputs,LinearDAG.eval_withInputs]
   exact ht x
end ExactFourier.CircuitCost

end
end

section
noncomputable section
namespace ExactFourier
open Filter Topology
open CircuitCost

end ExactFourier

end
end

section
namespace ExactFourier

end ExactFourier

end

section
noncomputable section
namespace ExactFourier
open Filter Topology

/-- Existence of an exact circuit in every width, used only to define the minimum. -/
theorem exists_fourier_circuit (n : ℕ) : ∃ k : ℕ,∃ C : Circuit n,
 C.size=k ∧ C.Computes (fourierMatrix n) := by
 obtain ⟨C,hC,hc⟩ := CircuitCost.exists_circuit (fourierMatrix n)
 exact ⟨C.size,C,rfl,hc⟩

def L (n : ℕ) : ℕ := by
 classical
 exact Nat.find (exists_fourier_circuit n)

theorem L_attained (n : ℕ) : ∃ C : Circuit n,C.size=L n ∧ C.Computes (fourierMatrix n) := by
 classical
 exact Nat.find_spec (exists_fourier_circuit n)

theorem L_le {n : ℕ} (C : Circuit n) (hC : C.Computes (fourierMatrix n)) : L n≤C.size := by
 classical
 exact Nat.find_min' (exists_fourier_circuit n) ⟨C,rfl,hC⟩

theorem fourier_denominator_pos {n : ℕ} (hn : 2≤n) :
 0 < (n:ℝ)*Real.logb 2 (n:ℝ) := by
 have hn' : (1:ℝ)< n := by exact_mod_cast (show 1< n from by omega)
 exact mul_pos (lt_trans zero_lt_one hn') (Real.logb_pos (by norm_num) hn')

end ExactFourier

end
end

end OAI
