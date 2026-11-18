import Tengoku.TusnadyLean.Oscillation.Influence
import Tengoku.TusnadyLean.Oscillation.FiniteAverage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Oscillation
noncomputable section
open Finset

def lowerHalfIndex {d : ℕ} (l : Fin d) : Fin (2 * d) := ⟨l.val, by omega⟩
def upperHalfIndex {d : ℕ} (l : Fin d) : Fin (2 * d) := ⟨d + l.val, by omega⟩

/--
@isnad1 id=eq.0h2v.s7.12702c46ab8f from=translated src=- shape=49f2bdee vocab=9a6bc37c
-/
lemma sum_two_halves {d : ℕ} (f : Fin (2 * d) → ℝ) :
    (∑ l, f l) = (∑ l : Fin d, f (lowerHalfIndex l)) +
      ∑ l : Fin d, f (upperHalfIndex l) := by
  have he : d + d = 2 * d := by omega
  have h := Fin.sum_univ_add (fun l : Fin (d + d) => f (Fin.cast he l))
  have hc : (∑ l : Fin (d + d), f (Fin.cast he l)) = ∑ l : Fin (2 * d), f l := by
    exact Equiv.sum_comp (finCongr he) f
  rw [hc] at h
  exact h

def maximizingIndex {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) : Fin m :=
  Classical.choose (gridMax_exists hm f)

/--
@isnad1 id=eq.1h2v.s4.e63b6b3ddaad from=translated src=- shape=12a07c49 vocab=79380a27
-/
lemma maximizingIndex_spec {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    f (maximizingIndex hm f) = gridMax hm f :=
  (Classical.choose_spec (gridMax_exists hm f)).symm

def representativeProbe {n b m : ℕ} (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c v : ℕ) (l : Fin b) : Fin (b * m) :=
  ⟨l.val * m + (maximizingIndex hm (blockValues χ p Y c (v * b + l.val))).val,
    by
      have ht := (maximizingIndex hm (blockValues χ p Y c (v * b + l.val))).isLt
      have hl := l.isLt
      nlinarith⟩

def representativeHeight {n b m : ℕ} (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c v : ℕ) (l : Fin b) : ℕ :=
  v * (b * m) + (representativeProbe hm χ p Y c v l).val + 1

/--
@isnad1 id=and.1h9v.s7.923d7dac951a from=translated src=- shape=3e65cd39 vocab=588ab3f6
-/
lemma representativeHeight_bounds {n b m : ℕ} (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c v : ℕ) (l : Fin b) :
    v * (b * m) + l.val * m < representativeHeight hm χ p Y c v l ∧
    representativeHeight hm χ p Y c v l ≤ v * (b * m) + (l.val + 1) * m := by
  have ht := (maximizingIndex hm (blockValues χ p Y c (v * b + l.val))).isLt
  unfold representativeHeight representativeProbe
  dsimp
  constructor <;> nlinarith

/--
@isnad1 id=strictmo.1h8v.s5.8a5945e316df from=translated src=- shape=30632545 vocab=54f288f5
-/
lemma representativeHeight_strictMono {n b m : ℕ} (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c v : ℕ) : StrictMono (representativeHeight (b := b) hm χ p Y c v) := by
  intro l k hlk
  have hl := (representativeHeight_bounds hm χ p Y c v l).2
  have hk := (representativeHeight_bounds hm χ p Y c v k).1
  have hmul := Nat.mul_le_mul_right m hlk
  nlinarith

/--
@isnad1 id=eq.1h9v.s6.280b8631e9dd from=translated src=- shape=d5054321 vocab=a919f96a
-/
lemma representativeHeight_value {n b m : ℕ} (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c v : ℕ) (l : Fin b) :
    endpointValue χ p Y c (representativeHeight hm χ p Y c v l) =
      gridMax hm (blockValues χ p Y c (v * b + l.val)) := by
  convert maximizingIndex_spec hm (blockValues χ p Y c (v * b + l.val)) using 1
  congr 1
  unfold representativeHeight representativeProbe blockValues
  dsimp
  ring

/-- The average plus the difference of the two end entries is bounded by the maximum.
@isnad1 id=le.2h4v.s7.b695c0339115 from=translated src=- shape=7bd9790d vocab=ecc37b0b
-/
lemma gridMax_end_comparison {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (f : Fin m → ℝ) (a : Fin (2 * d) → Fin m) :
    ((∑ l : Fin (2 * d), f (a l)) +
      |f (a ⟨0, by omega⟩) - f (a ⟨2*d-1, by omega⟩)|) / (2 * d : ℕ) ≤ gridMax hm f := by
  let lo : Fin (2*d) := ⟨0, by omega⟩
  let hi : Fin (2*d) := ⟨2*d-1, by omega⟩
  have hne : lo ≠ hi := by intro he; have := congrArg Fin.val he; dsimp [lo,hi] at this; omega
  have htotal : (∑ l : Fin (2*d), (gridMax hm f - f (a l))) =
      (2*d : ℕ) * gridMax hm f - ∑ l : Fin (2*d), f (a l) := by
    rw [sum_sub_distrib]; simp
  have hlo := single_le_sum (s := univ) (fun l _ => sub_nonneg.mpr (le_gridMax hm f (a l))) (mem_univ lo)
  have hhi := single_le_sum (s := univ) (fun l _ => sub_nonneg.mpr (le_gridMax hm f (a l))) (mem_univ hi)
  rw [htotal] at hlo hhi
  have hl := le_gridMax hm f (a lo)
  have hh := le_gridMax hm f (a hi)
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (2*d:ℕ))).mpr
  change (∑ l, f (a l)) + |f (a lo)-f (a hi)| ≤ _
  rcases le_total (f (a lo)) (f (a hi)) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]; nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]; nlinarith

/-- Only the bottom and top representatives contribute.-/
def representativeKernel {d : ℕ} (y : Fin (2 * d) → ℕ) (Y : ℕ) : ℝ :=
  (∑ l : Fin (2*d), if l.val+1 = 2*d then (if Y < y l then 1 else 0) else 0) -
    ∑ l : Fin (2*d), if l.val = 0 then (if Y < y l then 1 else 0) else 0

/--
@isnad1 id=eq.1h3v.s7.4a910d165b57 from=translated src=- shape=48e8c453 vocab=0b0a5103
-/
lemma representativeKernel_eq {d : ℕ} (hd : 0 < d) (y : Fin (2*d) → ℕ) (Y : ℕ) :
    representativeKernel y Y =
      (if Y < y ⟨2*d-1, by omega⟩ then 1 else 0) -
        (if Y < y ⟨0, by omega⟩ then 1 else 0) := by
  let lo : Fin (2*d) := ⟨0, by omega⟩
  let hi : Fin (2*d) := ⟨2*d-1, by omega⟩
  have hlast (l : Fin (2*d)) : l.val+1 = 2*d ↔ l = hi := by
    constructor
    · intro h; apply Fin.ext; change l.val = 2*d-1; omega
    · intro h; have he := congrArg Fin.val h; change l.val = 2*d-1 at he; omega
  have hfirst (l : Fin (2*d)) : l.val = 0 ↔ l = lo := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  simp [representativeKernel, hlast, hfirst, lo, hi]

/--
@isnad1 id=le.1h3v.s6.1b14821852bb from=translated src=- shape=c65d8bf3 vocab=2298dac3
-/
lemma representativeKernel_nonneg {d : ℕ} (y : Fin (2 * d) → ℕ)
    (hy : StrictMono y) (Y : ℕ) : 0 ≤ representativeKernel y Y := by
  by_cases hd : 0 < d
  · rw [representativeKernel_eq hd]
    have hh := hy (show (⟨0, by omega⟩ : Fin (2*d)) < ⟨2*d-1, by omega⟩ by
      change 0 < 2*d-1; omega)
    split_ifs <;> norm_num at * <;> omega
  · have : d = 0 := by omega
    subst d; simp [representativeKernel]

/--
@isnad1 id=le.4h3v.s7.ab8a1cfa9a32 from=translated src=- shape=74c0708d vocab=280dcb64
-/
lemma representativeKernel_ge_one {d : ℕ} (hd : 0 < d) (y : Fin (2 * d) → ℕ)
    (_hy : StrictMono y) (Y : ℕ)
    (hlo : y ⟨0, by omega⟩ ≤ Y) (hhi : Y < y ⟨2 * d - 1, by omega⟩) :
    1 ≤ representativeKernel y Y := by
  rw [representativeKernel_eq hd]
  simp [hhi, not_lt.mpr hlo]

def interiorIndices {n : ℕ} (b m : ℕ) (p Y : Fin n → ℕ) (c v : ℕ) : Finset (Fin n) :=
  univ.filter fun i => p i = c ∧ v * (b * m) + m ≤ Y i ∧
    Y i < v * (b * m) + (b - 1) * m

def interiorCount {n : ℕ} (b m : ℕ) (p Y : Fin n → ℕ) (c v : ℕ) : ℕ :=
  (interiorIndices b m p Y c v).card

def interiorMass {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) : ℝ :=
  ∑ c : Fin K, ∑ v : Fin V, Real.sqrt (interiorCount b m p Y c.val v.val)

/--
@isnad1 id=le.3h9v.s6.f1c6ac62098a from=translated src=- shape=b0a9a7ca vocab=0d894777
-/
lemma representativeKernel_interior {n d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c v : ℕ) (i : Fin n)
    (hi : i ∈ interiorIndices (2 * d) m p Y c v) :
    1 ≤ representativeKernel (representativeHeight (b := 2 * d) hm χ p Y c v) (Y i) := by
  rcases (mem_filter.mp hi).2 with ⟨hpc, hlo, hhi⟩
  apply representativeKernel_ge_one hd _ (representativeHeight_strictMono hm χ p Y c v) (Y i)
  · have hh := (representativeHeight_bounds hm χ p Y c v (⟨0, by omega⟩ : Fin (2 * d))).2
    norm_num at hh
    omega
  · have hh := (representativeHeight_bounds hm χ p Y c v
      (⟨2 * d - 1, by omega⟩ : Fin (2 * d))).1
    dsimp at hh
    omega

def rowDifference {n d : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c : ℕ) (y : Fin (2 * d) → ℕ) : ℝ :=
  (∑ l : Fin (2*d), if l.val = 0 then endpointValue χ p Y c (y l) else 0) -
    ∑ l : Fin (2*d), if l.val+1 = 2*d then endpointValue χ p Y c (y l) else 0

/--
@isnad1 id=eq.1h7v.s7.94f583c36d79 from=translated src=- shape=8ca1ea88 vocab=8512a5e7
-/
lemma rowDifference_endpoints {n d : ℕ} (hd : 0 < d) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c : ℕ) (y : Fin (2*d) → ℕ) :
    rowDifference χ p Y c y = endpointValue χ p Y c (y ⟨0, by omega⟩) -
      endpointValue χ p Y c (y ⟨2*d-1, by omega⟩) := by
  let lo : Fin (2*d) := ⟨0, by omega⟩
  let hi : Fin (2*d) := ⟨2*d-1, by omega⟩
  have hlast (l : Fin (2*d)) : l.val+1 = 2*d ↔ l = hi := by
    constructor
    · intro h; apply Fin.ext; change l.val = 2*d-1; omega
    · intro h; have he := congrArg Fin.val h; change l.val = 2*d-1 at he; omega
  have hfirst (l : Fin (2*d)) : l.val = 0 ↔ l = lo := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  simp [rowDifference, hlast, hfirst, lo, hi]

/--
@isnad1 id=eq.0h7v.s6.5bbca7716ecb from=translated src=- shape=9b4713e1 vocab=0ef10311
-/
lemma rowDifference_eq {n d : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c : ℕ) (y : Fin (2 * d) → ℕ) :
    rowDifference χ p Y c y =
      -∑ i, χ i * representativeKernel y (Y i) * endpointWeight (p i) c := by
  by_cases hd : 0 < d
  · rw [rowDifference_endpoints hd]
    simp_rw [representativeKernel_eq hd]
    unfold endpointValue
    rw [← sum_sub_distrib, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  · have : d = 0 := by omega
    subst d; simp [rowDifference, representativeKernel]

def kernelWeights {n d : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c : ℕ) (y : Fin (2 * d) → ℕ) : Fin n → ℝ :=
  fun i => if p i = c then χ i * representativeKernel y (Y i) else 0

/--
@isnad1 id=le.3h8v.s7.1119cc42df81 from=translated src=- shape=b550891d vocab=c35a7b50
-/
lemma kernelWeights_variance {n d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ) (c v : ℕ) :
    (interiorCount (2 * d) m p Y c v : ℝ) ≤
      ∑ i, (kernelWeights χ p Y c (representativeHeight (b := 2 * d) hm χ p Y c v) i)^2 := by
  have hi : ∀ i : Fin n, (if i ∈ interiorIndices (2 * d) m p Y c v then (1 : ℝ) else 0) ≤
      (kernelWeights χ p Y c (representativeHeight (b := 2 * d) hm χ p Y c v) i)^2 := by
    intro i
    by_cases his : i ∈ interiorIndices (2 * d) m p Y c v
    · have hpc := (mem_filter.mp his).2.1
      have hk := representativeKernel_interior hd hm χ p Y c v i his
      have hs : (χ i)^2 = 1 := by nlinarith [sq_abs (χ i), hχ i]
      simp only [his, ite_true, kernelWeights, hpc]
      rw [mul_pow, hs, one_mul]
      nlinarith
    · simp only [his, ite_false]
      positivity
  have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => hi i)
  simpa [interiorCount] using hh

end
end Oscillation
