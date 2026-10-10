import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.SeparableCoordinates

namespace OAI

universe uM uN uB uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {N : Type uN} [MetricSpace M] [MetricSpace N]

def quotients (f : M → N) (S : Set M) : Set ℝ :=
  {0} ∪ {r | ∃ x ∈ S, ∃ y ∈ S, r = dist (f x) (f y) / dist x y}

def constant (f : M → N) (S : Set M) : ℝ := sSup (quotients f S)

theorem quotients_nonempty (f : M → N) (S : Set M) : (quotients f S).Nonempty :=
  ⟨0,Or.inl rfl⟩

theorem quotient_le {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    dist (f x) (f y) / dist x y ≤ L := by
  by_cases hxy : x = y
  · simp [hxy]
  · exact (div_le_iff₀ (dist_pos.mpr hxy)).mpr (hf.dist_le_mul x hx y hy)

theorem quotients_bounded {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : BddAbove (quotients f S) := by
  refine ⟨L,?_⟩
  rintro r (rfl | ⟨x,hx,y,hy,rfl⟩)
  · exact L.coe_nonneg
  · exact quotient_le hf hx hy

theorem constant_nonneg {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : 0 ≤ constant f S :=
  le_csSup (quotients_bounded hf) (Or.inl rfl)

theorem constant_le {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : constant f S ≤ L := by
  apply csSup_le (quotients_nonempty f S)
  rintro r (rfl | ⟨x,hx,y,hy,rfl⟩)
  · exact L.coe_nonneg
  · exact quotient_le hf hx hy

theorem lipschitzOn_constant {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : LipschitzOnWith ⟨constant f S,constant_nonneg hf⟩ f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : x = y
  · simp [hxy]
  · have hq : dist (f x) (f y) / dist x y ≤ constant f S :=
      le_csSup (quotients_bounded hf) (Or.inr ⟨x,hx,y,hy,rfl⟩)
    exact (div_le_iff₀ (dist_pos.mpr hxy)).mp hq

theorem subsequence_constants {B : Type uB} [Countable B] (O : B → Set M)
    (f : ℕ → M → N) {L : ℝ≥0} (hf : ∀ i, LipschitzWith L (f i)) :
    ∃ a : B → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ b, a b ∈ Icc (0 : ℝ) L) ∧
      ∀ b, Tendsto (fun i => constant (f (s i)) (O b)) atTop (𝓝 (a b)) := by
  let v : ℕ → B → Icc (0 : ℝ) L := fun i b =>
    ⟨constant (f i) (O b), constant_nonneg (hf i).lipschitzOnWith,
      constant_le (hf i).lipschitzOnWith⟩
  obtain ⟨a,s,hs,ha⟩ := CompactSpace.tendsto_subseq v
  refine ⟨fun b => a b,s,hs,fun b => (a b).property,?_⟩
  intro b
  exact (continuous_subtype_val.tendsto _).comp
    ((continuous_apply b).tendsto a |>.comp ha)

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} [MetricSpace M]

theorem uniform_zero_on_compact (f : ℕ → M → ℝ) {L : ℝ≥0}
    (hf : ∀ i, LipschitzWith L (f i))
    (hpoint : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 0))
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ K, |f i x| < ε := by
  classical
  let δ : ℝ := ε / (2 * ((L : ℝ)+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  let : Fintype t := ht.fintype
  have hsmall : ∀ᶠ i in atTop, ∀ y : t, |f i y| < ε/2 := by
    apply Filter.eventually_all.mpr
    intro y
    have hlim := (hpoint y.val).abs
    simp only [abs_zero] at hlim
    exact hlim.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [hsmall] with i hi x hx
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : dist x y < δ := hxy
  have hLip := (hf i).dist_le_mul x y
  rw [Real.dist_eq] at hLip
  have htri : |f i x| ≤ |f i x-f i y|+|f i y| := by
    simpa only [sub_add_cancel] using abs_add_le (f i x-f i y) (f i y)
  have hδid : 2 * ((L : ℝ)+1) * δ = ε := by dsimp [δ]; field_simp
  have hine := mul_lt_mul_of_pos_left hdist (show 0 < (L : ℝ)+1 by positivity)
  have hy' := hi ⟨y,hy⟩
  nlinarith [mul_nonneg L.coe_nonneg (dist_nonneg (x := x) (y := y))]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

def LocalOrthogonality (D : M → Hilbert (ι := ι)) : Prop :=
  ∀ {I : Type} [Fintype I], ∀ z : I → M, Function.Injective z →
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∃ S : I → Set (Σ n, ι n),
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ i x, x ∈ Metric.ball (z i) r → tail l (D x) ∈ space (S i)

end LipschitzCounterexample.LocalGeometry
namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

def badSet {B : Type uB} (O : B → Set M) (a : B → ℝ) (η : ℝ) : Set M :=
  {z | ∀ j, z ∈ O j → η ≤ a j}

end LipschitzCounterexample.LocalGeometry

end

end OAI
