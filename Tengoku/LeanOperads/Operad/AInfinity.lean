/-
# A∞-algebras

In the bar convention, an **A∞-structure** on a super module `(V, ε)` is a family `b` of odd
operations, `bₙ` of arity `n + 1`, with `∑_{j + k = m} bⱼ ⋆ bₖ = 0` for every `m`, where `⋆` is
the Koszul circle product of `Operad.KoszulSign` (`AInf.IsAInf`).

* Families of operations of all positive arities, with the total Koszul product
  `(f ⋆ g)ₘ = ∑_{j + k = m} fⱼ ⋆ gₖ` (`AInf.tstar`), satisfy **the graded pre-Lie identity**
  (`AInf.tstar_assoc_symm`), and an odd family cancels against itself
  (`AInf.tstar_tstar_odd`).
* **The Hochschild differential** `D_b f = b ⋆ f - (-1)^|f| f ⋆ b` of an A∞-structure squares
  to zero (`AInf.hoch_hoch`): A∞-structures are the odd Maurer–Cartan elements of the
  Gerstenhaber algebra of `V`.
* **dg algebras** are the A∞-structures concentrated in arities one and two
  (`AInf.isAInf_dga_iff`): an odd differential and an odd product, with the Leibniz rule
  `d (x y) + (d x) y + (ε x) (d y) = 0` and associativity `(x y) z + (ε x) (y z) = 0` in the bar
  convention.
-/
import Tengoku.LeanOperads.Operad.KoszulSign
import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

namespace AInf

open End Finset

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Transport between arities -/

/-- Transport between arities, zero when they differ.-/
def acast {a b : ℕ} (x : End R V a) : End R V b :=
  if h : a = b then reindex R (End R V) h x else 0

lemma acast_of_eq {a b : ℕ} (h : a = b) (x : End R V a) :
    (acast x : End R V b) = reindex R (End R V) h x := dite_eq_left h

@[simp] lemma acast_self {a : ℕ} (x : End R V a) : (acast x : End R V a) = x := by
  rw [acast_of_eq rfl, reindex_rfl]

lemma acast_reindex {a b c : ℕ} (h : a = b) (x : End R V a) :
    (acast (reindex R (End R V) h x) : End R V c) = acast x := by
  subst h
  rw [reindex_rfl]

lemma acast_acast {a b c : ℕ} (h : a = b) (x : End R V a) :
    (acast (acast x : End R V b) : End R V c) = acast x := by
  rw [acast_of_eq h, acast_reindex]

@[simp] lemma acast_zero {a b : ℕ} : (acast (0 : End R V a) : End R V b) = 0 := by
  unfold acast
  split_ifs <;> simp

lemma acast_add {a b : ℕ} (x y : End R V a) :
    (acast (x + y) : End R V b) = acast x + acast y := by
  unfold acast
  split_ifs <;> simp

lemma acast_smul {a b : ℕ} (c : R) (x : End R V a) :
    (acast (c • x) : End R V b) = c • acast x := by
  unfold acast
  split_ifs <;> simp

lemma acast_neg {a b : ℕ} (x : End R V a) : (acast (-x) : End R V b) = -acast x := by
  unfold acast
  split_ifs <;> simp

lemma acast_sub {a b : ℕ} (x y : End R V a) :
    (acast (x - y) : End R V b) = acast x - acast y := by
  rw [sub_eq_add_neg, acast_add, acast_neg, ← sub_eq_add_neg]

lemma acast_sum {a b : ℕ} {ι : Type*} (s : Finset ι) (x : ι → End R V a) :
    (acast (∑ i ∈ s, x i) : End R V b) = ∑ i ∈ s, acast (x i) := by
  unfold acast
  split_ifs <;> simp

/-! ## Families and the total Koszul product -/

variable (R V) in
/-- Operations of all positive arities: `f n` has arity `n + 1`.-/
abbrev Fam : Type v := ∀ n : ℕ, End R V (n + 1)

variable (ε : V →ₗ[R] V)

/-- **The total Koszul product** of families, `(f ⋆ g)ₘ = ∑_{j + k = m} fⱼ ⋆ gₖ`, for `g` of
parity `q`.-/
def tstar (q : ℕ) (f g : Fam R V) : Fam R V :=
  fun m => ∑ j ∈ range (m + 1), acast (kstar ε q (f j) (g (m - j)))

lemma tstar_apply (q : ℕ) (f g : Fam R V) (m : ℕ) :
    tstar ε q f g m = ∑ j ∈ range (m + 1), acast (kstar ε q (f j) (g (m - j))) := rfl

lemma kstar_sum_left (q : ℕ) {j k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → End R V (j + 1))
    (β : End R V (k + 1)) : kstar ε q (∑ x ∈ s, f x) β = ∑ x ∈ s, kstar ε q (f x) β := by
  unfold kstar
  simp only [kcompFin_sum_left]
  exact Finset.sum_comm

lemma kstar_sum_right (q : ℕ) {j k : ℕ} {ι : Type*} (s : Finset ι) (α : End R V (j + 1))
    (g : ι → End R V (k + 1)) : kstar ε q α (∑ x ∈ s, g x) = ∑ x ∈ s, kstar ε q α (g x) := by
  unfold kstar
  simp only [kcompFin_sum_right]
  exact Finset.sum_comm

lemma kstar_add_left (q : ℕ) {j k : ℕ} (α α' : End R V (j + 1)) (β : End R V (k + 1)) :
    kstar ε q (α + α') β = kstar ε q α β + kstar ε q α' β := by
  have := kstar_sum_left ε q Finset.univ ![α, α'] β
  simpa using this

lemma kstar_add_right (q : ℕ) {j k : ℕ} (α : End R V (j + 1)) (β β' : End R V (k + 1)) :
    kstar ε q α (β + β') = kstar ε q α β + kstar ε q α β' := by
  have := kstar_sum_right ε q Finset.univ α ![β, β']
  simpa using this

lemma kstar_smul_left (q : ℕ) {j k : ℕ} (c : R) (α : End R V (j + 1)) (β : End R V (k + 1)) :
    kstar ε q (c • α) β = c • kstar ε q α β := by
  unfold kstar kcompFin
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, compFin_smul_left]

lemma kstar_smul_right (q : ℕ) {j k : ℕ} (c : R) (α : End R V (j + 1)) (β : End R V (k + 1)) :
    kstar ε q α (c • β) = c • kstar ε q α β := by
  unfold kstar kcompFin
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => compFin_smul_right _ _ _ _

@[simp] lemma kstar_zero_left (q : ℕ) {j k : ℕ} (β : End R V (k + 1)) :
    kstar ε q (0 : End R V (j + 1)) β = 0 := by
  simpa using kstar_smul_left ε q (0 : R) 0 β

@[simp] lemma kstar_zero_right (q : ℕ) {j k : ℕ} (α : End R V (j + 1)) :
    kstar ε q α (0 : End R V (k + 1)) = 0 := by
  simpa using kstar_smul_right ε q (0 : R) α 0

lemma kstar_acast_left (q : ℕ) {j j' k : ℕ} (h : j' = j) (α : End R V (j' + 1))
    (β : End R V (k + 1)) :
    kstar ε q (acast α : End R V (j + 1)) β = acast (kstar ε q α β) := by
  subst h
  simp

lemma kstar_acast_right (q : ℕ) {j k k' : ℕ} (h : k' = k) (α : End R V (j + 1))
    (β : End R V (k' + 1)) :
    kstar ε q α (acast β : End R V (k + 1)) = acast (kstar ε q α β) := by
  subst h
  simp

lemma kstar_sub_left (q : ℕ) {j k : ℕ} (α α' : End R V (j + 1)) (β : End R V (k + 1)) :
    kstar ε q (α - α') β = kstar ε q α β - kstar ε q α' β := by
  rw [sub_eq_add_neg, kstar_add_left, ← neg_one_smul R α', kstar_smul_left, neg_one_smul,
    ← sub_eq_add_neg]

lemma kstar_sub_right (q : ℕ) {j k : ℕ} (α : End R V (j + 1)) (β β' : End R V (k + 1)) :
    kstar ε q α (β - β') = kstar ε q α β - kstar ε q α β' := by
  rw [sub_eq_add_neg, kstar_add_right, ← neg_one_smul R β', kstar_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

lemma tstar_sub_left (q : ℕ) (f f' g : Fam R V) :
    tstar ε q (f - f') g = tstar ε q f g - tstar ε q f' g := by
  funext m
  simp only [tstar_apply, Pi.sub_apply, ← Finset.sum_sub_distrib, kstar_sub_left, acast_sub]

lemma tstar_sub_right (q : ℕ) (f g g' : Fam R V) :
    tstar ε q f (g - g') = tstar ε q f g - tstar ε q f g' := by
  funext m
  simp only [tstar_apply, Pi.sub_apply, ← Finset.sum_sub_distrib, kstar_sub_right, acast_sub]

lemma tstar_smul_left (q : ℕ) (c : R) (f g : Fam R V) :
    tstar ε q (c • f) g = c • tstar ε q f g := by
  funext m
  simp only [tstar_apply, Pi.smul_apply, kstar_smul_left, acast_smul, Finset.smul_sum]

lemma tstar_smul_right (q : ℕ) (c : R) (f g : Fam R V) :
    tstar ε q f (c • g) = c • tstar ε q f g := by
  funext m
  simp only [tstar_apply, Pi.smul_apply, kstar_smul_right, acast_smul, Finset.smul_sum]

@[simp] lemma tstar_zero_left (q : ℕ) (g : Fam R V) : tstar ε q 0 g = 0 := by
  funext m
  simp [tstar_apply]

@[simp] lemma tstar_zero_right (q : ℕ) (f : Fam R V) : tstar ε q f 0 = 0 := by
  funext m
  simp [tstar_apply]

/-! ## Triple sums -/

/-- Summing over `j + k + l = m` in the two nested orders.-/
lemma sum_triangle {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ a ∈ range (m + 1), ∑ j ∈ range (a + 1), F j (a - j) (m - a)
      = ∑ j ∈ range (m + 1), ∑ k ∈ range (m - j + 1), F j k (m - j - k) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 - x.2⟩) (fun y => ⟨y.1 + y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨j, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨a, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    simp only [Sigma.mk.injEq, heq_iff_eq, and_true]
    omega
  · rintro ⟨j, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    dsimp only
    simp only [Sigma.mk.injEq, heq_iff_eq, true_and]
    omega
  · rintro ⟨a, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    congr 1
    omega

/-- The disjoint parts of all the triple products in arity `m + 1`.-/
def defect (q r : ℕ) (f g h : Fam R V) (m : ℕ) : End R V (m + 1) :=
  ∑ j ∈ range (m + 1), ∑ k ∈ range (m - j + 1),
    acast (kdisjointPart ε q r (f j) (g k) (h (m - j - k)))

/-- **The associator of the total product is the sum of the disjoint parts.**-/
lemma tstar_assoc_eq_defect (q r : ℕ) (f g h : Fam R V) (m : ℕ) :
    tstar ε r (tstar ε q f g) h m - tstar ε (q + r) f (tstar ε r g h) m
      = defect ε q r f g h m := by
  have hL : tstar ε r (tstar ε q f g) h m
      = ∑ a ∈ range (m + 1), ∑ j ∈ range (a + 1),
          acast (kstar ε r (kstar ε q (f j) (g (a - j))) (h (m - a))) := by
    rw [tstar_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [tstar_apply, kstar_sum_left, acast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ a := by simp only [Finset.mem_range] at hj; omega
    rw [kstar_acast_left ε r (show j + (a - j) = a by omega), acast_acast]
    omega
  have hR : tstar ε (q + r) f (tstar ε r g h) m
      = ∑ j ∈ range (m + 1), ∑ k ∈ range (m - j + 1),
          acast (kstar ε (q + r) (f j) (kstar ε r (g k) (h (m - j - k)))) := by
    rw [tstar_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [tstar_apply, kstar_sum_right, acast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hj' : j ≤ m := by simp only [Finset.mem_range] at hj; omega
    have hk' : k ≤ m - j := by simp only [Finset.mem_range] at hk; omega
    rw [kstar_acast_right ε (q + r) (show k + (m - j - k) = m - j by omega), acast_acast]
    omega
  rw [hL, hR, sum_triangle m (fun j k l =>
    (acast (kstar ε r (kstar ε q (f j) (g k)) (h l)) : End R V (m + 1))), defect,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kstar_kstar_left_split, acast_add, acast_reindex]
  abel

variable (hε : ∀ x, ε (ε x) = x)
include hε

/-! ## A∞-structures -/

/-- **An A∞-structure** in the bar convention: a family of odd operations with `b ⋆ b = 0`.-/
structure IsAInf (b : Fam R V) : Prop where
  odd : ∀ n, IsHomog ε 1 (b n)
  mc : tstar ε 1 b b = 0

omit hε in
/-- **The Hochschild differential** of a family `b`, on families of parity `p`:
`D_b f = b ⋆ f - (-1)^p f ⋆ b`.-/
def hoch (b : Fam R V) (p : ℕ) (f : Fam R V) : Fam R V :=
  tstar ε p b f - (-1 : R) ^ p • tstar ε 1 f b

/-! ## dg algebras -/

omit hε in
variable (R V) in
/-- **The family of a dg algebra** in the bar convention: a differential `d` and a product `μ`.-/
def dga (d : End R V 1) (μ : End R V 2) : Fam R V
  | 0 => d
  | 1 => μ
  | _ + 2 => 0

omit hε in
lemma kstar_apply_11 (d d' : End R V 1) (v : Fin 1 → V) :
    kstar ε 1 d d' v = d ![d' ![v 0]] := by
  rw [kstar, Fin.sum_univ_one, kcompFin, compFin_apply, twist_apply]
  congr 1
  funext s
  fin_cases s
  simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
  rw [twistFn_of_ge _ _ _ _ le_rfl, LinearMap.id_apply, cfTuple_of_eq _ _ _ _ rfl]
  congr 1
  funext t
  fin_cases t
  rfl

omit hε in
lemma kstar_apply_12 (d : End R V 1) (μ : End R V 2) (v : Fin 2 → V) :
    kstar ε 1 d μ v = d ![μ ![v 0, v 1]] := by
  rw [kstar, Fin.sum_univ_one, kcompFin, compFin_apply, twist_apply]
  congr 1
  funext s
  fin_cases s
  simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
  rw [twistFn_of_ge _ _ _ _ le_rfl, LinearMap.id_apply, cfTuple_of_eq _ _ _ _ rfl]
  congr 1
  funext t
  fin_cases t <;> rfl

omit hε in
lemma kstar_apply_21 (μ : End R V 2) (d : End R V 1) (v : Fin 2 → V) :
    kstar ε 1 μ d v = μ ![d ![v 0], v 1] + μ ![ε (v 0), d ![v 1]] := by
  rw [kstar, Fin.sum_univ_two, add_apply]
  congr 1
  · rw [kcompFin, compFin_apply, twist_apply]
    congr 1
    funext s
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [twistFn_of_ge _ _ _ _ le_rfl, LinearMap.id_apply, cfTuple_of_eq _ _ _ _ rfl]
      congr 1
      funext t
      fin_cases t
      rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [twistFn_of_ge _ _ _ _ (by simp), LinearMap.id_apply,
        cfTuple_of_gt _ _ _ _ (by simp)]
      rfl
  · rw [kcompFin, compFin_apply, twist_apply]
    congr 1
    funext s
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [twistFn_of_lt _ _ _ _ (by simp), pow_one, cfTuple_of_lt _ _ _ _ (by simp)]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [twistFn_of_ge _ _ _ _ le_rfl, LinearMap.id_apply, cfTuple_of_eq _ _ _ _ rfl]
      congr 1
      funext t
      fin_cases t
      rfl

omit hε in
lemma kstar_apply_22 (μ ν : End R V 2) (v : Fin 3 → V) :
    kstar ε 1 μ ν v = μ ![ν ![v 0, v 1], v 2] + μ ![ε (v 0), ν ![v 1, v 2]] := by
  rw [kstar, Fin.sum_univ_two, add_apply]
  congr 1
  · rw [kcompFin, compFin_apply, twist_apply]
    congr 1
    funext s
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [twistFn_of_ge _ _ _ _ le_rfl, LinearMap.id_apply, cfTuple_of_eq _ _ _ _ rfl]
      congr 1
      funext t
      fin_cases t <;> rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [twistFn_of_ge _ _ _ _ (by simp), LinearMap.id_apply,
        cfTuple_of_gt _ _ _ _ (by simp)]
      rfl
  · rw [kcompFin, compFin_apply, twist_apply]
    congr 1
    funext s
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [twistFn_of_lt _ _ _ _ (by simp), pow_one, cfTuple_of_lt _ _ _ _ (by simp)]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [twistFn_of_ge _ _ _ _ le_rfl, LinearMap.id_apply, cfTuple_of_eq _ _ _ _ rfl]
      congr 1
      funext t
      fin_cases t <;> rfl

end AInf

end Operad
