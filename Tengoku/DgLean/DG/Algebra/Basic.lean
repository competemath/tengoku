import Tengoku.Seed.RingTheory.GradedAlgebra.Basic
import Tengoku.DgLean.DG.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential graded abelian groups, rings and algebras

This file defines the core objects of the library, with internal gradings in the style of
Mathlib's `GradedRing`.

* `DGAddCommGroup M`: a differential graded abelian group, i.e. an abelian group `M` with an
  internal `ℤ`-grading `grading : ℤ → AddSubgroup M` (a `DirectSum.Decomposition`) and a
  differential `d : M →+ M` of degree `1` with `d ∘ d = 0`. This is an internally graded
  cochain complex of abelian groups.
* `DGRing A`: a `Prop`-valued mixin saying that the ring structure of a `DGAddCommGroup A` is
  compatible with the grading (`1 ∈ A⁰`, `Aⁱ * Aʲ ⊆ Aⁱ⁺ʲ`) and with the differential
  (the graded Leibniz rule `d (a * b) = d a * b + (-1)^{|a|} • (a * d b)`).
* `DGAlgebra R A`: a `Prop`-valued mixin saying that an `R`-algebra structure on a dg ring `A`
  is compatible: the image of `R` lies in degree `0` and is killed by `d`. This makes `d`
  `R`-linear and every graded piece an `R`-submodule.

The data (grading and differential) live in `DGAddCommGroup`, so that the differential of a dg
ring and of a dg module are the same function `d`, and so that right modules and bimodules are
further `Prop` mixins on the same data (see `DG.Module.Basic`). This follows Mathlib's
separation of `Ring A` / `Module R M` / `IsScalarTower R A M`.

## Conventions

See `docs/CONVENTIONS.md`. Gradings are cohomological: `d` has degree `+1`. The Koszul sign
of degree `n` is `koszulSign n = Int.negOnePow n : ℤˣ`, used through the `ℤˣ`-action.
-/

open DirectSum

namespace DG

/-- A differential graded abelian group: an abelian group `M` with an internal `ℤ`-grading
`M = ⨁ n, grading n` and a differential `d : M →+ M` of degree `+1` squaring to zero.-/
class DGAddCommGroup (M : Type*) [AddCommGroup M] where
  /-- The homogeneous components `Mⁿ`.-/
  grading : ℤ → AddSubgroup M
  /-- The grading is an internal direct sum decomposition.-/
  [decomposition : DirectSum.Decomposition grading]
  /-- The differential.-/
  d : M →+ M
  d_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → d m ∈ grading (n + 1)
  d_d' : ∀ m : M, d (d m) = 0

attribute [instance_reducible, instance] DGAddCommGroup.decomposition

export DGAddCommGroup (grading d)

section DGAddCommGroup

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]

/--
@isnad1 id=mem.1h3v.s7.b9a8b6ddd03f from=translated src=- shape=21bd3a81 vocab=0de741f2
-/
theorem d_mem {n : ℤ} {m : M} (hm : m ∈ grading n) : d m ∈ grading (n + 1) :=
  DGAddCommGroup.d_mem' hm

/--
@isnad1 id=eq.0h2v.s7.8222dadab636 from=translated src=- shape=b2ee8c18 vocab=de36af19
-/
@[simp]
theorem d_d (m : M) : d (d m) = 0 :=
  DGAddCommGroup.d_d' m

/--
@isnad1 id=eq.0h1v.s7.58aa93cb6dbc from=translated src=- shape=365d5364 vocab=b59b4ab8
-/
@[simp]
theorem d_comp_d : (d : M →+ M).comp d = 0 := by
  ext m; exact d_d m

/--
@isnad1 id=eq.0h1v.s6.cde5cf6eceeb from=translated src=- shape=8be70fd0 vocab=de36af19
-/
@[simp]
theorem d_zero : d (0 : M) = 0 :=
  map_zero d

/--
@isnad1 id=eq.0h3v.s7.76d9d9c5a3ca from=translated src=- shape=6d953984 vocab=d48e3b82
-/
theorem d_add (m m' : M) : d (m + m') = d m + d m' :=
  map_add d m m'

/--
@isnad1 id=eq.0h2v.s7.31020e4dc996 from=translated src=- shape=e55842dd vocab=f1fbd493
-/
theorem d_neg (m : M) : d (-m) = -d m :=
  map_neg d m

/--
@isnad1 id=eq.0h3v.s7.0ecaff63df2b from=translated src=- shape=6d953984 vocab=5df5e206
-/
theorem d_sub (m m' : M) : d (m - m') = d m - d m' :=
  map_sub d m m'

/--
@isnad1 id=eq.0h3v.s7.c0d67b0729a7 from=translated src=- shape=28720f84 vocab=70bfd7dd
-/
theorem d_zsmul (k : ℤ) (m : M) : d (k • m) = k • d m :=
  map_zsmul d k m

/--
@isnad1 id=eq.0h3v.s7.f4e3bef82c9f from=translated src=- shape=28720f84 vocab=31c87e75
-/
theorem d_nsmul (k : ℕ) (m : M) : d (k • m) = k • d m :=
  map_nsmul d k m

/--
@isnad1 id=eq.0h3v.s7.c8adb16fcd69 from=translated src=- shape=18a70198 vocab=c786c1b3
-/
theorem d_units_smul (u : ℤˣ) (m : M) : d (u • m) = u • d m := by
  simp only [Units.smul_def, d_zsmul]

/-- The differential restricted to homogeneous components, `Mⁿ →+ Mⁿ⁺¹`.-/
def dHom (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) :
    grading (M := M) n →+ grading (M := M) (n + 1) where
  toFun m := ⟨d (m : M), d_mem m.2⟩
  map_zero' := by ext; simp
  map_add' m m' := by ext; simp [d_add]

/--
@isnad1 id=eq.0h3v.s10.faa95fb97771 from=translated src=- shape=37b41adb vocab=91d46adb
-/
@[simp]
theorem coe_dHom_apply (n : ℤ) (m : grading (M := M) n) : (dHom M n m : M) = d (m : M) := rfl

/-- Induction on the decomposition: to prove `P m` for all `m`, prove it for `0`, for homogeneous
elements, and show it is closed under addition.
@isnad1 id=var.0h6v.s7.c2294bd31e05 from=translated src=- shape=a4ecd280 vocab=28bd3d99
-/
theorem induction_on {P : M → Prop} (h_zero : P 0)
    (h_homogeneous : ∀ {n : ℤ} (m : grading (M := M) n), P m)
    (h_add : ∀ m m' : M, P m → P m' → P (m + m')) (m : M) : P m :=
  DirectSum.Decomposition.inductionOn (grading (M := M)) h_zero h_homogeneous h_add m

/-- The cocycles of degree `n`, `Zⁿ(M) = ker (d : Mⁿ → Mⁿ⁺¹)`.-/
def cocycles (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) : AddSubgroup M :=
  (grading (M := M) n) ⊓ (d : M →+ M).ker

/-- The coboundaries of degree `n`, `Bⁿ(M) = d (Mⁿ⁻¹)`.-/
def coboundaries (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) : AddSubgroup M :=
  (grading (M := M) (n - 1)).map d

/--
@isnad1 id=iff.0h3v.s7.6d6f8a701297 from=translated src=- shape=c1202c6a vocab=fde77a52
-/
theorem mem_cocycles {n : ℤ} {m : M} : m ∈ cocycles M n ↔ m ∈ grading n ∧ d m = 0 :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s7.4e268c074f2e from=translated src=- shape=83899362 vocab=18040c1a
-/
theorem mem_coboundaries {n : ℤ} {m : M} :
    m ∈ coboundaries M n ↔ ∃ m' ∈ grading (M := M) (n - 1), d m' = m :=
  Iff.rfl

/--
@isnad1 id=le.0h2v.s5.3c2b1672cb4b from=translated src=- shape=92e3ed7b vocab=098c703d
-/
theorem cocycles_le_grading (n : ℤ) : cocycles M n ≤ grading n :=
  inf_le_left

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N]

/-- An additive map of degree `k` commutes with taking homogeneous components.
@isnad1 id=eq.1h6v.s10.07ea053b3c37 from=translated src=- shape=86e2039b vocab=e0c9a5a0
-/
theorem decompose_map {k : ℤ} (f : M →+ N)
    (hf : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading (n + k)) (m : M) (n : ℤ) :
    (decompose (grading (M := N)) (f m) (n + k) : N) =
      f (decompose (grading (M := M)) m n) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous m =>
    obtain ⟨m, hm⟩ := m
    rename_i i
    by_cases h : i = n
    · subst h
      rw [decompose_of_mem_same _ hm, decompose_of_mem_same _ (hf hm)]
    · rw [decompose_of_mem_ne _ hm h, decompose_of_mem_ne _ (hf hm) (by omega), map_zero]
  | h_add m m' hm hm' =>
    simp only [map_add, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hm, hm']

/-- The differential commutes with taking homogeneous components: the degree-`n + 1`
component of `d m` is `d` of the degree-`n` component of `m`.
@isnad1 id=eq.0h3v.s10.701b169005cd from=translated src=- shape=0616ca51 vocab=3d209e7e
-/
theorem decompose_d (m : M) (n : ℤ) :
    (decompose (grading (M := M)) (d m) (n + 1) : M) =
      d (decompose (grading (M := M)) m n : M) :=
  decompose_map (k := 1) d (fun hm => d_mem hm) m n

/-- Induction over a homogeneous additive subgroup: a predicate which holds for `0`, for the
homogeneous elements of `S` and is closed under addition holds on all of `S`.
@isnad1 id=var.2h7v.s7.388258c88ab3 from=translated src=- shape=c2211759 vocab=20080dc7
-/
theorem induction_on_of_isHomogeneous {S : AddSubgroup M}
    (hS : SetLike.IsHomogeneous (grading (M := M)) S) {P : M → Prop} (h_zero : P 0)
    (h_homogeneous : ∀ {n : ℤ} {m : M}, m ∈ grading n → m ∈ S → P m)
    (h_add : ∀ m m' : M, P m → P m' → P (m + m')) {m : M} (hm : m ∈ S) : P m := by
  classical
  rw [← DirectSum.sum_support_decompose (grading (M := M)) m]
  refine Finset.sum_induction _ P h_add h_zero fun n _ => ?_
  exact h_homogeneous (decompose (grading (M := M)) m n).2 (hS n hm)

/-- The kernel of the differential is a homogeneous subgroup.
@isnad1 id=ishomoge.0h1v.s6.dff9fad21fe1 from=translated src=- shape=28015bfe vocab=1a0ed1f7
-/
theorem isHomogeneous_ker_d : SetLike.IsHomogeneous (grading (M := M)) (d : M →+ M).ker := by
  intro n m hm
  rw [AddMonoidHom.mem_ker] at hm ⊢
  rw [← decompose_d, hm, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- The image of the differential is a homogeneous subgroup.
@isnad1 id=ishomoge.0h1v.s5.b53f53a0f7dd from=translated src=- shape=28015bfe vocab=c7e3e40c
-/
theorem isHomogeneous_range_d :
    SetLike.IsHomogeneous (grading (M := M)) (d : M →+ M).range := by
  rintro n _ ⟨m, rfl⟩
  refine ⟨decompose (grading (M := M)) m (n - 1), ?_⟩
  rw [← decompose_d, sub_add_cancel]

end DGAddCommGroup

/-- A differential graded ring: a ring `A` which is a `DGAddCommGroup` such that the grading is
a ring grading (`1 ∈ A⁰`, `Aⁱ * Aʲ ⊆ Aⁱ⁺ʲ`) and the differential satisfies the graded Leibniz
rule `d (a * b) = d a * b + (-1)^{|a|} • (a * d b)` for `a` homogeneous of degree `|a|`.-/
class DGRing (A : Type*) [Ring A] [DGAddCommGroup A] : Prop
    extends SetLike.GradedMonoid (grading (M := A)) where
  d_mul' : ∀ {n : ℤ} {a : A}, a ∈ grading n → ∀ b : A,
    d (a * b) = d a * b + koszulSign n • (a * d b)

section DGRing

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

instance DGRing.toGradedRing : GradedRing (grading (M := A)) :=
  { DGRing.toGradedMonoid (A := A), DGAddCommGroup.decomposition (M := A) with }

/--
@isnad1 id=mem.0h1v.s6.308cb7f0a0e6 from=translated src=- shape=da94cacc vocab=391cc741
-/
theorem one_mem_grading : (1 : A) ∈ grading (M := A) 0 :=
  SetLike.GradedOne.one_mem

/--
@isnad1 id=mem.2h5v.s7.d4effe93b913 from=translated src=- shape=b2eb2f4c vocab=6f4c32e8
-/
theorem mul_mem_grading {i j : ℤ} {a b : A} (ha : a ∈ grading i) (hb : b ∈ grading j) :
    a * b ∈ grading (i + j) :=
  SetLike.GradedMul.mul_mem ha hb

/-- The graded Leibniz rule.
@isnad1 id=eq.1h4v.s8.c52c77acbd45 from=translated src=- shape=c0613a79 vocab=2a984adf
-/
theorem d_mul {n : ℤ} {a : A} (ha : a ∈ grading n) (b : A) :
    d (a * b) = d a * b + koszulSign n • (a * d b) :=
  DGRing.d_mul' ha b

/--
@isnad1 id=eq.2h4v.s8.520b9cbdcf1f from=translated src=- shape=4af97a14 vocab=27219870
-/
theorem d_mul_of_even {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n) (b : A) :
    d (a * b) = d a * b + a * d b := by
  rw [d_mul ha, koszulSign_even hn, one_smul]

/--
@isnad1 id=eq.2h4v.s8.e9d5a5fed302 from=translated src=- shape=4af97a14 vocab=6e107b8e
-/
theorem d_mul_of_odd {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Odd n) (b : A) :
    d (a * b) = d a * b - a * d b := by
  rw [d_mul ha, koszulSign_odd hn, Units.neg_smul, one_smul, sub_eq_add_neg]

/--
@isnad1 id=eq.0h1v.s6.5a2ff7c3dfb2 from=translated src=- shape=456ef8f9 vocab=e886130d
-/
@[simp]
theorem d_one : d (1 : A) = 0 := by
  have h := d_mul (one_mem_grading (A := A)) 1
  simp only [mul_one, one_mul, koszulSign, Int.negOnePow_zero, one_smul] at h
  exact left_eq_add.mp h

/--
@isnad1 id=eq.0h2v.s6.e9c7ece52b35 from=translated src=- shape=02b534a1 vocab=0331ca42
-/
theorem d_intCast (k : ℤ) : d (k : A) = 0 := by
  rw [← zsmul_one, d_zsmul, d_one, smul_zero]

/-- `d` is a derivation on even elements: `d (a * b) = d a * b + a * d b` for `a ∈ A⁰`.
@isnad1 id=eq.1h3v.s8.1b04e4293d11 from=translated src=- shape=74056f79 vocab=c168f98b
-/
theorem d_mul_of_mem_zero {a : A} (ha : a ∈ grading 0) (b : A) :
    d (a * b) = d a * b + a * d b :=
  d_mul_of_even ha Even.zero b

/-- If `b` is a cocycle then `d (a * b) = d a * b` for every `a`.
@isnad1 id=eq.1h3v.s8.7be747cc36bb from=translated src=- shape=82bcd24f vocab=3981e872
-/
theorem d_mul_of_d_eq_zero_right {b : A} (hb : d b = 0) (a : A) : d (a * b) = d a * b := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a => rw [d_mul a.2, hb, mul_zero, smul_zero, add_zero]
  | h_add a a' ha ha' => rw [add_mul, d_add, ha, ha', d_add, add_mul]

/-- The Leibniz rule for powers: for `a` homogeneous of degree `n`,
`d (a ^ k) = ∑ i < k, (-1)^(i n) • (a ^ i * d a * a ^ (k - 1 - i))`.
@isnad1 id=eq.1h4v.s8.ccaee7111b7b from=translated src=- shape=a5d41e16 vocab=11b0a871
-/
theorem d_pow {n : ℤ} {a : A} (ha : a ∈ grading n) (k : ℕ) :
    d (a ^ k) = ∑ i ∈ Finset.range k, koszulSign (i * n) • (a ^ i * d a * a ^ (k - 1 - i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', d_mul ha, ih, Finset.sum_range_succ', Finset.mul_sum, Finset.smul_sum,
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, smul_smul, ← koszulSign_add, pow_succ', mul_assoc a, mul_assoc a]
      congr 2
      · push_cast; ring
      · congr 2
        omega
    · simp

/-- For `a` homogeneous of even degree, `d (a ^ k) = ∑ i < k, a ^ i * d a * a ^ (k - 1 - i)`.
@isnad1 id=eq.2h4v.s8.f6a27c27f390 from=translated src=- shape=cb1c988a vocab=8911bf49
-/
theorem d_pow_of_even {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n) (k : ℕ) :
    d (a ^ k) = ∑ i ∈ Finset.range k, a ^ i * d a * a ^ (k - 1 - i) := by
  rw [d_pow ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [koszulSign_even (hn.mul_left _), one_smul]

/-- For `a` homogeneous of even degree commuting with `d a`,
`d (a ^ k) = k • (a ^ (k - 1) * d a)`.
@isnad1 id=eq.3h4v.s8.b6cd28e3850b from=translated src=- shape=8a6ac5af vocab=bae0da80
-/
theorem d_pow_of_even_of_commute {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n)
    (hc : Commute a (d a)) (k : ℕ) : d (a ^ k) = k • (a ^ (k - 1) * d a) := by
  rw [d_pow_of_even ha hn, Finset.sum_range]
  rw [Finset.sum_eq_card_nsmul (b := a ^ (k - 1) * d a) fun i _ => ?_]
  · simp
  · have hi := i.isLt
    rw [(hc.pow_left _).eq, mul_assoc, ← pow_add, ← (hc.pow_left _).eq]
    congr 3
    omega

/-- For `a ∈ A⁰` commuting with `d a`, `d (a ^ k) = k • (a ^ (k - 1) * d a)`.
@isnad1 id=eq.2h3v.s8.c2ff185481cf from=translated src=- shape=39b9c5d1 vocab=294e4920
-/
theorem d_pow_of_mem_zero_of_commute {a : A} (ha : a ∈ grading 0) (hc : Commute a (d a))
    (k : ℕ) : d (a ^ k) = k • (a ^ (k - 1) * d a) :=
  d_pow_of_even_of_commute ha Even.zero hc k

set_option backward.isDefEq.respectTransparency false in
/-- The graded Leibniz rule for `n`-fold products. For a list `l` of homogeneous elements
(each given with its degree), `d (l₁ ⋯ lₙ) = ∑ᵢ (-1)^{|l₁| + ⋯ + |lᵢ₋₁|} • (l₁ ⋯ d lᵢ ⋯ lₙ)`.
@isnad1 id=eq.0h2v.s11.c6b061d46565 from=translated src=- shape=2998052f vocab=5fd9572e
-/
theorem d_list_prod (l : List (Σ n : ℤ, grading (M := A) n)) :
    d (l.map fun x => (x.2 : A)).prod =
      ∑ i : Fin l.length, koszulSign ((l.take i).map (·.1)).sum •
        (((l.take i).map fun x => (x.2 : A)).prod * d (l[i].2 : A) *
          ((l.drop (i + 1)).map fun x => (x.2 : A)).prod) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, d_mul x.2.2, ih]
    erw [Fin.sum_univ_succ]
    rw [Finset.mul_sum, Finset.smul_sum]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ, List.take_succ_cons, List.map_cons, List.sum_cons, List.prod_cons,
        List.drop_succ_cons, Fin.getElem_fin, koszulSign_add, mul_smul,
        mul_assoc, mul_smul_comm]
      rfl

end DGRing

/-- A differential graded `R`-algebra: an `R`-algebra `A` which is a dg ring, such that the
structure map `R → A` lands in degree `0` and is killed by `d`. Then `d` is `R`-linear
(`DG.d_smul`) and each graded piece is an `R`-submodule (`DG.DGAlgebra.gradingSubmodule`).-/
class DGAlgebra (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [DGAddCommGroup A] [DGRing A] : Prop where
  algebraMap_mem' : ∀ r : R, algebraMap R A r ∈ grading (M := A) 0
  d_algebraMap' : ∀ r : R, d (algebraMap R A r) = 0

section DGAlgebra

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A]
  [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]

/--
@isnad1 id=mem.0h3v.s6.0b4af5fe68cf from=translated src=- shape=7c690486 vocab=a9cab6e2
-/
theorem algebraMap_mem_grading (r : R) : algebraMap R A r ∈ grading (M := A) 0 :=
  DGAlgebra.algebraMap_mem' r

/--
@isnad1 id=eq.0h3v.s7.659ba7c579a5 from=translated src=- shape=e0f08d5c vocab=eb736597
-/
@[simp]
theorem d_algebraMap (r : R) : d (algebraMap R A r) = 0 :=
  DGAlgebra.d_algebraMap' r

variable {R}

/--
@isnad1 id=mem.1h5v.s7.eac344d54deb from=translated src=- shape=d48fb8f9 vocab=e05fa070
-/
theorem DGAlgebra.smul_mem {n : ℤ} (r : R) {a : A} (ha : a ∈ grading n) :
    r • a ∈ grading n := by
  rw [Algebra.smul_def]
  simpa using mul_mem_grading (algebraMap_mem_grading R r) ha

/--
@isnad1 id=eq.0h4v.s7.c557d24f8f83 from=translated src=- shape=4e7cd95e vocab=1d921eb3
-/
theorem d_smul_algebra (r : R) (a : A) : d (r • a) = r • d a := by
  rw [Algebra.smul_def, d_mul (algebraMap_mem_grading R r), d_algebraMap, zero_mul, zero_add,
    koszulSign, Int.negOnePow_zero, one_smul, Algebra.smul_def]

variable (R A)

/-- The graded pieces of a dg `R`-algebra as `R`-submodules.-/
def DGAlgebra.gradingSubmodule (n : ℤ) : Submodule R A where
  __ := grading (M := A) n
  smul_mem' r _ ha := DGAlgebra.smul_mem r ha

/--
@isnad1 id=iff.0h4v.s7.f4b5c7f6ee1f from=translated src=- shape=b15c8b09 vocab=2d31e7f2
-/
@[simp]
theorem DGAlgebra.mem_gradingSubmodule {n : ℤ} {a : A} :
    a ∈ DGAlgebra.gradingSubmodule R A n ↔ a ∈ grading n :=
  Iff.rfl

/--
@isnad1 id=eq.0h3v.s6.a53092af3d11 from=translated src=- shape=6f290209 vocab=539ebe99
-/
@[simp]
theorem DGAlgebra.gradingSubmodule_toAddSubgroup (n : ℤ) :
    (DGAlgebra.gradingSubmodule R A n).toAddSubgroup = grading n := rfl

instance DGAlgebra.gradedAlgebra : GradedAlgebra (DGAlgebra.gradingSubmodule R A) where
  one_mem := one_mem_grading
  mul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  decompose' := DirectSum.decompose (grading (M := A))
  left_inv := DirectSum.Decomposition.left_inv (ℳ := grading (M := A))
  right_inv := DirectSum.Decomposition.right_inv (ℳ := grading (M := A))

/-- The differential of a dg `R`-algebra as an `R`-linear map.-/
def DGAlgebra.dLinear : A →ₗ[R] A where
  __ := (d : A →+ A)
  map_smul' := d_smul_algebra

/--
@isnad1 id=eq.0h3v.s7.3c3680bdfbd2 from=translated src=- shape=a6f2dd5e vocab=59eb6a1f
-/
@[simp]
theorem DGAlgebra.dLinear_apply (a : A) : DGAlgebra.dLinear R A a = d a := rfl

/-- A dg ring is a dg `ℤ`-algebra.
@isnad1 id=dgalgebr.0h1v.s4.0ce86f54a42a from=translated src=- shape=a97491eb vocab=efe94a7b
-/
instance DGAlgebra.int : DGAlgebra ℤ A where
  algebraMap_mem' k := by simpa using zsmul_mem (one_mem_grading (A := A)) k
  d_algebraMap' k := by simpa using d_intCast (A := A) k

end DGAlgebra

end DG
