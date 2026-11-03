module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Homological.CosetDecomp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Induced maps of free modules along `ι : B → E` and exactness of induction
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

variable {B E : Type u} [Group B] [Group E] (ι : B →* E) (hι : Function.Injective ι)

/-- Coordinatewise `ρ : ℤ[B]^n → ℤ[E]^n`.-/
noncomputable def ρV {n : ℕ} : FreeMod B n →+ FreeMod E n where
  toFun w j := ρ ι (w j)
  map_zero' := by ext j : 1; simp
  map_add' w w' := by ext j : 1; simp

/--
@isnad1 id=eq.0h6v.s8.8b0cf69b720e from=translated src=- shape=fcc86b59 vocab=446134be
-/
theorem ρV_apply {n : ℕ} (w : FreeMod B n) (j : Fin n) : ρV ι w j = ρ ι (w j) := rfl

/--
@isnad1 id=eq.0h6v.s9.32c9a09fe5bc from=translated src=- shape=6215edc9 vocab=caa1353d
-/
theorem ρV_smul {n : ℕ} (l : ZG B) (w : FreeMod B n) : ρV ι (l • w) = ρ ι l • ρV ι w := by
  ext j : 1; simp [ρV_apply]

/-- The induced map `ℤ[E] ⊗_{ℤ[B]} d` in coordinates.-/
noncomputable def indMap {a b : ℕ} (d : FreeMod B a →ₗ[ZG B] FreeMod B b) :
    FreeMod E a →ₗ[ZG E] FreeMod E b where
  toFun x := ∑ j, x j • ρV ι (d (Pi.single j 1))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' l x := by simp [Finset.smul_sum, mul_smul]

/--
@isnad1 id=eq.0h7v.s10.b708fc1f5b1e from=translated src=- shape=071e4e20 vocab=32996032
-/
theorem indMap_ρV {a b : ℕ} (d : FreeMod B a →ₗ[ZG B] FreeMod B b) (w : FreeMod B a) :
    indMap ι d (ρV ι w) = ρV ι (d w) := by
  conv_rhs => rw [eq_sum_single w]
  simp [indMap, map_sum, ρV_smul, ρV_apply]

/--
@isnad1 id=eq.0h7v.s10.2bda2ae12025 from=translated src=- shape=61b52f0f vocab=8b592720
-/
theorem indMap_single {a b : ℕ} (d : FreeMod B a →ₗ[ZG B] FreeMod B b) (j : Fin a) :
    indMap ι d (Pi.single j 1) = ρV ι (d (Pi.single j 1)) := by
  have : (Pi.single j 1 : FreeMod E a) = ρV ι (Pi.single j 1) := by
    ext i : 1
    by_cases h : i = j
    · subst h; simp [ρV_apply]
    · simp [ρV_apply, h]
  rw [this, indMap_ρV]

/-- The `q`-component of a vector in `ℤ[E]^n`.-/
noncomputable def compV (q : E ⧸ ι.range) {n : ℕ} : FreeMod E n →+ FreeMod B n where
  toFun v j := decomp ι hι (v j) q
  map_zero' := by ext j : 1; simp
  map_add' v w := by ext j : 1; simp

/--
@isnad1 id=eq.1h7v.s9.5c29da1d86cd from=translated src=- shape=babf249d vocab=2ba5d71d
-/
theorem compV_apply (q : E ⧸ ι.range) {n : ℕ} (v : FreeMod E n) (j : Fin n) :
    compV ι hι q v j = decomp ι hι (v j) q := rfl

/--
@isnad1 id=eq.1h7v.s9.46b08be3abd2 from=translated src=- shape=46ba63c5 vocab=eecb104a
-/
theorem compV_smul_ρV (q : E ⧸ ι.range) {n : ℕ} (f : ZG E) (w : FreeMod B n) :
    compV ι hι q (f • ρV ι w) = decomp ι hι f q • w := by
  ext j : 1
  simp [compV_apply, ρV_apply, decomp_mul_ρ]

open scoped Classical in
/--
@isnad1 id=eq.1h7v.s9.bd8b7212465e from=translated src=- shape=449da446 vocab=c3e9b309
-/
theorem compV_out_smul (q q' : E ⧸ ι.range) {n : ℕ} (w : FreeMod B n) :
    compV ι hι q (MonoidAlgebra.single q'.out (1 : ℤ) • ρV ι w) = if q' = q then w else 0 := by
  ext j : 1
  simp only [compV_apply, Pi.smul_apply, ρV_apply, smul_eq_mul, decomp_out_mul]
  split_ifs <;> simp

/--
@isnad1 id=eq.1h8v.s10.4aa7248a2ee0 from=translated src=- shape=c642e5db vocab=dbccb242
-/
theorem compV_indMap (q : E ⧸ ι.range) {a b : ℕ} (d : FreeMod B a →ₗ[ZG B] FreeMod B b)
    (v : FreeMod E a) : compV ι hι q (indMap ι d v) = d (compV ι hι q v) := by
  conv_rhs => rw [eq_sum_single (compV ι hι q v)]
  simp only [indMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, compV_smul_ρV, map_smul]
  rfl

open scoped Classical in
/-- A finite set of cosets carrying all components of `v`.-/
noncomputable def cosetSupport {n : ℕ} (v : FreeMod E n) : Finset (E ⧸ ι.range) :=
  Finset.univ.biUnion fun j => (decomp ι hι (v j)).support

theorem eq_sum_compV {n : ℕ} (v : FreeMod E n) :
    v = ∑ q ∈ cosetSupport ι hι v, MonoidAlgebra.single q.out (1 : ℤ) • ρV ι (compV ι hι q v) := by
  ext j : 1
  simp only [Finset.sum_apply, Pi.smul_apply, ρV_apply, compV_apply, smul_eq_mul]
  conv_lhs => rw [← assemble_decomp ι hι (v j)]
  unfold assemble
  rw [Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset]
  · rfl
  · intro q hq
    simp only [cosetSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨j, hq⟩
  · intro q _; simp

theorem eq_zero_of_compV {n : ℕ} (v : FreeMod E n) (h : ∀ q, compV ι hι q v = 0) : v = 0 := by
  rw [eq_sum_compV ι hι v]
  simp [h]

/--
@isnad1 id=iff.1h7v.s10.76df3f25e2b6 from=translated src=- shape=136712b0 vocab=dbccb242
-/
theorem indMap_eq_zero_iff {a b : ℕ} (d : FreeMod B a →ₗ[ZG B] FreeMod B b) (v : FreeMod E a) :
    indMap ι d v = 0 ↔ ∀ q, d (compV ι hι q v) = 0 := by
  constructor
  · intro h q
    rw [← compV_indMap, h, map_zero]
  · intro h
    apply eq_zero_of_compV ι hι
    intro q
    rw [compV_indMap, h]

/--
@isnad1 id=mem.2h7v.s10.83f165d388ce from=translated src=- shape=44f5fdd0 vocab=bb1eafb9
-/
theorem mem_range_indMap {a b : ℕ} (d : FreeMod B a →ₗ[ZG B] FreeMod B b) (v : FreeMod E b)
    (h : ∀ q, compV ι hι q v ∈ LinearMap.range d) : v ∈ LinearMap.range (indMap ι d) := by
  choose w hw using h
  refine ⟨∑ q ∈ cosetSupport ι hι v, MonoidAlgebra.single q.out (1 : ℤ) • ρV ι (w q), ?_⟩
  rw [map_sum]
  conv_rhs => rw [eq_sum_compV ι hι v]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, indMap_ρV, hw]

/--
@isnad1 id=mem.2h6v.s10.842222ce60b8 from=translated src=- shape=c09425a2 vocab=f634644d
-/
theorem mem_span_of_compV {n : ℕ} (S : Submodule (ZG B) (FreeMod B n)) (v : FreeMod E n)
    (h : ∀ q, compV ι hι q v ∈ S) :
    v ∈ Submodule.span (ZG E) (ρV ι '' (S : Set (FreeMod B n))) := by
  rw [eq_sum_compV ι hι v]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨_, h q, rfl⟩

include hι in
/-- Induction preserves exactness.
@isnad1 id=eq.2h8v.s10.bda991fd8f31 from=translated src=- shape=4f4a7210 vocab=7e0ede1d
-/
theorem indMap_exact {a b c : ℕ} (d : FreeMod B b →ₗ[ZG B] FreeMod B c)
    (d' : FreeMod B a →ₗ[ZG B] FreeMod B b) (h : LinearMap.ker d = LinearMap.range d') :
    LinearMap.ker (indMap ι d) = LinearMap.range (indMap ι d') := by
  ext v
  constructor
  · intro hv
    apply mem_range_indMap ι hι
    intro q
    rw [← h]
    exact (indMap_eq_zero_iff ι hι d v).1 hv q
  · rintro ⟨w, rfl⟩
    show indMap ι d (indMap ι d' w) = 0
    rw [indMap_eq_zero_iff ι hι]
    intro q
    rw [compV_indMap]
    have : d' (compV ι hι q w) ∈ LinearMap.ker d := by rw [h]; exact ⟨_, rfl⟩
    exact this

end TheoremA
