import Tengoku.Seed.RingTheory.Length
import Tengoku.Seed.LinearAlgebra.Pi
import Tengoku.Seed.Algebra.Module.Submodule.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Prefix lengths detect invariance under a finite triangular map

The coordinates are actual finite product coordinates, with arbitrary
modules at the individual ordered weights. Prefix lengths detect
invariance of homogeneous submodules under a triangular linear equivalence.
-/

noncomputable section

namespace AbelFormalization

section Length

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- An inclusion of submodules in a finite-length module is equality if
their lengths agree.
@isnad1 id=eq.2h4v.s7.498a61f35b32 from=translated src=- shape=3c6fa440 vocab=5e55fd5e
-/
theorem submodule_eq_of_le_of_length_eq
    [IsArtinian R V] [IsNoetherian R V] {A B : Submodule R V}
    (hAB : A ≤ B) (hlen : Module.length R A = Module.length R B) : A = B := by
  by_contra hne
  have hlt : A < B := (lt_iff_le_and_ne).mpr ⟨hAB, hne⟩
  have hstrict := Submodule.height_strictMono hlt
  rw [← Module.length_submodule, ← Module.length_submodule] at hstrict
  exact (ne_of_lt hstrict) hlen

/--
@isnad1 id=eq.0h4v.s8.29c2a8c75a2e from=translated src=- shape=7c08e2ea vocab=2fe4a380
-/
theorem length_map_linearEquiv (J : V ≃ₗ[R] V) (N : Submodule R V) :
    Module.length R (N.map J.toLinearMap) = Module.length R N :=
  (Submodule.equivMapOfInjective J.toLinearMap J.injective N).length_eq.symm

end Length

section Prefixes

variable (R : Type*) [Ring R] {n : ℕ}
variable (M : Fin n → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Projection onto the coordinates with index strictly less than `k`.-/
def finiteWeightPrefixProjection (k : ℕ) : (∀ i, M i) →ₗ[R] (∀ i, M i) where
  toFun x i := if i.val < k then x i else 0
  map_add' x y := by
    ext i
    by_cases hi : i.val < k <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : i.val < k <;> simp [hi]

/-- The actual low-weight coordinate submodule.-/
def finiteWeightPrefix (k : ℕ) : Submodule R (∀ i, M i) :=
  (finiteWeightPrefixProjection R M k).range

variable {R M}

/--
@isnad1 id=eq.0h6v.s8.968cc4d74a17 from=translated src=- shape=7a95def3 vocab=e3528ccf
-/
@[simp]
theorem finiteWeightPrefixProjection_apply (k : ℕ) (x : ∀ i, M i) (i : Fin n) :
    finiteWeightPrefixProjection R M k x i = if i.val < k then x i else 0 := rfl

/--
@isnad1 id=eq.1h6v.s9.dea41143966d from=translated src=- shape=98bf7dea vocab=c7143d4b
-/
theorem finiteWeightPrefixProjection_comp_of_le {k l : ℕ} (hlk : l ≤ k)
    (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k (finiteWeightPrefixProjection R M l x) =
      finiteWeightPrefixProjection R M l x := by
  ext i
  by_cases hi : i.val < l
  · simp [finiteWeightPrefixProjection_apply, hi, lt_of_lt_of_le hi hlk]
  · simp [finiteWeightPrefixProjection_apply, hi]

/--
@isnad1 id=eq.0h5v.s9.3d3463250b7c from=translated src=- shape=98c78ea0 vocab=6c0a9f67
-/
@[simp]
theorem finiteWeightPrefixProjection_idempotent (k : ℕ) (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k (finiteWeightPrefixProjection R M k x) =
      finiteWeightPrefixProjection R M k x :=
  finiteWeightPrefixProjection_comp_of_le le_rfl x

/--
@isnad1 id=iff.0h5v.s8.a09ba6f39927 from=translated src=- shape=e2cddac2 vocab=c9db22e0
-/
theorem finiteWeightPrefixProjection_eq_self_iff (k : ℕ) (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k x = x ↔ ∀ i, k ≤ i.val → x i = 0 := by
  constructor
  · intro h i hi
    have hcoord := congrFun h i
    simpa [finiteWeightPrefixProjection_apply, not_lt.mpr hi] using hcoord.symm
  · intro h
    ext i
    by_cases hi : i.val < k
    · simp [finiteWeightPrefixProjection_apply, hi]
    · simp [finiteWeightPrefixProjection_apply, hi, h i (le_of_not_gt hi)]

/--
@isnad1 id=iff.0h5v.s8.9858a42d2dfe from=translated src=- shape=d464b3ea vocab=df09ce67
-/
theorem mem_finiteWeightPrefix_iff (k : ℕ) (x : ∀ i, M i) :
    x ∈ finiteWeightPrefix R M k ↔ finiteWeightPrefixProjection R M k x = x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact finiteWeightPrefixProjection_idempotent k v
  · intro hx
    exact ⟨x, hx⟩

/--
@isnad1 id=eq.0h6v.s8.d6afbbcc3140 from=translated src=- shape=932118cd vocab=59ada7d8
-/
theorem finiteWeightPrefixProjection_single (k : ℕ) (i : Fin n) (v : M i) :
    finiteWeightPrefixProjection R M k (Pi.single i v) =
      if i.val < k then Pi.single i v else 0 := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hi : i.val < k <;> simp [finiteWeightPrefixProjection_apply, hi]
  · by_cases hi : i.val < k <;>
      simp [finiteWeightPrefixProjection_apply, hji, hi]

/-- For a coordinatewise homogeneous submodule, its prefix image is
exactly its intersection with the corresponding coordinate submodule.
@isnad1 id=eq.1h5v.s9.524bcdafad48 from=translated src=- shape=89280c7c vocab=fd846c75
-/
theorem map_finiteWeightPrefixProjection_eq_inf
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N) (k : ℕ) :
    N.map (finiteWeightPrefixProjection R M k) = N ⊓ finiteWeightPrefix R M k := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    rw [← LinearMap.sum_single_apply M (finiteWeightPrefixProjection R M k x)]
    apply N.sum_mem
    intro i hi
    by_cases hik : i.val < k
    · simpa [finiteWeightPrefixProjection_apply, hik] using hN x hx i
    · simp [finiteWeightPrefixProjection_apply, hik]
  · intro x hx
    exact ⟨x, hx.1, (mem_finiteWeightPrefix_iff k x).mp hx.2⟩

/-- A unipotent triangular map preserves every low-weight prefix.
Its structural hypothesis is the literal coordinate form of `J-id`
strictly lowering the weight of a homogeneous vector.
@isnad1 id=mem.2h6v.s10.beb820925853 from=translated src=- shape=f3ccac3a vocab=1d065470
-/
theorem triangular_map_preserves_finiteWeightPrefix
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (k : ℕ) {x : ∀ i, M i} (hx : x ∈ finiteWeightPrefix R M k) :
    J x ∈ finiteWeightPrefix R M k := by
  classical
  have hxzero := (finiteWeightPrefixProjection_eq_self_iff k x).mp
    ((mem_finiteWeightPrefix_iff k x).mp hx)
  apply (mem_finiteWeightPrefix_iff k (J x)).mpr
  conv_rhs => rw [← LinearMap.sum_single_apply M x, map_sum]
  conv_lhs => rw [← LinearMap.sum_single_apply M x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : i.val < k
  · calc
      finiteWeightPrefixProjection R M k (J (Pi.single i (x i))) =
          finiteWeightPrefixProjection R M k
            (Pi.single i (x i) +
              finiteWeightPrefixProjection R M i.val (J (Pi.single i (x i)))) :=
        congrArg (finiteWeightPrefixProjection R M k) (htri i (x i))
      _ = Pi.single i (x i) +
          finiteWeightPrefixProjection R M i.val (J (Pi.single i (x i))) := by
        rw [map_add, finiteWeightPrefixProjection_single, ite_eq_left hik,
          finiteWeightPrefixProjection_comp_of_le (Nat.le_of_lt hik)]
      _ = J (Pi.single i (x i)) := (htri i (x i)).symm
  · simp [hxzero i (le_of_not_gt hik)]

/-- Triangularity gives an actual inclusion, before any comparison of
lengths: the image of the old prefix lies in the prefix image of `J N`.
@isnad1 id=le.1h6v.s10.bf00849b4d60 from=translated src=- shape=47cbf831 vocab=7fbbfeeb
-/
theorem map_inf_prefix_le_prefix_map
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i)) (k : ℕ) :
    (N ⊓ finiteWeightPrefix R M k).map J.toLinearMap ≤
      (N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨J x, ⟨x, hx.1, rfl⟩, ?_⟩
  exact (mem_finiteWeightPrefix_iff k (J x)).mp
    (triangular_map_preserves_finiteWeightPrefix J htri k hx.2)

/-- For homogeneous `N`, every prefix-image length weakly increases
under an actual unipotent lower-triangular linear equivalence.
@isnad1 id=le.2h6v.s11.ea1487fd85b9 from=translated src=- shape=7bb3b556 vocab=46103772
-/
theorem finiteWeightPrefix_length_le_map
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N) (k : ℕ) :
    Module.length R (N.map (finiteWeightPrefixProjection R M k)) ≤
      Module.length R ((N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k)) := by
  rw [map_finiteWeightPrefixProjection_eq_inf N hN k,
    ← length_map_linearEquiv J (N ⊓ finiteWeightPrefix R M k)]
  rw [Module.length_submodule, Module.length_submodule]
  exact Order.height_mono (map_inf_prefix_le_prefix_map J htri N k)

variable [IsArtinian R (∀ i, M i)] [IsNoetherian R (∀ i, M i)]

/-- Equality of all prefix-image lengths detects actual `J`-invariance.
This proves the decisive finite-length implication without exterior powers
and without assuming an identity about initial submodules.
@isnad1 id=eq.3h5v.s11.c862b1c0227f from=translated src=- shape=417378c5 vocab=bd3b1942
-/
theorem triangular_invariant_of_finiteWeightPrefix_lengths_eq
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hlen : ∀ k : ℕ,
      Module.length R ((N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k)) =
        Module.length R (N.map (finiteWeightPrefixProjection R M k))) :
    N.map J.toLinearMap = N := by
  classical
  have hprefix (k : ℕ) : (N ⊓ finiteWeightPrefix R M k).map J.toLinearMap =
      (N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k) := by
    apply submodule_eq_of_le_of_length_eq (map_inf_prefix_le_prefix_map J htri N k)
    rw [length_map_linearEquiv, hlen k, map_finiteWeightPrefixProjection_eq_inf N hN k]
  have hle : N ≤ N.map J.toLinearMap := by
    intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply (N.map J.toLinearMap).sum_mem
    intro i hi
    let v : ∀ i, M i := Pi.single i (x i)
    have hv : v ∈ N := hN x hx i
    have hp : finiteWeightPrefixProjection R M i.val (J v) ∈
        (N.map J.toLinearMap).map (finiteWeightPrefixProjection R M i.val) :=
      ⟨J v, ⟨v, hv, rfl⟩, rfl⟩
    rw [← hprefix i.val] at hp
    obtain ⟨w, hw, hJw⟩ := hp
    have hJw' : J w = finiteWeightPrefixProjection R M i.val (J v) := hJw
    refine ⟨v - w, N.sub_mem hv hw.1, ?_⟩
    change J (v - w) = v
    rw [map_sub, hJw']
    exact sub_eq_iff_eq_add.mpr (htri i (x i))
  exact (submodule_eq_of_le_of_length_eq hle (length_map_linearEquiv J N).symm).symm

end Prefixes

end AbelFormalization
