import Tengoku.AbelFormalization.AbelFormalization.FiniteWeightLengthDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Exact sequences for finite-weight initial submodules

Each initial piece is the actual projection of
the submodule whose earlier coordinates vanish. The prefix-length equality
is derived from explicit exact sequences, rather than assumed.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [Ring R] {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/--
@isnad1 id=eq.1h6v.s9.831cf6adf6eb from=translated src=- shape=075da313 vocab=c7143d4b
-/
theorem finiteWeightPrefixProjection_comp_eq_left_of_le {k l : ℕ} (hkl : k ≤ l)
    (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k (finiteWeightPrefixProjection R M l x) =
      finiteWeightPrefixProjection R M k x := by
  ext i
  by_cases hi : i.val < k
  · simp [finiteWeightPrefixProjection_apply, hi, lt_of_lt_of_le hi hkl]
  · simp [finiteWeightPrefixProjection_apply, hi]

/--
@isnad1 id=eq.0h5v.s9.321b7be2c5be from=translated src=- shape=17dd81a1 vocab=ebfb601b
-/
theorem finiteWeightPrefixProjection_succ (i : Fin n) (x : ∀ j, M j) :
    finiteWeightPrefixProjection R M (i.val + 1) x =
      finiteWeightPrefixProjection R M i.val x + Pi.single i (x i) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [finiteWeightPrefixProjection_apply]
  · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    by_cases hj : j.val < i.val
    · simp [finiteWeightPrefixProjection_apply, hj, Nat.lt_succ_of_lt hj,
        hji]
    · have hjsucc : ¬j.val < i.val + 1 := by
        intro h
        exact hval (Nat.le_antisymm (Nat.lt_succ_iff.mp h) (Nat.le_of_not_gt hj))
      simp [finiteWeightPrefixProjection_apply, hj, hjsucc,
        hji]

/--
@isnad1 id=eq.0h3v.s8.7e96f3b8821f from=translated src=- shape=52d828ed vocab=1ee6e696
-/
@[simp]
theorem finiteWeightPrefixProjection_zero : finiteWeightPrefixProjection R M 0 = 0 := by
  ext x i
  simp [finiteWeightPrefixProjection_apply]

/--
@isnad1 id=eq.1h4v.s7.dedd722e5bad from=translated src=- shape=59f134ca vocab=f96fcdcc
-/
theorem finiteWeightPrefixProjection_eq_id_of_le {k : ℕ} (hnk : n ≤ k) :
    finiteWeightPrefixProjection R M k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  simp [finiteWeightPrefixProjection_apply, lt_of_lt_of_le i.isLt hnk]

/-- The image of a submodule under an actual coordinate prefix projection.-/
def finiteWeightPrefixImage (U : Submodule R (∀ i, M i)) (k : ℕ) :
    Submodule R (∀ i, M i) := U.map (finiteWeightPrefixProjection R M k)

/-- The i-th least-weight piece of all elements of U whose lower
coordinates vanish.-/
def finiteWeightInitialPiece (U : Submodule R (∀ i, M i)) (i : Fin n) :
    Submodule R (M i) :=
  (U ⊓ (finiteWeightPrefixProjection R M i.val).ker).map (LinearMap.proj i)

/--
@isnad1 id=mem.1h6v.s8.c219053491a1 from=translated src=- shape=729af6e5 vocab=93f02167
-/
theorem single_mem_finiteWeightPrefixImage_succ
    (U : Submodule R (∀ i, M i)) (i : Fin n) {v : M i}
    (hv : v ∈ finiteWeightInitialPiece U i) :
    Pi.single i v ∈ finiteWeightPrefixImage U (i.val + 1) := by
  obtain ⟨x, hx, hxi⟩ := hv
  refine ⟨x, hx.1, ?_⟩
  have hxzero : finiteWeightPrefixProjection R M i.val x = 0 := hx.2
  change finiteWeightPrefixProjection R M (i.val + 1) x = Pi.single i v
  rw [finiteWeightPrefixProjection_succ, hxzero, zero_add]
  exact congrArg (Pi.single i) hxi

/--
@isnad1 id=mem.1h6v.s9.06cad5803ecc from=translated src=- shape=779587e2 vocab=a08ff863
-/
theorem prefix_mem_finiteWeightPrefixImage
    (U : Submodule R (∀ i, M i)) (i : Fin n) {x : ∀ j, M j}
    (hx : x ∈ finiteWeightPrefixImage U (i.val + 1)) :
    finiteWeightPrefixProjection R M i.val x ∈ finiteWeightPrefixImage U i.val := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨v, hv, (finiteWeightPrefixProjection_comp_eq_left_of_le
    (Nat.le_succ i.val) v).symm⟩

/-- The first map in the exact sequence for adjoining one coordinate.-/
def finiteWeightPieceToPrefix (U : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightInitialPiece U i →ₗ[R] finiteWeightPrefixImage U (i.val + 1) :=
  LinearMap.codRestrict _
    ((LinearMap.single R M i).domRestrict (finiteWeightInitialPiece U i))
    (fun v => single_mem_finiteWeightPrefixImage_succ U i v.property)

/-- The second map simply forgets the last coordinate of a prefix image.-/
def finiteWeightPrefixToPrefix (U : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightPrefixImage U (i.val + 1) →ₗ[R] finiteWeightPrefixImage U i.val :=
  LinearMap.codRestrict _
    ((finiteWeightPrefixProjection R M i.val).domRestrict
      (finiteWeightPrefixImage U (i.val + 1)))
    (fun x => prefix_mem_finiteWeightPrefixImage U i x.property)

/--
@isnad1 id=eq.0h6v.s10.70855d8c50f3 from=translated src=- shape=5426860f vocab=400b557c
-/
@[simp]
theorem finiteWeightPieceToPrefix_coe (U : Submodule R (∀ i, M i))
    (i : Fin n) (v : finiteWeightInitialPiece U i) :
    ((finiteWeightPieceToPrefix U i v) : ∀ j, M j) = Pi.single i (v : M i) := rfl

/--
@isnad1 id=eq.0h6v.s11.f28b269d9c12 from=translated src=- shape=9795038a vocab=4c360652
-/
@[simp]
theorem finiteWeightPrefixToPrefix_coe (U : Submodule R (∀ i, M i))
    (i : Fin n) (x : finiteWeightPrefixImage U (i.val + 1)) :
    ((finiteWeightPrefixToPrefix U i x) : ∀ j, M j) =
      finiteWeightPrefixProjection R M i.val (x : ∀ j, M j) := rfl

/--
@isnad1 id=injectiv.0h5v.s10.1bd2d8f1b5bd from=translated src=- shape=8458c61f vocab=1a8148cf
-/
theorem finiteWeightPieceToPrefix_injective (U : Submodule R (∀ i, M i))
    (i : Fin n) : Function.Injective (finiteWeightPieceToPrefix U i) := by
  intro v w h
  apply Subtype.ext
  have hi := congrFun (congrArg Subtype.val h) i
  simpa using hi

/--
@isnad1 id=surjecti.0h5v.s11.dbbf5e041223 from=translated src=- shape=2f2b935b vocab=23cc97f9
-/
theorem finiteWeightPrefixToPrefix_surjective (U : Submodule R (∀ i, M i))
    (i : Fin n) : Function.Surjective (finiteWeightPrefixToPrefix U i) := by
  intro x
  obtain ⟨v, hv, hvx⟩ := x.property
  refine ⟨⟨finiteWeightPrefixProjection R M (i.val + 1) v, ⟨v, hv, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change finiteWeightPrefixProjection R M i.val
    (finiteWeightPrefixProjection R M (i.val + 1) v) = (x : ∀ j, M j)
  rw [finiteWeightPrefixProjection_comp_eq_left_of_le (Nat.le_succ i.val)]
  exact hvx

/-- The first image is exactly the kernel of forgetting the last
coordinate. Both maps are explicit maps of the actual prefix modules.
@isnad1 id=exact.0h5v.s11.6642b5adf610 from=translated src=- shape=00da26be vocab=5907ef05
-/
theorem finiteWeightPrefix_exact (U : Submodule R (∀ i, M i)) (i : Fin n) :
    Function.Exact (finiteWeightPieceToPrefix U i) (finiteWeightPrefixToPrefix U i) := by
  intro x
  constructor
  · intro hx
    have hxzero : finiteWeightPrefixProjection R M i.val (x : ∀ j, M j) = 0 :=
      congrArg Subtype.val hx
    obtain ⟨v, hv, hvx⟩ := x.property
    have hvzero : finiteWeightPrefixProjection R M i.val v = 0 := by
      calc
        finiteWeightPrefixProjection R M i.val v =
            finiteWeightPrefixProjection R M i.val
              (finiteWeightPrefixProjection R M (i.val + 1) v) :=
          (finiteWeightPrefixProjection_comp_eq_left_of_le (Nat.le_succ i.val) v).symm
        _ = finiteWeightPrefixProjection R M i.val (x : ∀ j, M j) :=
          congrArg (finiteWeightPrefixProjection R M i.val) hvx
        _ = 0 := hxzero
    let vi : finiteWeightInitialPiece U i := ⟨v i, ⟨v, ⟨hv, hvzero⟩, rfl⟩⟩
    refine ⟨vi, ?_⟩
    apply Subtype.ext
    change Pi.single i (v i) = (x : ∀ j, M j)
    rw [← hvx, finiteWeightPrefixProjection_succ, hvzero, zero_add]
  · rintro ⟨v, rfl⟩
    apply Subtype.ext
    change finiteWeightPrefixProjection R M i.val (Pi.single i (v : M i)) = 0
    simp [finiteWeightPrefixProjection_single]

/-- Length additivity for the actual prefix images, derived from the
explicit short exact sequence. No finite-length hypothesis is needed.
@isnad1 id=eq.0h5v.s9.7b81e49493e7 from=translated src=- shape=fb3b7938 vocab=3a1353dd
-/
theorem finiteWeightPrefixImage_length_succ (U : Submodule R (∀ i, M i)) (i : Fin n) :
    Module.length R (finiteWeightPrefixImage U (i.val + 1)) =
      Module.length R (finiteWeightInitialPiece U i) +
        Module.length R (finiteWeightPrefixImage U i.val) :=
  Module.length_eq_add_of_exact (finiteWeightPieceToPrefix U i)
    (finiteWeightPrefixToPrefix U i) (finiteWeightPieceToPrefix_injective U i)
    (finiteWeightPrefixToPrefix_surjective U i) (finiteWeightPrefix_exact U i)

/-- The actual full initial submodule, collecting every possible
least-weight component, not the initial forms of a selected generating list.-/
def finiteWeightInitial (U : Submodule R (∀ i, M i)) : Submodule R (∀ i, M i) :=
  Submodule.pi Set.univ (finiteWeightInitialPiece U)

/--
@isnad1 id=iff.0h5v.s8.e0c4b3eda459 from=translated src=- shape=71868f9c vocab=8dea25ff
-/
@[simp]
theorem mem_finiteWeightInitial_iff (U : Submodule R (∀ i, M i)) (x : ∀ i, M i) :
    x ∈ finiteWeightInitial U ↔ ∀ i, x i ∈ finiteWeightInitialPiece U i := by
  simp [finiteWeightInitial, Submodule.mem_pi]

/--
@isnad1 id=mem.1h6v.s8.a5d9d53672c7 from=translated src=- shape=c47abb0e vocab=7a0c6544
-/
theorem single_mem_finiteWeightInitial (U : Submodule R (∀ i, M i)) (i : Fin n)
    {v : M i} (hv : v ∈ finiteWeightInitialPiece U i) :
    Pi.single i v ∈ finiteWeightInitial U := by
  classical
  apply (mem_finiteWeightInitial_iff U _).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hv
  · simp [hji]

/--
@isnad1 id=mem.1h6v.s8.302ec7fb7083 from=translated src=- shape=7d257587 vocab=96530273
-/
theorem finiteWeightInitial_homogeneous (U : Submodule R (∀ i, M i)) :
    ∀ x ∈ finiteWeightInitial U, ∀ i, Pi.single i (x i) ∈ finiteWeightInitial U := by
  intro x hx i
  exact single_mem_finiteWeightInitial U i ((mem_finiteWeightInitial_iff U x).mp hx i)

/-- All least-coordinate forms of all elements of U; a zero coordinate
contributes only the zero vector and does not alter the generated submodule.-/
def finiteWeightInitialGenerators (U : Submodule R (∀ i, M i)) : Set (∀ i, M i) :=
  {v | ∃ x ∈ U, ∃ i : Fin n, finiteWeightPrefixProjection R M i.val x = 0 ∧
    v = Pi.single i (x i)}

/-- The product-of-pieces construction is exactly the full span of the
least-weight components of all U-elements.
@isnad1 id=eq.0h4v.s7.f7126a580ace from=translated src=- shape=3d19a8d6 vocab=1561ef4f
-/
theorem finiteWeightInitial_eq_span (U : Submodule R (∀ i, M i)) :
    finiteWeightInitial U = Submodule.span R (finiteWeightInitialGenerators U) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply (Submodule.span R (finiteWeightInitialGenerators U)).sum_mem
    intro i hi
    obtain ⟨v, hv, hvi⟩ := (mem_finiteWeightInitial_iff U x).mp hx i
    apply Submodule.subset_span
    exact ⟨v, hv.1, i, hv.2, congrArg (Pi.single i) hvi.symm⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, i, hlow, rfl⟩
    exact single_mem_finiteWeightInitial U i ⟨x, ⟨hx, hlow⟩, rfl⟩

/-- Initial formation fixes every coordinatewise homogeneous submodule.
@isnad1 id=eq.1h4v.s8.a98dedcc8a85 from=translated src=- shape=7b9ac5cb vocab=96530273
-/
theorem finiteWeightInitial_eq_of_homogeneous (U : Submodule R (∀ i, M i))
    (hU : ∀ x ∈ U, ∀ i, Pi.single i (x i) ∈ U) : finiteWeightInitial U = U := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply U.sum_mem
    intro i hi
    obtain ⟨v, hv, hvi⟩ := (mem_finiteWeightInitial_iff U x).mp hx i
    change v i = x i at hvi
    rw [← hvi]
    exact hU v hv.1 i
  · intro x hx
    apply (mem_finiteWeightInitial_iff U x).mpr
    intro i
    refine ⟨Pi.single i (x i), ⟨hU x hx i, ?_⟩, ?_⟩
    · change finiteWeightPrefixProjection R M i.val (Pi.single i (x i)) = 0
      simp [finiteWeightPrefixProjection_single]
    · simp

/-- Initial formation leaves every projected kernel piece unchanged.
@isnad1 id=eq.0h5v.s7.726f3f9f21f8 from=translated src=- shape=a63f0039 vocab=78b527d4
-/
theorem finiteWeightInitialPiece_initial (U : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightInitialPiece (finiteWeightInitial U) i = finiteWeightInitialPiece U i := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_finiteWeightInitial_iff U x).mp hx.1 i
  · intro v hv
    refine ⟨Pi.single i v, ⟨single_mem_finiteWeightInitial U i hv, ?_⟩, ?_⟩
    · change finiteWeightPrefixProjection R M i.val (Pi.single i v) = 0
      simp [finiteWeightPrefixProjection_single]
    · simp

/--
@isnad1 id=eq.0h4v.s7.58ac93ad0645 from=translated src=- shape=e18bf8fa vocab=69f425b0
-/
@[simp]
theorem finiteWeightPrefixImage_zero (U : Submodule R (∀ i, M i)) :
    finiteWeightPrefixImage U 0 = ⊥ := by
  simp [finiteWeightPrefixImage]

/--
@isnad1 id=eq.1h5v.s7.8ccef53b124c from=translated src=- shape=26804a41 vocab=06566076
-/
theorem finiteWeightPrefixImage_eq_self_of_le (U : Submodule R (∀ i, M i))
    {k : ℕ} (hnk : n ≤ k) : finiteWeightPrefixImage U k = U := by
  rw [finiteWeightPrefixImage, finiteWeightPrefixProjection_eq_id_of_le hnk,
    Submodule.map_id]

/-- Initial formation preserves every prefix length. The proof uses the
explicit exact sequence repeatedly, and never cancels infinite lengths.
@isnad1 id=eq.0h5v.s9.d4d0f251f537 from=translated src=- shape=e0300ecb vocab=65524d0e
-/
theorem finiteWeightInitial_prefix_length (U : Submodule R (∀ i, M i)) (k : ℕ) :
    Module.length R (finiteWeightPrefixImage (finiteWeightInitial U) k) =
      Module.length R (finiteWeightPrefixImage U k) := by
  have hbounded : ∀ k : ℕ, k ≤ n →
      Module.length R (finiteWeightPrefixImage (finiteWeightInitial U) k) =
        Module.length R (finiteWeightPrefixImage U k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [finiteWeightPrefixImage_zero, finiteWeightPrefixImage_zero]
    | succ k ih =>
      intro hk
      let i : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
      have hrec := finiteWeightPrefixImage_length_succ (finiteWeightInitial U) i
      rw [finiteWeightInitialPiece_initial, ih (Nat.le_of_succ_le hk)] at hrec
      exact hrec.trans (finiteWeightPrefixImage_length_succ U i).symm
  by_cases hk : k ≤ n
  · exact hbounded k hk
  · have hnk : n ≤ k := le_of_not_ge hk
    rw [finiteWeightPrefixImage_eq_self_of_le _ hnk,
      finiteWeightPrefixImage_eq_self_of_le _ hnk]
    have h := hbounded n le_rfl
    rw [finiteWeightPrefixImage_eq_self_of_le _ (le_refl n),
      finiteWeightPrefixImage_eq_self_of_le _ (le_refl n)] at h
    exact h

/-- In particular, the full initial submodule has the same actual module
length as the original submodule.
@isnad1 id=eq.0h4v.s9.6a4e5771f1a6 from=translated src=- shape=84bdd9a7 vocab=d18a878c
-/
theorem finiteWeightInitial_length (U : Submodule R (∀ i, M i)) :
    Module.length R (finiteWeightInitial U) = Module.length R U := by
  have h := finiteWeightInitial_prefix_length U n
  rw [finiteWeightPrefixImage_eq_self_of_le _ (le_refl n),
    finiteWeightPrefixImage_eq_self_of_le _ (le_refl n)] at h
  exact h

end AbelFormalization
