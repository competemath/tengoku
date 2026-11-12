import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Flattening finite families of variable-length traces

This module turns a finite family of variable-length operation blocks into
one chronological finite trace.  The core equivalence remembers both the
cluster and the local operation index.  Prefix offsets and boundary indices
make its arithmetic convention explicit.

The final section specializes the construction to the three phases used by
an ordered-cluster transfer: a list of individual decrements, one first
simultaneous step, and a finite list of extra retained steps.  No polynomial,
ideal, or analytic data occurs here.
-/

set_option autoImplicit false

namespace AbelFormalization
namespace FiniteFamilyFlattening

open scoped BigOperators

universe u

/-! ## General finite flattening -/

/-- The total length of a finite family of operation blocks.-/
def totalCount {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) : ℕ :=
  ∑ c, length c

/-- The number of operations in clusters strictly before `boundary`.

The boundary type has one more element than the cluster type: zero is the
initial boundary and `Fin.last clusterCount` is the terminal boundary.-/
def prefixOffset {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (boundary : Fin (clusterCount + 1)) : ℕ :=
  ∑ c : Fin boundary,
    length (Fin.castLE (Nat.le_of_lt_succ boundary.isLt) c)

/--
@isnad1 id=eq.0h2v.s5.49367eeba4ff from=translated src=- shape=8f01e93f vocab=39ee1034
-/
@[simp]
theorem prefixOffset_zero {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) :
    prefixOffset length 0 = 0 := by
  simp [prefixOffset]

/-- Crossing cluster `c` adds exactly its local length.
@isnad1 id=eq.0h3v.s5.639dfb95eaa2 from=translated src=- shape=40a7bf81 vocab=6bde1a1c
-/
theorem prefixOffset_succ {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) (c : Fin clusterCount) :
    prefixOffset length c.succ =
      prefixOffset length c.castSucc + length c := by
  unfold prefixOffset
  change (∑ i : Fin (c.val + 1), length (Fin.castLE _ i)) =
    (∑ i : Fin c.val, length (Fin.castLE _ i)) + length c
  rw [Fin.sum_univ_castSucc]
  congr 1

/-- Prefix offsets strictly increase across positive-length blocks.
@isnad1 id=lt.1h3v.s5.0eb65809a24d from=translated src=- shape=54470fe1 vocab=da1e7917
-/
theorem prefixOffset_lt_succ {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (c : Fin clusterCount) :
    prefixOffset length c.castSucc < prefixOffset length c.succ := by
  rw [prefixOffset_succ]
  exact Nat.lt_add_of_pos_right (hpositive c)

/-- The terminal prefix offset is the full sum of local lengths.
@isnad1 id=eq.0h2v.s4.4cbabda8fdb0 from=translated src=- shape=f5fe031d vocab=9153f086
-/
@[simp]
theorem prefixOffset_last {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) :
    prefixOffset length (Fin.last clusterCount) = totalCount length := by
  unfold prefixOffset totalCount
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- The canonical equivalence between a global operation index and its
dependent pair of cluster and local indices.-/
def flattenEquiv {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) :
    Fin (totalCount length) ≃ Σ c, Fin (length c) :=
  finSigmaFinEquiv.symm

/-- Insert one local operation into the global chronological index.-/
def flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    Fin (totalCount length) :=
  finSigmaFinEquiv ⟨c, i⟩

/--
@isnad1 id=eq.0h4v.s6.65a6b78a6ae0 from=translated src=- shape=e9165d12 vocab=12efd9d9
-/
@[simp]
theorem flattenEquiv_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    flattenEquiv length (flattenIndex length c i) = ⟨c, i⟩ := by
  exact finSigmaFinEquiv.symm_apply_apply ⟨c, i⟩

/-- Look up both dependent local coordinates of a global operation.-/
def lookup {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) : Σ c, Fin (length c) :=
  flattenEquiv length j

/-- The cluster containing a global operation.-/
def lookupCluster {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) : Fin clusterCount :=
  (lookup length j).1

/-- The local index of a global operation inside its cluster.-/
def lookupLocal {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) :
    Fin (length (lookupCluster length j)) :=
  (lookup length j).2

/--
@isnad1 id=eq.0h4v.s5.618acb497a7f from=translated src=- shape=15e9e733 vocab=5ec05089
-/
@[simp]
theorem lookup_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    lookup length (flattenIndex length c i) = ⟨c, i⟩ := by
  exact flattenEquiv_flattenIndex length c i

/--
@isnad1 id=eq.0h4v.s4.1bdaafa48e1c from=translated src=- shape=84453fa2 vocab=6a9f1a5d
-/
@[simp]
theorem lookupCluster_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    lookupCluster length (flattenIndex length c i) = c := by
  simp [lookupCluster]

/-- Re-inserting the coordinates obtained by lookup returns the original
global index.
@isnad1 id=eq.0h3v.s4.e914a2ca6244 from=translated src=- shape=17a27f02 vocab=4ba95ad2
-/
theorem flattenIndex_lookup {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) :
    flattenIndex length (lookupCluster length j) (lookupLocal length j) = j := by
  exact finSigmaFinEquiv.apply_symm_apply j

/-- Look up a natural-number operation index when it lies inside the finite
trace.  This is the nondependent entry point for APIs whose stage index is
`Nat`.-/
def operationAt? {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) (j : ℕ) :
    Option (Σ c, Fin (length c)) :=
  if h : j < totalCount length then some (lookup length ⟨j, h⟩) else none

/--
@isnad1 id=eq.0h4v.s5.b0c4c099ac2f from=translated src=- shape=3c08e8f6 vocab=cec5f056
-/
@[simp]
theorem operationAt?_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    operationAt? length (flattenIndex length c i) = some ⟨c, i⟩ := by
  simp [operationAt?, lookup]

/-- Flatten an ordinary local operation family.-/
def operationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (family : ∀ c, Fin (length c) → A)
    (j : Fin (totalCount length)) : A :=
  family (lookupCluster length j) (lookupLocal length j)

/--
@isnad1 id=eq.0h6v.s5.786712e6841a from=translated src=- shape=96c86f3d vocab=c327adde
-/
@[simp]
theorem operationFamily_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (family : ∀ c, Fin (length c) → A)
    (c : Fin clusterCount) (i : Fin (length c)) :
    operationFamily length family (flattenIndex length c i) = family c i := by
  unfold operationFamily
  change family (lookup length (flattenIndex length c i)).1
      (lookup length (flattenIndex length c i)).2 = family c i
  rw [lookup_flattenIndex]

/-- Extend an ordinary flattened operation family to all natural indices by
an explicit fallback value after the finite trace.-/
def natOperationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (fallback : A) (family : ∀ c, Fin (length c) → A)
    (j : ℕ) : A :=
  if h : j < totalCount length then operationFamily length family ⟨j, h⟩
  else fallback

/--
@isnad1 id=eq.0h7v.s5.54ff08aad652 from=translated src=- shape=2c1a0933 vocab=207eca70
-/
@[simp]
theorem natOperationFamily_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (fallback : A) (family : ∀ c, Fin (length c) → A)
    (c : Fin clusterCount) (i : Fin (length c)) :
    natOperationFamily length fallback family (flattenIndex length c i) =
      family c i := by
  simp [natOperationFamily]

/-- The value of a global index is its cluster offset plus its local index.
@isnad1 id=eq.0h4v.s5.70d040ba023b from=translated src=- shape=ce87d3c2 vocab=8e7893f1
-/
theorem flattenIndex_val {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    (flattenIndex length c i : ℕ) =
      prefixOffset length c.castSucc + i := by
  rw [flattenIndex, finSigmaFinEquiv_apply]
  unfold prefixOffset
  congr 2

/-- A flattened local index lies in the exact half-open interval belonging
to its cluster.
@isnad1 id=and.0h4v.s5.f18564db3a96 from=translated src=- shape=79d70402 vocab=f0199032
-/
theorem flattenIndex_mem_block {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    prefixOffset length c.castSucc ≤ (flattenIndex length c i : ℕ) ∧
      (flattenIndex length c i : ℕ) < prefixOffset length c.succ := by
  rw [flattenIndex_val, prefixOffset_succ]
  omega

/-- The end offset of a positive-length block does not exceed the total.
@isnad1 id=le.1h3v.s5.86288d2f424b from=translated src=- shape=1a5c32c6 vocab=2cd5cf99
-/
theorem prefixOffset_succ_le_total {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (c : Fin clusterCount) :
    prefixOffset length c.succ ≤ totalCount length := by
  let i : Fin (length c) := ⟨length c - 1, by
    have := hpositive c
    omega⟩
  have hi := (flattenIndex length c i).isLt
  rw [flattenIndex_val] at hi
  rw [prefixOffset_succ]
  dsimp [i] at hi
  omega

/-- Every boundary offset of positive-length blocks is at most the total.
@isnad1 id=le.1h3v.s5.0bc050e8205a from=translated src=- shape=b54eda6a vocab=ab6cc9c3
-/
theorem prefixOffset_le_total {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (boundary : Fin (clusterCount + 1)) :
    prefixOffset length boundary ≤ totalCount length := by
  refine Fin.cases ?_ (fun c ↦ ?_) boundary
  · simp
  · exact prefixOffset_succ_le_total length hpositive c

/-! ## Global boundaries and Nat-indexed dependent families -/

/-- Insert a local boundary into the global boundary sequence.-/
def boundaryIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c + 1)) :
    Fin (totalCount length + 1) :=
  ⟨prefixOffset length c.castSucc + i, by
    have hfinish := prefixOffset_succ_le_total length hpositive c
    rw [prefixOffset_succ] at hfinish
    omega⟩

/--
@isnad1 id=eq.1h4v.s6.054dc593837e from=translated src=- shape=cbf5da8b vocab=4b828672
-/
@[simp]
theorem boundaryIndex_val {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c + 1)) :
    (boundaryIndex length hpositive c i : ℕ) =
      prefixOffset length c.castSucc + i := rfl

/-- The boundary after a local operation is the successor of that operation's
global index.
@isnad1 id=eq.1h4v.s6.4eea93d99575 from=translated src=- shape=9ab8591a vocab=6bc47514
-/
theorem boundaryIndex_succ {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c)) :
    boundaryIndex length hpositive c i.succ =
      (flattenIndex length c i).succ := by
  apply Fin.ext
  change prefixOffset length c.castSucc + (i.val + 1) =
    (flattenIndex length c i : ℕ) + 1
  rw [flattenIndex_val]
  omega

/-- Adjacent clusters assign their shared local boundaries the same global
boundary index.
@isnad1 id=eq.2h4v.s6.610bb9ca6a78 from=translated src=- shape=7f4e2e41 vocab=24384629
-/
theorem boundaryIndex_terminal_eq_initial {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    {c next : Fin clusterCount} (hnext : next.val = c.val + 1) :
    boundaryIndex length hpositive c (Fin.last (length c)) =
      boundaryIndex length hpositive next 0 := by
  apply Fin.ext
  simp only [boundaryIndex_val, Fin.val_last, Fin.val_zero, add_zero]
  rw [← prefixOffset_succ]
  congr 1
  apply Fin.ext
  exact hnext.symm

/-- The first local boundary is the first global boundary.
@isnad1 id=eq.2h2v.s7.e532aa82b8c3 from=translated src=- shape=2d81055f vocab=5bbc5c84
-/
theorem boundaryIndex_first {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    boundaryIndex length hpositive ⟨0, hcount⟩ 0 = 0 := by
  apply Fin.ext
  simp [boundaryIndex, prefixOffset]

/-- The index of the last cluster of a nonempty finite cluster family.-/
def lastClusterIndex {clusterCount : ℕ}
    (hcount : 0 < clusterCount) : Fin clusterCount :=
  ⟨clusterCount - 1, by omega⟩

/--
@isnad1 id=eq.1h1v.s5.84c928c3bc02 from=translated src=- shape=3a23b35f vocab=8d044d38
-/
@[simp]
theorem lastClusterIndex_val {clusterCount : ℕ}
    (hcount : 0 < clusterCount) :
    (lastClusterIndex hcount : ℕ) = clusterCount - 1 := rfl

/--
@isnad1 id=eq.1h1v.s5.50ee2927563f from=translated src=- shape=c0392faf vocab=23f5728e
-/
theorem lastClusterIndex_succ {clusterCount : ℕ}
    (hcount : 0 < clusterCount) :
    (lastClusterIndex hcount).succ = Fin.last clusterCount := by
  apply Fin.ext
  simp [lastClusterIndex]
  omega

/-- The last local boundary of the last cluster is the terminal global
boundary.
@isnad1 id=eq.2h2v.s6.e6719a22c558 from=translated src=- shape=05b824bc vocab=b8a3e657
-/
theorem boundaryIndex_last {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    boundaryIndex length hpositive (lastClusterIndex hcount)
        (Fin.last (length (lastClusterIndex hcount))) =
      Fin.last (totalCount length) := by
  apply Fin.ext
  change prefixOffset length (lastClusterIndex hcount).castSucc +
      length (lastClusterIndex hcount) = totalCount length
  rw [← prefixOffset_succ, lastClusterIndex_succ, prefixOffset_last]

/-- Clamp a natural stage to the terminal boundary.  This extends a finite
boundary family to the all-natural-number indexing used by trace APIs.-/
def clampBoundary (total j : ℕ) : Fin (total + 1) :=
  ⟨min j total, by omega⟩

/--
@isnad1 id=eq.1h2v.s5.680695dbbbd7 from=translated src=- shape=0553190f vocab=807e09e6
-/
@[simp]
theorem clampBoundary_of_le {total j : ℕ} (h : j ≤ total) :
    clampBoundary total j = ⟨j, Nat.lt_succ_of_le h⟩ := by
  apply Fin.ext
  simp [clampBoundary, h]

/-- Flatten a dependent family of local operation sorts.-/
def dependentOperationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (family : ∀ c, Fin (length c) → Sort u)
    (j : Fin (totalCount length)) : Sort u :=
  family (lookupCluster length j) (lookupLocal length j)

/-- Extend a flattened dependent operation family to `ℕ` with an explicit
fallback sort outside the finite trace.-/
def natDependentOperationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (fallback : Sort u) (family : ∀ c, Fin (length c) → Sort u)
    (j : ℕ) : Sort u :=
  if h : j < totalCount length then
    dependentOperationFamily length family ⟨j, h⟩
  else fallback

/-- At every genuine global operation, the Nat-indexed dependent extension
reduces to the original local family.
@isnad1 id=eq.0h6v.s5.359bb97df516 from=translated src=- shape=eada1eb7 vocab=11cdf516
-/
@[simp]
theorem natDependentOperationFamily_flattenIndex
    {clusterCount : ℕ} (length : Fin clusterCount → ℕ)
    (fallback : Sort u) (family : ∀ c, Fin (length c) → Sort u)
    (c : Fin clusterCount) (i : Fin (length c)) :
    natDependentOperationFamily length fallback family
        (flattenIndex length c i) = family c i := by
  unfold natDependentOperationFamily
  simp only [Fin.isLt, ↓reduceDIte]
  unfold dependentOperationFamily
  change family (lookup length (flattenIndex length c i)).1
      (lookup length (flattenIndex length c i)).2 = family c i
  rw [lookup_flattenIndex]

/-! ## Concatenating compatible boundary families -/

/-- Local boundary families with explicit identifications at cluster seams.

Taking `A := Type u` makes the fields literal type equalities.  Data living
in those types can then be moved with the explicit transport function below;
no equality between unrelated local types is inferred by the combinator.-/
structure CompatibleBoundaryFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) (A : Type*) where
  initial : A
  boundary : ∀ c, Fin (length c + 1) → A
  initial_eq_first : ∀ h : 0 < clusterCount,
    initial = boundary ⟨0, h⟩ 0
  terminal_eq_next : ∀ {c next : Fin clusterCount},
    next.val = c.val + 1 →
      boundary c (Fin.last (length c)) = boundary next 0

/-- Concatenate compatible local boundary families.  A positive global
boundary is represented by the output boundary of its preceding operation.-/
def CompatibleBoundaryFamily.concatenate
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    Fin (totalCount length + 1) → A :=
  Fin.cases family.initial fun j ↦
    family.boundary (lookupCluster length j) (lookupLocal length j).succ

/--
@isnad1 id=eq.0h4v.s5.4b120f729f8f from=translated src=- shape=88e79d53 vocab=de2ca10c
-/
@[simp]
theorem CompatibleBoundaryFamily.concatenate_zero
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    family.concatenate 0 = family.initial := rfl

/-- Concatenation preserves every positive local boundary literally.
@isnad1 id=eq.1h6v.s6.79f26f23f5bb from=translated src=- shape=fe9483f9 vocab=ba22e35b
-/
theorem CompatibleBoundaryFamily.concatenate_boundaryIndex_succ
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c)) :
    family.concatenate (boundaryIndex length hpositive c i.succ) =
      family.boundary c i.succ := by
  rw [boundaryIndex_succ]
  change family.boundary (lookup length (flattenIndex length c i)).1
      (lookup length (flattenIndex length c i)).2.succ =
    family.boundary c i.succ
  rw [lookup_flattenIndex]

/-- Concatenation preserves the terminal boundary of every positive-length
cluster.
@isnad1 id=eq.1h5v.s5.4daf81430ca3 from=translated src=- shape=f641e395 vocab=a945010d
-/
theorem CompatibleBoundaryFamily.concatenate_boundaryIndex_terminal
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c) (c : Fin clusterCount) :
    family.concatenate
        (boundaryIndex length hpositive c (Fin.last (length c))) =
      family.boundary c (Fin.last (length c)) := by
  let i : Fin (length c) := ⟨length c - 1, by
    have := hpositive c
    omega⟩
  have hi : i.succ = Fin.last (length c) := by
    apply Fin.ext
    have hc := hpositive c
    simp [i]
    omega
  rw [← hi, family.concatenate_boundaryIndex_succ]

/-- At a cluster seam, the concatenated boundary is the next cluster's
explicitly identified initial boundary.
@isnad1 id=eq.2h6v.s6.2ee0447f1abf from=translated src=- shape=d93b5189 vocab=b32e1175
-/
theorem CompatibleBoundaryFamily.concatenate_seam
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c)
    {c next : Fin clusterCount} (hnext : next.val = c.val + 1) :
    family.concatenate
        (boundaryIndex length hpositive c (Fin.last (length c))) =
      family.boundary next 0 := by
  rw [family.concatenate_boundaryIndex_terminal]
  exact family.terminal_eq_next hnext

/-- Concatenation preserves the first local boundary through the supplied
initial identification.
@isnad1 id=eq.2h4v.s7.3dae3e773f45 from=translated src=- shape=919bdd97 vocab=ea587923
-/
theorem CompatibleBoundaryFamily.concatenate_first
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    family.concatenate
        (boundaryIndex length hpositive ⟨0, hcount⟩ 0) =
      family.boundary ⟨0, hcount⟩ 0 := by
  rw [boundaryIndex_first, family.concatenate_zero,
    family.initial_eq_first hcount]

/-- Concatenation preserves the last local boundary at the global endpoint.
@isnad1 id=eq.2h4v.s6.1dada7d49a42 from=translated src=- shape=49008456 vocab=86f927a9
-/
theorem CompatibleBoundaryFamily.concatenate_last
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    family.concatenate (Fin.last (totalCount length)) =
      family.boundary (lastClusterIndex hcount)
        (Fin.last (length (lastClusterIndex hcount))) := by
  rw [← boundaryIndex_last length hpositive hcount]
  exact family.concatenate_boundaryIndex_terminal hpositive _

/-- The Nat-indexed boundary family obtained by clamping after the finite
terminal stage.-/
def CompatibleBoundaryFamily.natFamily
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) (j : ℕ) : A :=
  family.concatenate (clampBoundary (totalCount length) j)

/--
@isnad1 id=eq.0h4v.s4.56995672d5d2 from=translated src=- shape=2f0f425d vocab=f48bd0a4
-/
@[simp]
theorem CompatibleBoundaryFamily.natFamily_zero
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    family.natFamily 0 = family.initial := by
  simp [CompatibleBoundaryFamily.natFamily, clampBoundary]

/--
@isnad1 id=eq.0h4v.s5.fadc35b9f06f from=translated src=- shape=1f1a2d0c vocab=f138169c
-/
@[simp]
theorem CompatibleBoundaryFamily.natFamily_total
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    family.natFamily (totalCount length) =
      family.concatenate (Fin.last (totalCount length)) := by
  unfold CompatibleBoundaryFamily.natFamily
  congr 1
  apply Fin.ext
  simp [clampBoundary]

/-- At the successor of a flattened operation, the Nat-indexed family is
the corresponding local output boundary.
@isnad1 id=eq.1h6v.s6.f3e304d742d3 from=translated src=- shape=10206bfe vocab=ec0d53b2
-/
theorem CompatibleBoundaryFamily.natFamily_succ_flattenIndex
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c)) :
    family.natFamily ((flattenIndex length c i : ℕ) + 1) =
      family.boundary c i.succ := by
  unfold CompatibleBoundaryFamily.natFamily
  have hle : (flattenIndex length c i : ℕ) + 1 ≤ totalCount length :=
    (flattenIndex length c i).isLt
  rw [clampBoundary_of_le hle]
  change family.concatenate (flattenIndex length c i).succ = _
  rw [← boundaryIndex_succ length hpositive]
  exact family.concatenate_boundaryIndex_succ hpositive c i

/-- Explicitly transport dependent data from a local output boundary to the
corresponding Nat-indexed global boundary.-/
def CompatibleBoundaryFamily.transportAfter
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ}
    (family : CompatibleBoundaryFamily length (Type u))
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c))
    (x : family.boundary c i.succ) :
    family.natFamily ((flattenIndex length c i : ℕ) + 1) :=
  Eq.mp (family.natFamily_succ_flattenIndex hpositive c i).symm x

/-! ## Ordered-cluster transfer phases -/

/-- The three kinds of transfer operation belonging to one ordered cluster.-/
inductive ClusterTransferOperation
    (individualCount extraRetainedCount : ℕ) where
  | individual : Fin individualCount →
      ClusterTransferOperation individualCount extraRetainedCount
  | firstSimultaneous :
      ClusterTransferOperation individualCount extraRetainedCount
  | extraRetained : Fin extraRetainedCount →
      ClusterTransferOperation individualCount extraRetainedCount

/-- Split a cluster transfer operation into its three finite summands.-/
def clusterTransferOperationSumEquiv
    (individualCount extraRetainedCount : ℕ) :
    ClusterTransferOperation individualCount extraRetainedCount ≃
      Fin individualCount ⊕ (Fin 1 ⊕ Fin extraRetainedCount) where
  toFun
    | .individual i => Sum.inl i
    | .firstSimultaneous => Sum.inr (Sum.inl 0)
    | .extraRetained i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl i => .individual i
    | Sum.inr (Sum.inl _) => .firstSimultaneous
    | Sum.inr (Sum.inr i) => .extraRetained i
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with i | i
    · rfl
    · rcases i with i | i
      · rcases i with ⟨i, hi⟩
        have : i = 0 := by omega
        subst i
        rfl
      · rfl

/-- Chronological local numbering: individual operations, the first
simultaneous operation, then the extra retained operations.-/
def clusterTransferOperationFinEquiv
    (individualCount extraRetainedCount : ℕ) :
    ClusterTransferOperation individualCount extraRetainedCount ≃
      Fin (individualCount + 1 + extraRetainedCount) :=
  (clusterTransferOperationSumEquiv individualCount extraRetainedCount).trans
    ((Equiv.sumCongr (Equiv.refl (Fin individualCount)) finSumFinEquiv).trans
      (finSumFinEquiv.trans
        (finCongr (Nat.add_assoc individualCount 1 extraRetainedCount).symm)))

/--
@isnad1 id=eq.0h3v.s7.c4225ad34ce9 from=translated src=- shape=2b2667ca vocab=d305beb5
-/
@[simp]
theorem clusterTransferOperationFinEquiv_individual
    {individualCount extraRetainedCount : ℕ} (i : Fin individualCount) :
    (clusterTransferOperationFinEquiv individualCount extraRetainedCount
        (.individual i) : ℕ) = i := by
  simp [clusterTransferOperationFinEquiv, clusterTransferOperationSumEquiv,
    finSumFinEquiv_apply_left]

/--
@isnad1 id=eq.0h2v.s7.cd96b7255230 from=translated src=- shape=2bfe40d8 vocab=af51ed92
-/
@[simp]
theorem clusterTransferOperationFinEquiv_firstSimultaneous
    (individualCount extraRetainedCount : ℕ) :
    (clusterTransferOperationFinEquiv individualCount extraRetainedCount
        .firstSimultaneous : ℕ) = individualCount := by
  simp [clusterTransferOperationFinEquiv, clusterTransferOperationSumEquiv,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/--
@isnad1 id=eq.0h3v.s7.77a9369b35b6 from=translated src=- shape=270f03ef vocab=a1c8e309
-/
@[simp]
theorem clusterTransferOperationFinEquiv_extraRetained
    {individualCount extraRetainedCount : ℕ} (i : Fin extraRetainedCount) :
    (clusterTransferOperationFinEquiv individualCount extraRetainedCount
        (.extraRetained i) : ℕ) = individualCount + 1 + i := by
  simp [clusterTransferOperationFinEquiv, clusterTransferOperationSumEquiv,
    finSumFinEquiv_apply_right]
  omega

/-- The operation count of one cluster's three transfer phases.-/
abbrev clusterTransferLength {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) : ℕ :=
  individualCount c + 1 + extraRetainedCount c

/--
@isnad1 id=lt.0h4v.s4.ddb2c86fff98 from=translated src=- shape=3bbf331b vocab=79e6edfb
-/
theorem clusterTransferLength_pos {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) :
    0 < clusterTransferLength individualCount extraRetainedCount c := by
  unfold clusterTransferLength
  omega

/-- The total number of transfer operations in all ordered clusters.-/
abbrev totalClusterTransferCount {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ) : ℕ :=
  totalCount (clusterTransferLength individualCount extraRetainedCount)

/-- Enumerate all three-phase operations across all ordered clusters.-/
def orderedClusterTransferEquiv {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ) :
    Fin (totalClusterTransferCount individualCount extraRetainedCount) ≃
      Σ c, ClusterTransferOperation
        (individualCount c) (extraRetainedCount c) :=
  (flattenEquiv
      (clusterTransferLength individualCount extraRetainedCount)).trans
    (Equiv.sigmaCongrRight fun c ↦
      (clusterTransferOperationFinEquiv
        (individualCount c) (extraRetainedCount c)).symm)

/-- Insert a named local transfer operation into the global trace.-/
def clusterTransferIndex {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount)
    (operation : ClusterTransferOperation
      (individualCount c) (extraRetainedCount c)) :
    Fin (totalClusterTransferCount individualCount extraRetainedCount) :=
  flattenIndex (clusterTransferLength individualCount extraRetainedCount) c
    (clusterTransferOperationFinEquiv
      (individualCount c) (extraRetainedCount c) operation)

/--
@isnad1 id=eq.0h5v.s7.c03a171ab9a3 from=translated src=- shape=8c94d08f vocab=9c7f1d8b
-/
@[simp]
theorem orderedClusterTransferEquiv_clusterTransferIndex
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount)
    (operation : ClusterTransferOperation
      (individualCount c) (extraRetainedCount c)) :
    orderedClusterTransferEquiv individualCount extraRetainedCount
        (clusterTransferIndex individualCount extraRetainedCount c operation) =
      ⟨c, operation⟩ := by
  unfold orderedClusterTransferEquiv clusterTransferIndex
  rw [Equiv.trans_apply, flattenEquiv_flattenIndex]
  change (⟨c, (clusterTransferOperationFinEquiv
        (individualCount c) (extraRetainedCount c)).symm
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c) operation)⟩ :
      Σ c, ClusterTransferOperation
        (individualCount c) (extraRetainedCount c)) =
    (⟨c, operation⟩ : Σ c, ClusterTransferOperation
      (individualCount c) (extraRetainedCount c))
  rw [Equiv.symm_apply_apply]

/--
@isnad1 id=eq.0h5v.s5.9bb87ee2c3f4 from=translated src=- shape=a918e3de vocab=0bfef494
-/
@[simp]
theorem clusterTransferIndex_individual_val
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (individualCount c)) :
    (clusterTransferIndex individualCount extraRetainedCount c
        (.individual i) : ℕ) =
      prefixOffset
          (clusterTransferLength individualCount extraRetainedCount)
          c.castSucc + i := by
  calc
    (clusterTransferIndex individualCount extraRetainedCount c
        (.individual i) : ℕ) =
        prefixOffset
            (clusterTransferLength individualCount extraRetainedCount)
            c.castSucc +
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c)
            (.individual i) : ℕ) := by
      exact flattenIndex_val
        (clusterTransferLength individualCount extraRetainedCount) c _
    _ = _ := by simp

/--
@isnad1 id=eq.0h4v.s5.6db48ceb5b7c from=translated src=- shape=8ebf287d vocab=f9419464
-/
@[simp]
theorem clusterTransferIndex_firstSimultaneous_val
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) :
    (clusterTransferIndex individualCount extraRetainedCount c
        .firstSimultaneous : ℕ) =
      prefixOffset
          (clusterTransferLength individualCount extraRetainedCount)
          c.castSucc + individualCount c := by
  calc
    (clusterTransferIndex individualCount extraRetainedCount c
        .firstSimultaneous : ℕ) =
        prefixOffset
            (clusterTransferLength individualCount extraRetainedCount)
            c.castSucc +
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c)
            .firstSimultaneous : ℕ) := by
      exact flattenIndex_val
        (clusterTransferLength individualCount extraRetainedCount) c _
    _ = _ := by simp

/--
@isnad1 id=eq.0h5v.s6.09444fb05c41 from=translated src=- shape=27f6df0c vocab=88517d94
-/
@[simp]
theorem clusterTransferIndex_extraRetained_val
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (extraRetainedCount c)) :
    (clusterTransferIndex individualCount extraRetainedCount c
        (.extraRetained i) : ℕ) =
      prefixOffset
          (clusterTransferLength individualCount extraRetainedCount)
          c.castSucc + individualCount c + 1 + i := by
  calc
    (clusterTransferIndex individualCount extraRetainedCount c
        (.extraRetained i) : ℕ) =
        prefixOffset
            (clusterTransferLength individualCount extraRetainedCount)
            c.castSucc +
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c)
            (.extraRetained i) : ℕ) := by
      exact flattenIndex_val
        (clusterTransferLength individualCount extraRetainedCount) c _
    _ = _ := by
      simp
      omega

/-- Total transfer count when the individual phases are actual operation
lists rather than bare lengths.-/
def totalClusterTransferCountOfLists
    {clusterCount : ℕ} {Block : Fin clusterCount → Type u}
    (individualSteps : ∀ c, List (Block c))
    (extraRetainedCount : Fin clusterCount → ℕ) : ℕ :=
  totalClusterTransferCount (fun c ↦ (individualSteps c).length)
    extraRetainedCount

/-- Enumerate variable-length individual operation lists together with the
first simultaneous and extra retained operations of every cluster.-/
def orderedClusterTransferEquivOfLists
    {clusterCount : ℕ} {Block : Fin clusterCount → Type u}
    (individualSteps : ∀ c, List (Block c))
    (extraRetainedCount : Fin clusterCount → ℕ) :
    Fin (totalClusterTransferCountOfLists
      individualSteps extraRetainedCount) ≃
      Σ c, ClusterTransferOperation
        (individualSteps c).length (extraRetainedCount c) :=
  orderedClusterTransferEquiv (fun c ↦ (individualSteps c).length)
    extraRetainedCount

/-- Read the selected block stored at an individual-operation index.-/
def individualStepAt
    {clusterCount : ℕ} {Block : Fin clusterCount → Type u}
    (individualSteps : ∀ c, List (Block c)) (c : Fin clusterCount)
    (i : Fin (individualSteps c).length) : Block c :=
  (individualSteps c).get i

end FiniteFamilyFlattening
end AbelFormalization
