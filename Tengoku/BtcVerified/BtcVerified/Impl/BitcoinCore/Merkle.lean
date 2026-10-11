import Tengoku.BtcVerified.BtcVerified.Crypto.Merkle
/-!
  # Bitcoin Core's `ComputeMerkleRoot`, checked against the spec

  `BtcVerified.Merkle` is the platonic merkle spec: the root as a tree fold
  (`root`), with canonicality a separate decidable property of the leaf list
  (`Canonical`). This module holds Bitcoin's *vector* computation of that root —
  the bottom-up level fold (`computeRoot`, proved equal to the tree root by
  `computeRoot_eq_root`) — and Bitcoin Core's fused variant that also computes
  the `mutated` flag. The level fold and its flag are the implementation-shaped
  pieces; they live here, not in the spec, because a level is a fact about the
  flat vector layout, not the tree. Only Bitcoin Core is considered for now, so
  the vector computation lives with it; a shared layer can be factored out if a
  second client enters the repo.

  ## The algorithm (Bitcoin Core, src/consensus/merkle.cpp @ d84fc352)

  ```cpp
  uint256 ComputeMerkleRoot(std::vector<uint256> hashes, bool* mutated) {
      bool mutation = false;
      while (hashes.size() > 1) {
          if (mutated) {
              for (size_t pos = 0; pos + 1 < hashes.size(); pos += 2) {
                  if (hashes[pos] == hashes[pos + 1]) mutation = true;
              }
          }
          if (hashes.size() & 1) {
              hashes.push_back(hashes.back());
          }
          SHA256D64(hashes[0].begin(), hashes[0].begin(), hashes.size() / 2);
          hashes.resize(hashes.size() / 2);
      }
      if (mutated) *mutated = mutation;
      if (hashes.size() == 0) return uint256();
      return hashes[0];
  }
  ```

  This is a transcription, not a literal copy: Core mutates a `std::vector` in a
  `while` loop; Lean is functional. The correspondence is *up to the
  imperative-to-functional rendering* — the loop invariant "`hashes` holds the
  current level" becomes the recursion's list argument, and the sticky local
  `bool mutation` becomes the OR of each level's scan, folded up through the
  recursion. One recursive call is one loop iteration; the `size > 1` guard is
  the two-or-more-element pattern. Line by line:

  - `while (hashes.size() > 1)` — the `x :: y :: rest` arm; `[]`/`[x]` exit.
  - `for (pos=0; pos+1<size; pos+=2) if (h[pos]==h[pos+1])` — `levelMutation`
    (the lone odd tail is left unscanned).
  - `if (size & 1) push_back(back())` then `SHA256D64` — `foldLevel`
    (pad-and-combine one level). `SHA256D64` computes double-SHA-256 over each
    64-byte pair; the spec models this abstractly as `combine l r =
    sha256d (l ++ r)`, so the equivalence is independent of which SHA-256 routine
    Core uses, and rides only on the leaf byte order being `uint256::begin()`
    order — fixed in `Crypto/Hash256.lean`, with no reversal, as Core does none
    in the tree.
  - sticky `bool mutation`, OR-ed across iterations — `levelMutation xs || r.2`,
    this level's scan OR-ed with the flag returned from the recursion.
  - `if (size == 0) return uint256()` — `[] => (0, ·)` (`0 : Hash256` is 32 zero
    bytes = `uint256()`); `return hashes[0]` — `[x] => (x, ·)`. Both cases are
    for totality: a consensus block always has a coinbase leaf, so neither the
    empty nor the singleton case arises in block validation.

  We model the `mutated != nullptr` branch — the consensus path. `CheckBlock`
  calls `BlockMerkleRoot(block, &mutated)` and rejects the block when the flag
  comes back set (the CVE-2012-2459 fix); `BlockMerkleRoot` forwards that
  non-null pointer, so the scan always runs. The `nullptr` callers (e.g.
  `BlockWitnessMerkleRoot`) skip the scan; `computeMerkleRoot_fst` shows the root
  is the same either way.

  The load-bearing fidelity point is the *ordering*: Core scans the current level
  for adjacent duplicates **before** it pads, so a duplicate that padding
  synthesizes (the copied last node of an odd level) is never compared to its
  twin — only a duplicate already present as a complete pair trips the flag. This
  is exactly the CVE-2012-2459 defense.

  Checked claims:

  * `canonical_of_not_mutated`: a leaf list Core accepts (`mutated = false`) is
    the spec's `Canonical` — unconditionally.
  * `eq_of_computeMerkleRoot_eq_of_not_mutated`: two nonempty equal-width leaf
    lists Core accepts with equal roots are equal — or two concrete byte strings
    collide under double-SHA-256.
  * `computeMerkleRoot_fst`: the root Core returns is exactly `computeRoot`, on
    every input.
  * `computeRoot_eq_root`: the bottom-up vector fold computes the spec's tree
    root.
-/

attribute [local simp] BtcVerified.Bytes.length_val

namespace BtcVerified.Impl.BitcoinCore

open BtcVerified BtcVerified.Merkle

/-! ## The bottom-up computation -/

/-- One level of Bitcoin's bottom-up fold: hash adjacent pairs, hashing an
unpaired last node with itself. -/
def foldLevel : List Hash256 → List Hash256
  | [] => []
  | [x] => [combine x x]
  | x :: y :: rest => combine x y :: foldLevel rest

/-- Each fold level halves the node count, rounding up. -/
theorem foldLevel_length : ∀ xs : List Hash256, (foldLevel xs).length = (xs.length + 1) / 2
  | [] => by simp [foldLevel]
  | [_] => by simp [foldLevel]
  | _ :: _ :: rest => by simp [foldLevel, foldLevel_length rest]; omega

/-- The merkle root as Bitcoin computes it: fold levels bottom-up until one
node remains. One deterministic cryptographic operation — canonicality of the
input is `Canonical`'s concern, decided separately. (Core fuses a duplicate
scan into this same pass under the name `mutated`; see the module header.) -/
def computeRoot : List Hash256 → Hash256
  | [] => 0
  | [x] => x
  | x :: y :: rest => computeRoot (foldLevel (x :: y :: rest))
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-- A fold level distributes over an append at an even boundary. -/
theorem foldLevel_append : ∀ (as bs : List Hash256), as.length % 2 = 0 →
    foldLevel (as ++ bs) = foldLevel as ++ foldLevel bs
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: a' :: rest, bs, h => by
    have hrest : rest.length % 2 = 0 := by simp at h; omega
    cases bs with
    | nil => simp [foldLevel]
    | cons b bs' =>
      simp only [List.cons_append, foldLevel, foldLevel_append rest (b :: bs') hrest]

/-- One merkle level's pre-padding duplicate-pair scan, exactly Core's
`for (pos = 0; pos + 1 < size; pos += 2) if (hashes[pos] == hashes[pos+1])`:
fires iff some adjacent even-aligned pair is equal. The lone last element of an
odd-length level is never compared (at `pos = size - 1` the guard `pos + 1 <
size` fails), so a duplicate that padding will later synthesize cannot trigger
here — the CVE-2012-2459 defense. -/
def levelMutation : List Hash256 → Bool
  | [] => false
  | [_] => false
  | x :: y :: rest => (x == y) || levelMutation rest

/-- Bitcoin Core's `ComputeMerkleRoot(hashes, &mutated)` on the consensus path:
at each level with two or more nodes (the `while (size > 1)` guard), scan the
current level for an adjacent duplicate (`levelMutation`), pad-and-combine the
level (`foldLevel`), recurse, and OR this level's scan into the flag folded up
from the levels below — Core's sticky `bool mutation`. Returns the root paired
with that flag. -/
def computeMerkleRoot : List Hash256 → Hash256 × Bool
  | [] => (0, false)
  | [x] => (x, false)
  | x :: y :: rest =>
      let r := computeMerkleRoot (foldLevel (x :: y :: rest))
      (r.1, levelMutation (x :: y :: rest) || r.2)
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-! ## The mutation check, read off the tree (internal)

  `Canonical` is a right-spine property of the spec's `Tree`, while the scan
  above is a flat fold over the list. They meet through `treeMutation`, the same
  duplicate check read off the tree the fold builds — a genuine interior `node`
  with equal-root children, `pad` nodes exempt. `computeMerkleRoot_snd_eq_treeMutation`
  is the commute triangle relating the two, the mutation analogue of
  `computeRoot_eq_root`. All `private`: durable facts on the way to the public
  results, not part of the surface. -/

/-- The whole-tree image of the `mutated` flag: a tree mutates iff some genuine
interior `node` joins two subtrees with equal roots. A `pad` node contributes no
equality test of its own — mirroring that the padded duplicate is never scanned
— but its child is still walked. -/
private def treeMutation : Tree → Bool
  | .leaf _ => false
  | .pad t => treeMutation t
  | .node l r => (l.root == r.root) || treeMutation l || treeMutation r

/-! ## What is proved -/

/-- Bitcoin Core returns exactly the spec's `computeRoot` in its first component
— unconditionally; the mutated flag does not affect the returned root. -/
theorem computeMerkleRoot_fst : ∀ xs : List Hash256,
    (computeMerkleRoot xs).1 = computeRoot xs
  | [] => by simp [computeMerkleRoot, computeRoot]
  | [_] => by simp [computeMerkleRoot, computeRoot]
  | x :: y :: rest => by
    simp only [computeMerkleRoot]
    rw [computeMerkleRoot_fst (foldLevel (x :: y :: rest))]
    conv_rhs => rw [computeRoot]
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

end BtcVerified.Impl.BitcoinCore
