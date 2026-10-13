/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.AuxiliaryUnary.Defs
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.AuxiliaryUnary.Internal

/-!
# The auxiliary-unary distribution

This module exposes the exact sampler shape and counting theory for Hirahara's
uniform distribution with auxiliary unary input. At positive parameter `m`, a
sample is `pair x (List.replicate t true)` for uniform `t ∈ {1, ..., m}` and
uniform `x ∈ {0,1}^{m-t}`.
-/

public section

namespace Complexity

namespace AuxiliaryUnarySeed

/-- The selected binary length is strictly below every positive slice
parameter.
@isnad1 id=lt.1h2v.s4.a4d12d4fdd6f from=translated src=- shape=d85d56cc vocab=7684ac70
-/
theorem split_lt {m : ℕ} (hm : 0 < m) (seed : AuxiliaryUnarySeed m) :
    seed.split < m :=
  split_lt_internal hm seed

/-- The retained binary component has the selected length.
@isnad1 id=eq.0h2v.s3.b01adcd5ed54 from=translated src=- shape=9a3a44a2 vocab=510f99e1
-/
@[simp] theorem binary_length {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.binary.length = seed.split :=
  binary_length_internal seed

/-- The unary component fills the remainder of the size parameter.
@isnad1 id=eq.0h2v.s4.672c6ee089f0 from=translated src=- shape=ee30882d vocab=51d9fdb4
-/
@[simp] theorem unary_length {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.unary.length = m - seed.split :=
  unary_length_internal seed

/-- The auxiliary unary clock is nonempty on every positive slice.
@isnad1 id=lt.1h2v.s4.169be716717a from=translated src=- shape=2765c2f9 vocab=71fa4708
-/
theorem unary_length_pos {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.unary.length :=
  unary_length_pos_internal hm seed

/-- The two decoded component lengths sum to the slice parameter.
@isnad1 id=eq.0h2v.s4.b75889568b57 from=translated src=- shape=c6a00294 vocab=b96105fa
-/
theorem component_length_sum {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.binary.length + seed.unary.length = m :=
  component_length_sum_internal seed

/-- Decoding an auxiliary-unary sample recovers its two components exactly.
@isnad1 id=eq.0h2v.s5.c26fa8b5ff5e from=translated src=- shape=73c5ced9 vocab=faca6a31
-/
@[simp] theorem unpair?_sample {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    unpair? seed.sample = some (seed.binary, seed.unary) :=
  unpair?_sample_internal seed

/-- The `m`th seed space contains `max 1 m * 2^m` equiprobable seeds.
@isnad1 id=eq.0h1v.s6.0a4c6ae5aba4 from=translated src=- shape=979535f0 vocab=29b1ec1b
-/
theorem card (m : ℕ) :
    Fintype.card (AuxiliaryUnarySeed m) = Nat.max 1 m * 2 ^ m :=
  card_internal m

/-- A uniform `m`-bit string has any fixed length-`n` prefix with probability
exactly `2^-n`.
@isnad1 id=eq.1h3v.s8.918899ad9f23 from=translated src=- shape=75b4a15a vocab=7fdbd648
-/
theorem prefix_probability {m n : ℕ} (hn : n ≤ m)
    (x : Fin n → Bool) :
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 = x) =
      1 / (2 : ℚ) ^ n :=
  prefix_probability_internal hn x

/-- Retaining a uniform prefix preserves the exact uniform probability of
every finite event on prefixes, not only singleton events.
@isnad1 id=eq.1h3v.s8.0624751151d5 from=translated src=- shape=babaef2f vocab=23549e0a
-/
theorem prefix_event_probability {m n : ℕ} (hn : n ≤ m)
    (event : Finset (Fin n → Bool)) :
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 ∈ event) =
      eventProb event :=
  prefix_event_probability_internal hn event

/-- Choosing a split and retaining its prefix gives the uniform average of a
possibly length-dependent family of prefix-event probabilities.
@isnad1 id=eq.0h2v.s9.c8c3f0cf1365 from=translated src=- shape=8719f3f9 vocab=fcd1df9a
-/
theorem split_prefix_event_probability {m : ℕ}
    (event : ∀ n, Finset (Fin n → Bool)) :
    uniformProbability
        (Finset.univ.filter fun seed : (Fin m) × (Fin m → Bool) =>
          (bitBlocks (Nat.le_of_lt seed.1.isLt) seed.2).1 ∈
            event seed.1.val) =
      (1 / (m : ℚ)) * ∑ n : Fin m, eventProb (event n.val) :=
  split_prefix_event_probability_internal event

/-- The joint seed event selecting binary length `n` and fixed prefix `x` has
probability exactly `1 / (m * 2^n)`.
@isnad1 id=eq.1h3v.s9.979df45daeb9 from=translated src=- shape=ffb1640d vocab=dd08409b
-/
theorem split_prefix_probability {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) :
    uniformProbability
        (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
          seed.1.val = n ∧
            (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) :=
  split_prefix_probability_internal hn x

/-- A seed produces a specified canonical auxiliary-unary pair exactly when it
selects the pair's binary length and binary contents.
@isnad1 id=iff.1h4v.s7.5af6dd634518 from=translated src=- shape=adf4525f vocab=b65a4e51
-/
theorem sample_eq_pair_iff {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) (seed : AuxiliaryUnarySeed m) :
    seed.sample = pair (List.ofFn x) (List.replicate (m - n) true) ↔
      seed.1.val = n ∧
        (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x :=
  sample_eq_pair_iff_internal hn x seed

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/-- Exact mass of a fixed auxiliary-unary input. For `n < m`, every
`pair x 1^(m-n)` with `|x| = n` has probability `1 / (m * 2^n)`.
@isnad1 id=eq.1h3v.s6.9d367870d518 from=translated src=- shape=02bc9ef7 vocab=a3ff3ba4
-/
theorem mass_auxiliaryUnary_pair {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) :
    auxiliaryUnary.mass m
        (pair (List.ofFn x) (List.replicate (m - n) true)) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) :=
  mass_auxiliaryUnary_pair_internal hn x

end FiniteEnsemble

end Complexity
