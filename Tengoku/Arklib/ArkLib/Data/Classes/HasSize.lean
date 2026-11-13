/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Tengoku.Seed.Logic.Embedding.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  # `HasSize` class
-/

@[expose] public section
namespace Tengoku.Arklib end Tengoku.Arklib open Tengoku.Arklib 
/-- Type class for types that has an injective mapping to a vector of a given length `size` of
  another type (often `UInt8`).-/
class _root_.Tengoku.Arklib.HasSize (α : Type*) (β : Type*) where
  size : Nat
  toFun : α ↪ Vector β size
-- Tengoku: root names of this library moved to Tengoku.Arklib so they do not collide with other libraries (generated)
