/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
# Universe boundary for integral representations

Mathlib's `Rep ℤ G` currently requires the coefficient ring and acting group
to inhabit the same universe.  Since `ℤ : Type 0`, every representation-bearing
part of local class field theory uses this single named boundary.  Keeping the
restriction here makes a future universe-polymorphic migration searchable and
prevents individual subtrees from inventing private aliases.
-/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-- The universe-zero group boundary imposed by integral representations.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.IntegralRepGroupType := Type 0
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
