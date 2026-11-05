/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates on roots of unity

Primitive roots identify additive residue classes with roots of unity. These
coordinates respect reduction and the actual cyclotomic Galois action.
-/

namespace KummerTheory
universe u
variable {Ω : Type u} [Field Ω]

/-- The root of unity represented by a residue class through the chosen primitive root.-/
noncomputable def primitiveRootCoordinate {n : ℕ} {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) : Ωˣ :=
  (hζ.zmodEquivZPowers a).toMul.1

/--
@isnad1 id=injectiv.1h3v.s6.9618cc935aef from=translated src=- shape=a975c902 vocab=5ea1442d
-/
theorem primitiveRootCoordinate_injective {n : ℕ} {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (primitiveRootCoordinate hζ) := by
  intro a b h
  apply hζ.zmodEquivZPowers.injective
  change (hζ.zmodEquivZPowers a).toMul = (hζ.zmodEquivZPowers b).toMul
  exact Subtype.ext h

/--
@isnad1 id=eq.1h4v.s7.cf4e3c053c19 from=translated src=- shape=e8c74e9b vocab=11df9795
-/
theorem primitiveRootCoordinate_natCast {n : ℕ} {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) (a : ℕ) :
    primitiveRootCoordinate hζ (a : ZMod n) = ζ ^ a :=
  congrArg (fun z : Additive (Subgroup.zpowers ζ) => z.toMul.1)
    (hζ.zmodEquivZPowers_apply_coe_nat a)

/--
@isnad1 id=eq.1h4v.s7.d951e3bc1ac4 from=translated src=- shape=94f71761 vocab=7e0397ae
-/
theorem primitiveRootCoordinate_eq_pow_val {n : ℕ} [NeZero n] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) :
    primitiveRootCoordinate hζ a = ζ ^ a.val := by
  calc
    primitiveRootCoordinate hζ a = primitiveRootCoordinate hζ (a.val : ZMod n) :=
      congrArg _ (ZMod.natCast_zmod_val a).symm
    _ = ζ ^ a.val := primitiveRootCoordinate_natCast hζ a.val

/--
@isnad1 id=eq.1h5v.s7.abf4a3151e4e from=translated src=- shape=0c13c9df vocab=0ac32a9b
-/
theorem primitiveRootCoordinate_add {n : ℕ} {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) (a b : ZMod n) :
    primitiveRootCoordinate hζ (a + b) =
      primitiveRootCoordinate hζ a * primitiveRootCoordinate hζ b :=
  congrArg (fun z : Additive (Subgroup.zpowers ζ) => z.toMul.1)
    (hζ.zmodEquivZPowers.map_add a b)

/--
@isnad1 id=eq.1h4v.s7.ff659149f456 from=translated src=- shape=56edffe2 vocab=3868c7b8
-/
theorem primitiveRootCoordinate_pow_eq_one {n : ℕ} {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) :
    primitiveRootCoordinate hζ a ^ n = 1 := by
  have hle : Subgroup.zpowers ζ ≤ rootsOfUnity n Ω :=
    Subgroup.zpowers_le_of_mem hζ.pow_eq_one
  exact hle (hζ.zmodEquivZPowers a).toMul.property

/--
@isnad1 id=ex.2h4v.s7.4d18227658ab from=translated src=- shape=a814af13 vocab=591a43f3
-/
theorem primitiveRootCoordinate_surjective_roots {n : ℕ} [NeZero n] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ n) (z : Ωˣ) (hz : z ^ n = 1) :
    ∃ a : ZMod n, primitiveRootCoordinate hζ a = z := by
  obtain ⟨a, _, ha⟩ := hζ.eq_pow_of_mem_rootsOfUnity (mem_rootsOfUnity n z |>.mpr hz)
  exact ⟨a, (primitiveRootCoordinate_natCast hζ a).trans ha⟩

/--
@isnad1 id=eq.2h6v.s8.1351f7e6a75c from=translated src=- shape=ebc7760f vocab=679304c0
-/
theorem primitiveRootCoordinate_reduction
    (N n m : ℕ) [NeZero N] [NeZero n] (hN : N = n * m) {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) :
    primitiveRootCoordinate hζ a ^ m =
      primitiveRootCoordinate (hζ.pow (Nat.pos_of_neZero N) (hN.trans (Nat.mul_comm n m)))
        (ZMod.castHom (by rw [hN]; exact dvd_mul_right n m) (ZMod n) a) := by
  have hcast : ZMod.castHom (by rw [hN]; exact dvd_mul_right n m) (ZMod n) a =
      (a.val : ZMod n) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [map_natCast]
  rw [hcast, primitiveRootCoordinate_eq_pow_val, primitiveRootCoordinate_natCast,
    pow_right_comm]

/--
@isnad1 id=eq.1h6v.s10.fc5b4880c869 from=translated src=- shape=9872d2ee vocab=6e90f760
-/
theorem primitiveRootCoordinate_cyclotomic
    (p : ℕ) [Fact p.Prime]
    [∀ i : ℕ, HasEnoughRootsOfUnity Ω (p ^ i)]
    (n : ℕ) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (g : Ω ≃+* Ω) (a : ZMod (p ^ n)) :
    Units.map g.toMonoidHom (primitiveRootCoordinate hζ a) =
      primitiveRootCoordinate hζ
        ((cyclotomicCharacter Ω p g : PadicInt p).toZModPow n * a) := by
  let b : ZMod (p ^ n) := (cyclotomicCharacter Ω p g : PadicInt p).toZModPow n
  have hζfield : (ζ : Ω) ^ (p ^ n) = 1 :=
    congrArg (fun x : Ωˣ => (x : Ω)) hζ.pow_eq_one
  have hgζ : Units.map g.toMonoidHom ζ = ζ ^ b.val := by
    apply Units.ext
    exact cyclotomicCharacter.spec p g (ζ : Ω) hζfield
  change Units.map g.toMonoidHom (primitiveRootCoordinate hζ a) =
    primitiveRootCoordinate hζ (b * a)
  rw [primitiveRootCoordinate_eq_pow_val hζ a, map_pow, hgζ, ← pow_mul]
  symm
  calc
    primitiveRootCoordinate hζ (b * a) =
        primitiveRootCoordinate hζ ((b.val * a.val : ℕ) : ZMod (p ^ n)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    _ = ζ ^ (b.val * a.val) := primitiveRootCoordinate_natCast hζ _

end KummerTheory
