/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RiDecomp
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxFunctor
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.ConstPuiseux

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — the commutation isomorphism `R[i]⟨⟨ε⟩⟩ ≅ R⟨⟨ε⟩⟩[i]`

For a real closed field `R` (so `Ri R = R[i]` is a field), adjoining `i` commutes with forming
Puiseux series:
> `Ri (PuiseuxSeries R) ≃+* PuiseuxSeries (Ri R)`.

The forward map `φ` is `AdjoinRoot.lift` of the coefficient inclusion `R⟨⟨ε⟩⟩ ↪ R[i]⟨⟨ε⟩⟩`
together with `i ↦ constPuiseux i`. Its inverse `ψ` splits a Puiseux series over `R[i]` into its
real and imaginary Puiseux series (`Ri.reL`/`Ri.imL` applied coefficientwise). Both compositions
collapse, coefficient by coefficient, to the `R[i]` decomposition `Ri.of_reL_add_of_imL_mul_i`. -/

namespace Azurite.BPR

open Polynomial AdjoinRoot _root_.Azurite.BPR.HahnSeries

variable {R : Type*} [Field R] [IsRealClosed R]

/-- The coefficient inclusion `R⟨⟨ε⟩⟩ ↪ R[i]⟨⟨ε⟩⟩`.-/
noncomputable def riIota : PuiseuxSeries R →+* PuiseuxSeries (Ri R) :=
  puiseuxMapRingHom (AdjoinRoot.of (X ^ 2 + 1))

/-- The image of `i` in `R[i]⟨⟨ε⟩⟩`: the constant Puiseux series `i`.-/
noncomputable def riJ : PuiseuxSeries (Ri R) := constPuiseux (Ri.i R)

/--
@isnad1 id=eq.0h1v.s16.54d927753831 from=translated src=- shape=3be07375 vocab=e1e1a64e
-/
theorem riJ_sq_add_one : (riJ (R := R)) ^ 2 + 1 = 0 := by
  rw [riJ, ← map_pow, Ri.i_sq, map_neg, map_one, neg_add_cancel]

/--
@isnad1 id=eq.0h1v.s15.1e2f391e308e from=translated src=- shape=1c78fd44 vocab=14271d48
-/
theorem riHj : (X ^ 2 + 1 : (PuiseuxSeries R)[X]).eval₂ (riIota (R := R)) riJ = 0 := by
  rw [eval₂_add, eval₂_pow, eval₂_X, eval₂_one]; exact riJ_sq_add_one

/-- **Forward map** `φ : R[i]⟨⟨ε⟩⟩ → R⟨⟨ε⟩⟩[i]`.-/
noncomputable def riPhi : Ri (PuiseuxSeries R) →+* PuiseuxSeries (Ri R) :=
  AdjoinRoot.lift riIota riJ riHj

/--
@isnad1 id=eq.0h2v.s17.f0f2e993640f from=translated src=- shape=e2acd05f vocab=7f883ea6
-/
theorem riPhi_of (a : PuiseuxSeries R) :
    riPhi (AdjoinRoot.of (X ^ 2 + 1) a) = riIota a := AdjoinRoot.lift_of riHj

/--
@isnad1 id=eq.0h1v.s15.85fd55699765 from=translated src=- shape=fb6bc504 vocab=27aa5cf2
-/
theorem riPhi_root : riPhi (Ri.i (PuiseuxSeries R)) = riJ := AdjoinRoot.lift_root riHj

/--
@isnad1 id=eq.0h2v.s15.cc9acdf26a93 from=translated src=- shape=02888ed8 vocab=fa233009
-/
theorem riIota_coe (a : PuiseuxSeries R) :
    (riIota a : PuiseuxSeries (Ri R)).1
      = HahnSeries.mapRingHom (AdjoinRoot.of (X ^ 2 + 1)) a.1 := rfl

/--
@isnad1 id=eq.0h1v.s12.22f37ce28812 from=translated src=- shape=2b39cc24 vocab=a8e33cae
-/
theorem riJ_coe : (riJ (R := R) : PuiseuxSeries (Ri R)).1 = HahnSeries.single 0 (Ri.i R) := by
  rw [riJ, coe_constPuiseux]

/-- `φ (a + b·i)` read off coefficientwise: `re`/`im` recombine via `R[i]`.
@isnad1 id=eq.0h4v.s19.49e22db2f2f5 from=translated src=- shape=3dfd3449 vocab=63a6d170
-/
theorem riPhi_lin_coe_coeff (a b : PuiseuxSeries R) (n : ℚ) :
    ((riPhi (AdjoinRoot.of (X ^ 2 + 1) a
        + AdjoinRoot.of (X ^ 2 + 1) b * Ri.i (PuiseuxSeries R)) : PuiseuxSeries (Ri R))
        : HahnSeries ℚ (Ri R)).coeff n
      = AdjoinRoot.of (X ^ 2 + 1) (a.1.coeff n)
        + AdjoinRoot.of (X ^ 2 + 1) (b.1.coeff n) * Ri.i R := by
  rw [map_add, map_mul, riPhi_of, riPhi_of, riPhi_root, Subfield.coe_add, HahnSeries.coeff_add,
    Subfield.coe_mul, riJ_coe, HahnSeries.coeff_mul_single_zero, riIota_coe, riIota_coe,
    HahnSeries.mapRingHom_coeff, HahnSeries.mapRingHom_coeff]

/-- Real part of a Puiseux series over `R[i]`.-/
noncomputable def riReP (s : PuiseuxSeries (Ri R)) : PuiseuxSeries R :=
  ⟨(s : HahnSeries ℚ (Ri R)).map Ri.reL, map_zeroHom_mem_puiseux Ri.reL s.2⟩

/-- Imaginary part of a Puiseux series over `R[i]`.-/
noncomputable def riImP (s : PuiseuxSeries (Ri R)) : PuiseuxSeries R :=
  ⟨(s : HahnSeries ℚ (Ri R)).map Ri.imL, map_zeroHom_mem_puiseux Ri.imL s.2⟩

/--
@isnad1 id=eq.0h3v.s12.aaed7fbf018c from=translated src=- shape=ffd8abf0 vocab=3920fe9e
-/
theorem riReP_coe_coeff (s : PuiseuxSeries (Ri R)) (n : ℚ) :
    (riReP s).1.coeff n = Ri.reL (s.1.coeff n) := rfl

/--
@isnad1 id=eq.0h3v.s12.72b8cc328432 from=translated src=- shape=ffd8abf0 vocab=228daec8
-/
theorem riImP_coe_coeff (s : PuiseuxSeries (Ri R)) (n : ℚ) :
    (riImP s).1.coeff n = Ri.imL (s.1.coeff n) := rfl

/-- **Inverse map** `ψ : R⟨⟨ε⟩⟩[i] → R[i]⟨⟨ε⟩⟩`.-/
noncomputable def riPsi (s : PuiseuxSeries (Ri R)) : Ri (PuiseuxSeries R) :=
  AdjoinRoot.of (X ^ 2 + 1) (riReP s)
    + AdjoinRoot.of (X ^ 2 + 1) (riImP s) * Ri.i (PuiseuxSeries R)

/--
@isnad1 id=eq.0h2v.s16.fc31eefb3e4a from=translated src=- shape=cdc30fd0 vocab=2dbdefa3
-/
theorem riPhi_psi (s : PuiseuxSeries (Ri R)) : riPhi (riPsi s) = s := by
  apply Subtype.ext
  apply HahnSeries.ext
  funext n
  rw [riPsi, riPhi_lin_coe_coeff, riReP_coe_coeff, riImP_coe_coeff,
    Ri.of_reL_add_of_imL_mul_i]

/--
@isnad1 id=eq.0h2v.s17.9c75e865645a from=translated src=- shape=eda63b50 vocab=cd12b04f
-/
theorem riReP_riPhi (z : Ri (PuiseuxSeries R)) : riReP (riPhi z) = Ri.reL z := by
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i z]
  apply Subtype.ext
  apply HahnSeries.ext
  funext n
  rw [riReP_coe_coeff, riPhi_lin_coe_coeff, Ri.reL_lin]

/--
@isnad1 id=eq.0h2v.s17.c22f13957974 from=translated src=- shape=eda63b50 vocab=977bd8b7
-/
theorem riImP_riPhi (z : Ri (PuiseuxSeries R)) : riImP (riPhi z) = Ri.imL z := by
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i z]
  apply Subtype.ext
  apply HahnSeries.ext
  funext n
  rw [riImP_coe_coeff, riPhi_lin_coe_coeff, Ri.imL_lin]

/--
@isnad1 id=eq.0h2v.s15.a15998dcfdca from=translated src=- shape=51b41f2f vocab=2dbdefa3
-/
theorem riPsi_phi (z : Ri (PuiseuxSeries R)) : riPsi (riPhi z) = z := by
  rw [riPsi, riReP_riPhi, riImP_riPhi, Ri.of_reL_add_of_imL_mul_i]

/-- **The commutation isomorphism** `R[i]⟨⟨ε⟩⟩ ≅ R⟨⟨ε⟩⟩[i]`.-/
noncomputable def riPuiseuxEquiv : Ri (PuiseuxSeries R) ≃+* PuiseuxSeries (Ri R) :=
  RingEquiv.ofBijective riPhi
    ⟨fun z z' h => by rw [← riPsi_phi z, ← riPsi_phi z', h],
      fun s => ⟨riPsi s, riPhi_psi s⟩⟩

end Azurite.BPR
