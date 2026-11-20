import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.MinSpecCorrespondence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Changing parallel basepoints (paper `prop:basechange`, `sec:normalization`)

Paper labels covered:

* `prop:basechange` (Changing parallel basepoints), in full:
  - the rebased normalized datum `OEData.rebase d c` with `b'_s = b_s · c` and the SAME
    right action, morphism action and transport (`reind`, `χ`); only basepoints, coordinates and
    the chosen vertical arrows change;
  - on a connected base, every parallel family `b' : S → O` (with `p(b'_s) = s`) for the
    transport of `d` is `b'_s = b_s · c` for a UNIQUE constant `c`
    (`parallel_family_eq_translate`), and it is the basepoint field of a unique `d.rebase c`
    (`parallel_family_eq_rebase_base`); for a full second normalized datum `d'` with the same
    action and transport this is `parallel_basepoints_eq_rebase`, and the whole datum is then
    `d.rebase c` (`eq_rebase_of_base`, `exists_unique_eq_rebase`);
    uniqueness alone needs only a nonempty base (`parallel_basepoints_const_unique`);
  - the coordinate formula `g'_x = c⁻¹ g_x` (`coord_eq_of_base`) and the functor formulas
    `Λ'_a = Λ_{cac⁻¹}` (`Λ_eq_of_base`), `Λ'_a = Λ_c Λ_a Λ_c⁻¹` (`Λ_eq_conj_of_base`),
    `Ã' = Ã` (`liftFunctor_eq_of_base`), `Ã'_θ = Λ_{c θ_A(c⁻¹)} Ã_θ`
    (`liftFunctorθ_eq_of_base`) and `Ã'_θ = Λ_c Ã_θ Λ_c⁻¹` (`liftFunctorθ_eq_conj_of_base`),
    all as equalities of FUNCTORS `O ⥤ O` (no connectedness needed once `b' = b · c` is given);
  - the displayed object identity `b'_{A(p x)} · θ_A(g'_x) = b_{A(p x)} · (c θ_A(c⁻¹) θ_A(g_x))`
    (`liftFunctorθ_obj_eq_of_base`).
* The group-level reading of `prop:basechange` and the paragraph after it (`sec:normalization`):
  - the canonical identifications `autBoxGCongr : AutBoxG d ≃* AutBoxG d'`, `autBoxGOverCongr`,
    `autBoxGθOverCongr`, which are the IDENTITY on `hom`, `inv` and `base` and exist because the
    lift conditions only mention the action (equivariance) and the transport (cleavage
    preservation), never basepoints or coordinates ("the group of admissible lifts and its
    projection to `H` do not refer to basepoints or coordinates");
  - the formulas for the homomorphisms `ΛHom`, `liftHom`, `ΛHomOver`, `liftHomOver`, `ΛHomθOver`,
    `liftHomθOver`, pointwise and as equalities of `MonoidHom`s, transported along these
    identifications;
  - the two semidirect identifications `autBoxGθOverMulEquivSemidirect d` and `… d'` differ by
    the inner automorphism `F ↦ Λ_c F Λ_c⁻¹` (`autBoxGθOverMulEquivSemidirect_symm_eq_of_base`),
    and likewise the untwisted product identifications (`autBoxGOverMulEquivProd_symm_eq_of_base`);
    in the untwisted case the canonical section itself is unchanged
    (`liftHom_eq_of_base`, `liftHomOver_eq_of_base`);
  - the coboundary identity `z_c(AB) = z_c(A) θ_A(z_c(B))` for `z_c(A) = c θ_A(c⁻¹)`: the
    canonical statement is `OECocycle.coboundary_mul` (module `Cocycles`); the local copy
    `baseChange_twistFactor_mul` states the same identity locally and is identified with
    `OECocycle.coboundary` by `baseChange_twistFactor_eq_coboundary`.
* The remaining sentences of that paragraph, which need `Cocycles`, are in the bridge module
  `BaseChangeCocycle`: the conjugacy class of the canonical section under the kernel of
  `ΦθOver` is independent of parallel normalization (`liftHomθOver_rebase_conj_ker`), read in
  the fixed semidirect coordinates of `d` the new section is the cocycle section of the
  coboundary `z_c` (`liftHomθOver_rebase_semidirect`), and its class in `H¹(H,G)` is the trivial
  class (`liftHomθOver_rebase_class`).

Conventions: `F ⋙ G` is "first `F`, then `G`", so the paper's operator-order `Λ_c Λ_a Λ_c⁻¹`
is `Λ d c⁻¹ ⋙ Λ d a ⋙ Λ d c` and `Λ_{cθ_A(c⁻¹)} Ã_θ` is `liftFunctorθ d A θ ⋙ Λ d (c * θ c⁻¹)`.

The hypotheses fixing the same `p`, right action and cleavage are
`hact : ∀ x g, d'.act x g = d.act x g` and
`hreind : ∀ {s t} (u : s ⟶ t) y hy, d'.reind u y hy = d.reind u y hy`; the morphism action and the
chosen arrows `χ` then agree automatically by faithfulness (see `OEData.ext_of_data`).
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-! ## 1. The rebased datum -/

namespace Tengoku.ObserverEquivarianceLean.OEData

/-- The rebased normalized datum (paper `prop:basechange`): the same right action, morphism
    action and transport (`reind`, `chi`, with all their laws) as `d`, but with the parallel
    basepoints `b'_s = b_s · c`, the coordinates `g'_x = c⁻¹ g_x`, and the vertical arrows
    `ℓ'_{a,x} = ℓ_{cac⁻¹,x}` (followed by the object identity
    `b_{p x} · (c a c⁻¹ g_x) = (b_{p x} · c) · (a · c⁻¹ g_x)`).-/
def rebase (d : OEData G p) (c : G) : OEData G p where
  act := d.act
  act_one := d.act_one
  act_mul := d.act_mul
  p_act := d.p_act
  act_free := d.act_free
  actHom := d.actHom
  actHom_id := d.actHom_id
  actHom_comp := d.actHom_comp
  actHom_one := d.actHom_one
  actHom_mul := d.actHom_mul
  p_actHom := d.p_actHom
  base s := d.act (d.base s) c
  p_base s := (d.p_act _ _).trans (d.p_base s)
  coord x := c⁻¹ * d.coord x
  base_coord x := by
    show d.act (d.act (d.base (p.obj x)) c) (c⁻¹ * d.coord x) = x
    rw [d.act_mul, mul_inv_cancel_left, d.base_coord]
  coord_base s g := by
    show c⁻¹ * d.coord (d.act (d.act (d.base s) c) g) = g
    rw [d.act_mul, d.coord_base, inv_mul_cancel_left]
  reind := d.reind
  p_reind := d.p_reind
  chi := d.chi
  p_chi := d.p_chi
  reind_base {s t} u := by
    show d.reind u (d.act (d.base t) c) ((d.p_act _ _).trans (d.p_base t)) = d.act (d.base s) c
    rw [d.reind_act u (d.base t) (d.p_base t) c, d.reind_base]
  reind_act := d.reind_act
  chi_act := d.chi_act
  ltrans a x := d.ltrans (c * a * c⁻¹) x ≫ eqToHom (by
    show d.act (d.base (p.obj x)) (c * a * c⁻¹ * d.coord x)
      = d.act (d.act (d.base (p.obj x)) c) (a * (c⁻¹ * d.coord x))
    rw [d.act_mul]
    congr 1
    group)
  p_ltrans a x := by
    rw [p.map_comp, d.p_ltrans, eqToHom_map, eqToHom_trans]
  reind_id := d.reind_id
  chi_id := d.chi_id
  reind_comp := d.reind_comp
  chi_comp := d.chi_comp
  p_faithful := d.p_faithful

/-- The rebased datum has the same right action (paper `prop:basechange`: fixed action).
@isnad1 id=eq.0h6v.s6.9d831a7c7b52 from=translated src=- shape=eb4b8371 vocab=ae167ac0
-/
@[simp] theorem rebase_act (d : OEData G p) (c : G) : (d.rebase c).act = d.act := rfl

/-- The rebased datum has the same morphism action (paper `prop:basechange`).
@isnad1 id=eq.0h10v.s7.bb979a9eff98 from=translated src=- shape=26fe146b vocab=f31eb18c
-/
@[simp] theorem rebase_actHom (d : OEData G p) (c : G) {x y : O} (f : x ⟶ y) (g : G) :
    (d.rebase c).actHom f g = d.actHom f g := rfl

/-- The rebased datum has the same transport on objects (paper `prop:basechange`: fixed
    cleavage).
@isnad1 id=eq.1h10v.s6.71026829c9f3 from=translated src=- shape=7ff239d0 vocab=32722aef
-/
theorem rebase_reind (d : OEData G p) (c : G) {s t : S} (u : s ⟶ t) (y : O)
    (hy : p.obj y = t) : (d.rebase c).reind u y hy = d.reind u y hy := rfl

/-- The rebased datum has the same chosen transport arrows `χ` (paper `prop:basechange`).
@isnad1 id=eq.1h10v.s7.a15eaa7617f9 from=translated src=- shape=a9e7a539 vocab=3ea0670e
-/
theorem rebase_chi (d : OEData G p) (c : G) {s t : S} (u : s ⟶ t) (y : O)
    (hy : p.obj y = t) : (d.rebase c).chi u y hy = d.chi u y hy := rfl

/-- The basepoints of the rebased datum are `b'_s = b_s · c` (paper `prop:basechange`).
@isnad1 id=eq.0h7v.s6.95c5f8bd6645 from=translated src=- shape=b4cb8d53 vocab=7df3dbc9
-/
@[simp] theorem rebase_base (d : OEData G p) (c : G) (s : S) :
    (d.rebase c).base s = d.act (d.base s) c := rfl

/-- The coordinates of the rebased datum are `g'_x = c⁻¹ g_x` (paper `prop:basechange`).
@isnad1 id=eq.0h7v.s6.c5527f566ad1 from=translated src=- shape=db645936 vocab=8149694c
-/
@[simp] theorem rebase_coord (d : OEData G p) (c : G) (x : O) :
    (d.rebase c).coord x = c⁻¹ * d.coord x := rfl

/-- The vertical arrows of the rebased datum (paper `prop:basechange`):
    `ℓ'_{a,x} = ℓ_{cac⁻¹,x}` followed by the object identity.
@isnad1 id=ex.0h8v.s10.d0f1d93b9864 from=translated src=- shape=173cd5fe vocab=ce01c0bc
-/
theorem rebase_ltrans (d : OEData G p) (c : G) (a : G) (x : O) :
    ∃ h, (d.rebase c).ltrans a x = d.ltrans (c * a * c⁻¹) x ≫ eqToHom h := ⟨_, rfl⟩

/-- Rebasing by `1` gives back the datum (paper `prop:basechange`, `c = 1`).
@isnad1 id=eq.0h5v.s5.a220989e67a4 from=translated src=- shape=870eb705 vocab=88cc0650
-/
theorem rebase_one (d : OEData G p) : d.rebase 1 = d :=
  OEData.ext_of_data _ _ rfl (funext fun s => d.act_one _)
    (funext fun x => by simp only [rebase_coord, inv_one, one_mul]) (fun _ _ _ => rfl)

/-- Rebasing twice composes the constants (paper `prop:basechange`):
    `(d.rebase c).rebase c' = d.rebase (c * c')`.
@isnad1 id=eq.0h7v.s6.bd78214d8e98 from=translated src=- shape=bc511cc5 vocab=f53e9879
-/
theorem rebase_rebase (d : OEData G p) (c c' : G) :
    (d.rebase c).rebase c' = d.rebase (c * c') :=
  OEData.ext_of_data _ _ rfl (funext fun s => d.act_mul _ _ _)
    (funext fun x => by simp only [rebase_coord, mul_inv_rev, mul_assoc]) (fun _ _ _ => rfl)

end Tengoku.ObserverEquivarianceLean.OEData

/-! ## 2. Every other parallel choice of basepoints is a rebasing -/

/-- Pointwise torsor description of another parallel choice of basepoints (paper
    `prop:basechange`, proof: "the torsor property gives `b'_s = b_s · c(s)`"), with
    `c(s) = g_{b'_s}`.  No hypothesis relating `d'` to `d` is needed.
@isnad1 id=eq.0h7v.s7.53a31021ef88 from=translated src=- shape=55048dc2 vocab=394d1f03
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.parallel_basepoints_pointwise (d d' : OEData G p) (s : S) :
    d'.base s = d.act (d.base s) (d.coord (d'.base s)) := by
  have h := d.base_coord (d'.base s)
  rw [d'.p_base] at h
  exact h.symm

/-- Local constancy of the pointwise factor (paper `prop:basechange`, proof: "applying
    transport along `u : s → t` and using equivariance gives `c(s) = c(t)`"): for data with
    the same transport, `g_{b'_s} = g_{b'_t}` along every base arrow `u : s ⟶ t`.
@isnad1 id=eq.1h9v.s7.411cbdf8eff0 from=translated src=- shape=dc7f7723 vocab=8f37afd3
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.parallel_basepoints_locally_const (d d' : OEData G p)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy)
    {s t : S} (u : s ⟶ t) : d.coord (d'.base s) = d.coord (d'.base t) := by
  have key := d'.reind_base u
  rw [hreind, d.reind_eq] at key
  rw [← key, d.coord_base]

/-- Uniqueness of the constant (paper `prop:basechange`): on a nonempty base, `b'_s = b_s · c`
    for all `s` determines `c`.
@isnad1 id=eq.2h8v.s7.3c8e9b63c179 from=translated src=- shape=ce1a2e76 vocab=9c91bb50
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.parallel_basepoints_const_unique [Nonempty S] (d d' : OEData G p) {c c' : G}
    (hc : ∀ s, d'.base s = d.act (d.base s) c) (hc' : ∀ s, d'.base s = d.act (d.base s) c') :
    c = c' := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  exact d.act_free _ _ _ ((hc s₀).symm.trans (hc' s₀))

/-- Changing parallel basepoints, bare-family form (paper `prop:basechange`, first sentence:
    "Any other parallel choice of basepoints is `b'_s = b_s · c` for one constant `c ∈ G`"):
    on a connected base, any family `b' : S → O` with `p(b'_s) = s` that is parallel for the
    transport of `d` (`u^* b'_t = b'_s` for every `u : s ⟶ t`) is `b'_s = b_s · c` for a UNIQUE
    `c ∈ G`.  No second normalized datum is assumed.
@isnad1 id=existsun.2h6v.s7.d4d18cf8fd38 from=translated src=- shape=469d2658 vocab=dc9610b8
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.parallel_family_eq_translate [IsConnected S] (d : OEData G p) (b' : S → O)
    (hp : ∀ s, p.obj (b' s) = s)
    (hpar : ∀ {s t : S} (u : s ⟶ t), d.reind u (b' t) (hp t) = b' s) :
    ∃! c : G, ∀ s, b' s = d.act (d.base s) c := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have hpt : ∀ s, b' s = d.act (d.base s) (d.coord (b' s)) := fun s => by
    have h := d.base_coord (b' s); rw [hp] at h; exact h.symm
  have hloc : ∀ {s t : S} (u : s ⟶ t), d.coord (b' s) = d.coord (b' t) := fun u => by
    have key := hpar u
    rw [d.reind_eq] at key
    rw [← key, d.coord_base]
  have hconst : ∀ s, d.coord (b' s) = d.coord (b' s₀) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (b' s)) (fun _ _ u => hloc u) s s₀
  refine ⟨d.coord (b' s₀), fun s => by rw [← hconst s]; exact hpt s, fun c hc => ?_⟩
  rw [hc s₀, d.coord_base]

/-- Changing parallel basepoints, bare-family form (paper `prop:basechange`, first sentence):
    on a connected base, every parallel family `b'` for the transport of `d` is the basepoint
    field of the rebased datum `d.rebase c` for a UNIQUE `c ∈ G`.
@isnad1 id=existsun.2h6v.s7.8baf24f4582b from=translated src=- shape=b4409b1e vocab=a0939ba7
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.parallel_family_eq_rebase_base [IsConnected S] (d : OEData G p) (b' : S → O)
    (hp : ∀ s, p.obj (b' s) = s)
    (hpar : ∀ {s t : S} (u : s ⟶ t), d.reind u (b' t) (hp t) = b' s) :
    ∃! c : G, (d.rebase c).base = b' := by
  obtain ⟨c, hc, hu⟩ := parallel_family_eq_translate d b' hp hpar
  exact ⟨c, funext fun s => (hc s).symm, fun c' h => hu c' fun s => by rw [← h]; rfl⟩

/-- Changing parallel basepoints (paper `prop:basechange`, first sentence): on a connected
    base, any other normalized datum `d'` with the same right action and the same transport has
    basepoints `b'_s = b_s · c` for ONE constant `c ∈ G`, and this `c` is unique.
    (The action hypothesis records that the right action is kept fixed; the proof only needs the
    transport hypothesis, hence the binder name `_hact`.)
@isnad1 id=existsun.2h6v.s7.cd5fd666e9b1 from=translated src=- shape=ac3f07b3 vocab=dc9610b8
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.parallel_basepoints_eq_rebase [IsConnected S] (d d' : OEData G p)
    (_hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) :
    ∃! c : G, ∀ s, d'.base s = d.act (d.base s) c := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have hconst : ∀ s, d.coord (d'.base s) = d.coord (d'.base s₀) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (d'.base s))
      (fun _ _ u => parallel_basepoints_locally_const d d' hreind u) s s₀
  refine ⟨d.coord (d'.base s₀), fun s => ?_, fun c hc => ?_⟩
  · rw [← hconst s]
    exact parallel_basepoints_pointwise d d' s
  · have h := hc s₀
    rw [h, d.coord_base]

/-- The coordinate formula `g'_x = c⁻¹ g_x` (paper `prop:basechange`): for the same action
    and `b'_s = b_s · c`.
@isnad1 id=eq.2h8v.s7.1cd0202457d1 from=translated src=- shape=e6425e52 vocab=0519750c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.coord_eq_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (x : O) :
    d'.coord x = c⁻¹ * d.coord x := by
  have h1 : d.act (d.base (p.obj x)) (c * d'.coord x) = x := by
    rw [← d.act_mul, ← hc, ← hact, d'.base_coord]
  have h2 := congrArg d.coord h1
  rw [d.coord_base] at h2
  rw [← h2, inv_mul_cancel_left]

/-- A normalized datum with the same action and transport as `d` and basepoints
    `b'_s = b_s · c` IS the rebased datum `d.rebase c` (paper `prop:basechange`: "any other
    parallel choice of basepoints is `b'_s = b_s · c`", as an equality of data).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.eq_rebase_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) : d' = d.rebase c :=
  OEData.ext_of_data d' (d.rebase c) (funext fun x => funext fun g => hact x g) (funext hc)
    (funext (coord_eq_of_base d d' hact hc)) hreind

/-- Changing parallel basepoints, datum form (paper `prop:basechange`): on a connected base,
    every normalized datum `d'` with the same action and transport as `d` is `d.rebase c` for a
    unique `c ∈ G`.
@isnad1 id=existsun.2h6v.s7.b7b4b09005ca from=translated src=- shape=792ad2c3 vocab=4bc8d8ec
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.exists_unique_eq_rebase [IsConnected S] (d d' : OEData G p)
    (hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) :
    ∃! c : G, d' = d.rebase c := by
  obtain ⟨c, hc, _⟩ := parallel_basepoints_eq_rebase d d' hact hreind
  refine ⟨c, eq_rebase_of_base d d' hact hreind hc, fun c' hc' => ?_⟩
  have hb : ∀ s, d'.base s = d.act (d.base s) c' := fun s => by rw [hc']; rfl
  exact parallel_basepoints_const_unique d d' hb hc

/-! ## 3. Functor formulas (no connectedness needed) -/

/-- Normalized translations after a change of basepoints (paper `prop:basechange`):
    `Λ'_a = Λ_{cac⁻¹}` as functors `O ⥤ O`.
@isnad1 id=eq.2h8v.s7.fba646dcaa17 from=translated src=- shape=c0542a7a vocab=195528b4
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_eq_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (a : G) :
    Λ d' a = Λ d (c * a * c⁻¹) := by
  refine funct_ext d (fun x => ?_) (by rw [Λ_comp_p, Λ_comp_p])
  show d'.act (d'.base (p.obj x)) (a * d'.coord x)
    = d.act (d.base (p.obj x)) (c * a * c⁻¹ * d.coord x)
  rw [hact, hc, d.act_mul, coord_eq_of_base d d' hact hc]
  congr 1
  group

/-- Normalized translations after a change of basepoints, conjugation form (paper
    `prop:basechange`): `Λ'_a = Λ_c Λ_a Λ_c⁻¹` (operator order), i.e.
    `Λ d' a = Λ d c⁻¹ ⋙ Λ d a ⋙ Λ d c`.
@isnad1 id=eq.2h8v.s7.95aadc5f36eb from=translated src=- shape=fd5e3cea vocab=a0202880
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_eq_conj_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (a : G) :
    Λ d' a = Λ d c⁻¹ ⋙ Λ d a ⋙ Λ d c := by
  rw [Λ_eq_of_base d d' hact hc, Λ_comp, Λ_comp]

/-- Canonical lifts are unchanged by a change of parallel basepoints (paper
    `prop:basechange`): `Ã' = Ã` as functors, for every `A : S ⥤ S`.
@isnad1 id=eq.2h8v.s7.c0dec634948f from=translated src=- shape=3fe49535 vocab=d8f8f096
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctor_eq_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (A : S ⥤ S) :
    liftFunctor d' A = liftFunctor d A := by
  refine funct_ext d (fun x => ?_)
    (by rw [(lift_preservesCleavage d' A).covers, (lift_preservesCleavage d A).covers])
  show d'.act (d'.base (A.obj (p.obj x))) (d'.coord x)
    = d.act (d.base (A.obj (p.obj x))) (d.coord x)
  rw [hact, hc, d.act_mul, coord_eq_of_base d d' hact hc, mul_inv_cancel_left]

/-- The displayed object identity in the proof of `prop:basechange`:
    `b'_{A(p x)} · θ_A(g'_x) = b_{A(p x)} · (c θ_A(c⁻¹) θ_A(g_x))`.
@isnad1 id=eq.2h10v.s9.262ccb1ac8af from=translated src=- shape=6c402a91 vocab=ebd59b8a
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctorθ_obj_eq_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (A : S ⥤ S) (θ : MulAut G) (x : O) :
    d'.act (d'.base (A.obj (p.obj x))) (θ (d'.coord x))
      = d.act (d.base (A.obj (p.obj x))) (c * θ c⁻¹ * θ (d.coord x)) := by
  rw [hact, hc, d.act_mul, coord_eq_of_base d d' hact hc, map_mul, mul_assoc]

/-- Twisted canonical lifts after a change of basepoints (paper `prop:basechange`):
    `Ã'_θ = Λ_{c θ_A(c⁻¹)} Ã_θ` (operator order), i.e.
    `liftFunctorθ d' A θ = liftFunctorθ d A θ ⋙ Λ d (c * θ c⁻¹)` as functors.
@isnad1 id=eq.2h9v.s8.d48d35f356ea from=translated src=- shape=ce0a113e vocab=d083173f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctorθ_eq_of_base (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ d' A θ = liftFunctorθ d A θ ⋙ Λ d (c * θ c⁻¹) := by
  refine funct_ext d (fun x => ?_)
    (by rw [liftθ_covers, Functor.assoc, Λ_comp_p, liftθ_covers])
  show d'.act (d'.base (A.obj (p.obj x))) (θ (d'.coord x))
    = d.act (d.base (p.obj (d.act (d.base (A.obj (p.obj x))) (θ (d.coord x)))))
        (c * θ c⁻¹ * d.coord (d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))))
  rw [liftFunctorθ_obj_eq_of_base d d' hact hc, d.p_act, d.p_base, d.coord_base]

/-- Twisted canonical lifts after a change of basepoints, conjugation form (paper
    `prop:basechange`): `Ã'_θ = Λ_c Ã_θ Λ_c⁻¹` (operator order), i.e.
    `liftFunctorθ d' A θ = Λ d c⁻¹ ⋙ liftFunctorθ d A θ ⋙ Λ d c`.
@isnad1 id=eq.2h9v.s7.63d8447dae75 from=translated src=- shape=03794811 vocab=924d3213
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctorθ_eq_conj_of_base (d d' : OEData G p)
    (hact : ∀ x g, d'.act x g = d.act x g)
    {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c) (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ d' A θ = Λ d c⁻¹ ⋙ liftFunctorθ d A θ ⋙ Λ d c := by
  rw [liftFunctorθ_eq_of_base d d' hact hc, ← Functor.assoc, Λ_comp_liftθ, Functor.assoc,
    Λ_comp]

/-- The rebased translations (paper `prop:basechange` for `d.rebase c`):
    `Λ (d.rebase c) a = Λ d (c * a * c⁻¹)`.
@isnad1 id=eq.0h7v.s6.fc7f183833d4 from=translated src=- shape=0f4c33ce vocab=6f67645f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_rebase (d : OEData G p) (c a : G) : Λ (d.rebase c) a = Λ d (c * a * c⁻¹) :=
  Λ_eq_of_base d (d.rebase c) (fun _ _ => rfl) (fun _ => rfl) a

/-- The rebased canonical lifts (paper `prop:basechange` for `d.rebase c`):
    `liftFunctor (d.rebase c) A = liftFunctor d A`.
@isnad1 id=eq.0h7v.s6.76bf3c5020e6 from=translated src=- shape=3523841b vocab=71472fae
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctor_rebase (d : OEData G p) (c : G) (A : S ⥤ S) :
    liftFunctor (d.rebase c) A = liftFunctor d A :=
  liftFunctor_eq_of_base d (d.rebase c) (fun _ _ => rfl) (fun _ => rfl) A

/-- The rebased twisted lifts (paper `prop:basechange` for `d.rebase c`):
    `liftFunctorθ (d.rebase c) A θ = liftFunctorθ d A θ ⋙ Λ d (c * θ c⁻¹)`.
@isnad1 id=eq.0h8v.s7.8debc5ef0563 from=translated src=- shape=510eaa12 vocab=bff53af4
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctorθ_rebase (d : OEData G p) (c : G) (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ (d.rebase c) A θ = liftFunctorθ d A θ ⋙ Λ d (c * θ c⁻¹) :=
  liftFunctorθ_eq_of_base d (d.rebase c) (fun _ _ => rfl) (fun _ => rfl) A θ

/-! ## 4. The lift conditions do not refer to basepoints or coordinates -/

/-- `G`-equivariance only depends on the right action (paper `sec:normalization`: the group
    of admissible lifts does not refer to basepoints or coordinates).
@isnad1 id=iff.1h7v.s6.233bd4fde464 from=translated src=- shape=b79b491a vocab=05c22838
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isGEquivariant_iff_of_act_eq (d d' : OEData G p)
    (hact : ∀ x g, d'.act x g = d.act x g) (F : O ⥤ O) :
    IsGEquivariant d' F ↔ IsGEquivariant d F := by
  simp only [IsGEquivariant, hact]

/-- Twisted equivariance only depends on the right action (paper `sec:normalization`).
@isnad1 id=iff.1h8v.s6.59d6e19c78de from=translated src=- shape=efb37b3a vocab=6c61e5e5
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isTwistedEquivariant_iff_of_act_eq (d d' : OEData G p)
    (hact : ∀ x g, d'.act x g = d.act x g) (θ : MulAut G) (F : O ⥤ O) :
    IsTwistedEquivariant d' θ F ↔ IsTwistedEquivariant d θ F := by
  simp only [IsTwistedEquivariant, hact]

/-- Cleavage preservation only depends on the transport (paper `sec:normalization`).
@isnad1 id=iff.1h8v.s7.9bd60e6f6343 from=translated src=- shape=8c2a25a2 vocab=9bcef678
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.preservesCleavage_iff_of_reind_eq (d d' : OEData G p)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) (F : O ⥤ O) (A : S ⥤ S) :
    PreservesCleavage d' F A ↔ PreservesCleavage d F A := by
  constructor
  · intro h
    exact ⟨h.covers, fun u y hy => by rw [← hreind, ← hreind]; exact h.src u y hy⟩
  · intro h
    exact ⟨h.covers, fun u y hy => by rw [hreind, hreind]; exact h.src u y hy⟩

/-! ## 5. Canonical identifications of the lift groups -/

/-- The canonical identification `Sym(d) ≃* Sym(d')` for data with the same action and
    transport (paper `sec:normalization`): the IDENTITY on `hom`, `inv` and `base`; only the
    proofs of equivariance and cleavage preservation are transported.-/
def _root_.Tengoku.ObserverEquivarianceLean.autBoxGCongr (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) :
    AutBoxG d ≃* AutBoxG d' where
  toFun e :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id
      base := e.base
      equiv := (isGEquivariant_iff_of_act_eq d d' hact e.hom).2 e.equiv
      pres := (preservesCleavage_iff_of_reind_eq d d' hreind e.hom e.base.hom).2 e.pres }
  invFun e :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id
      base := e.base
      equiv := (isGEquivariant_iff_of_act_eq d d' hact e.hom).1 e.equiv
      pres := (preservesCleavage_iff_of_reind_eq d d' hreind e.hom e.base.hom).1 e.pres }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

section CongrSimp

variable (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
  (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    d'.reind u y hy = d.reind u y hy)

/-- `autBoxGCongr` is the identity on `hom` (paper `sec:normalization`).
@isnad1 id=eq.2h7v.s9.9e3d1a2f99bb from=translated src=- shape=326798e7 vocab=e33b23fb
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGCongr_hom (e : AutBoxG d) :
    (autBoxGCongr d d' hact hreind e).hom = e.hom := rfl

/-- `autBoxGCongr` is the identity on `inv` (paper `sec:normalization`).
@isnad1 id=eq.2h7v.s9.b348613819d5 from=translated src=- shape=326798e7 vocab=ecde977a
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGCongr_inv (e : AutBoxG d) :
    (autBoxGCongr d d' hact hreind e).inv = e.inv := rfl

/-- `autBoxGCongr` is the identity on `base` (paper `sec:normalization`).
@isnad1 id=eq.2h7v.s9.c41bdefd60d8 from=translated src=- shape=282892fa vocab=4b3c5ebb
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGCongr_base (e : AutBoxG d) :
    (autBoxGCongr d d' hact hreind e).base = e.base := rfl

/-- The inverse of `autBoxGCongr` is the identity on `hom` (paper `sec:normalization`).
@isnad1 id=eq.2h7v.s9.b893467decd3 from=translated src=- shape=a14ba6a5 vocab=c25749ac
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGCongr_symm_hom (e : AutBoxG d') :
    ((autBoxGCongr d d' hact hreind).symm e).hom = e.hom := rfl

end CongrSimp

/-- The canonical identification `Sym_H(d) ≃* Sym_H(d')` of the lifts over a subgroup
    `H ≤ StrictAut S` (paper `sec:normalization`): the restriction of `autBoxGCongr`, hence the
    identity on `hom`, `inv` and `base`.-/
def _root_.Tengoku.ObserverEquivarianceLean.autBoxGOverCongr (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) (H : Subgroup (StrictAut S)) :
    AutBoxGOver d H ≃* AutBoxGOver d' H where
  toFun e := ⟨autBoxGCongr d d' hact hreind e.1, e.2⟩
  invFun e := ⟨(autBoxGCongr d d' hact hreind).symm e.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `autBoxGOverCongr` is `autBoxGCongr` on the underlying bundle automorphisms
    (paper `sec:normalization`).
@isnad1 id=eq.2h8v.s10.0918432b6b2c from=translated src=- shape=76b58215 vocab=4f5cfdd6
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGOverCongr_coe (d d' : OEData G p)
    (hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) (H : Subgroup (StrictAut S)) (e : AutBoxGOver d H) :
    (autBoxGOverCongr d d' hact hreind H e).1 = autBoxGCongr d d' hact hreind e.1 := rfl

/-- The canonical identification `Sym^θ_H(d) ≃* Sym^θ_H(d')` of the twisted lifts (paper
    `sec:normalization`): the identity on `hom`, `inv` and `base`.-/
def _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverCongr (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d'.reind u y hy = d.reind u y hy) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) :
    AutBoxGθOver d H θ ≃* AutBoxGθOver d' H θ where
  toFun e :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id
      base := e.base
      equiv := (isTwistedEquivariant_iff_of_act_eq d d' hact (θ e.base) e.hom).2 e.equiv
      pres := (preservesCleavage_iff_of_reind_eq d d' hreind e.hom e.base.1.hom).2 e.pres }
  invFun e :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id
      base := e.base
      equiv := (isTwistedEquivariant_iff_of_act_eq d d' hact (θ e.base) e.hom).1 e.equiv
      pres := (preservesCleavage_iff_of_reind_eq d d' hreind e.hom e.base.1.hom).1 e.pres }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

section CongrθSimp

variable (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
  (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    d'.reind u y hy = d.reind u y hy) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)

/-- `autBoxGθOverCongr` is the identity on `hom` (paper `sec:normalization`).
@isnad1 id=eq.2h9v.s10.1412f332705e from=translated src=- shape=7087e918 vocab=7337c44d
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverCongr_hom (e : AutBoxGθOver d H θ) :
    (autBoxGθOverCongr d d' hact hreind H θ e).hom = e.hom := rfl

/-- `autBoxGθOverCongr` is the identity on `inv` (paper `sec:normalization`).
@isnad1 id=eq.2h9v.s10.18c8eb8952da from=translated src=- shape=7087e918 vocab=16542f1f
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverCongr_inv (e : AutBoxGθOver d H θ) :
    (autBoxGθOverCongr d d' hact hreind H θ e).inv = e.inv := rfl

/-- `autBoxGθOverCongr` is the identity on `base` (paper `sec:normalization`).
@isnad1 id=eq.2h9v.s10.ba8c5fec8530 from=translated src=- shape=1c5ee237 vocab=1c43ab86
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverCongr_base (e : AutBoxGθOver d H θ) :
    (autBoxGθOverCongr d d' hact hreind H θ e).base = e.base := rfl

end CongrθSimp

/-! ## 6. Homomorphism-level formulas -/

section HomFormulas

variable (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
  (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    d'.reind u y hy = d.reind u y hy)
  {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c)

include hact hc in
/-- Inverse translations after a change of basepoints (used for the `inv` fields):
    `Λ'_{a⁻¹} = Λ_{(cac⁻¹)⁻¹}` (paper `prop:basechange`).
@isnad1 id=eq.2h8v.s7.aeebfc86a181 from=translated src=- shape=a13a67bf vocab=195528b4
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_inv_eq_of_base (a : G) : Λ d' a⁻¹ = Λ d (c * a * c⁻¹)⁻¹ := by
  rw [Λ_eq_of_base d d' hact hc]
  congr 1
  group

end HomFormulas

/-! ## 7. The two classifying isomorphisms differ by an inner automorphism -/

section Identifications

variable (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
  (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    d'.reind u y hy = d.reind u y hy)
  {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c)

end Identifications

/-! ## 8. The twist factor is a coboundary -/

/-- The factor `z_c(A) = c θ_A(c⁻¹)` of `prop:basechange` satisfies the nonabelian cocycle
    identity `z_c(AB) = z_c(A) θ_A(z_c(B))` (paper `sec:normalization`, cocycle paragraph).
    This is a local duplicate: the canonical statement is
    `OECocycle.coboundary_mul` in `Cocycles`, and `baseChange_twistFactor_eq_coboundary` (module
    `BaseChangeCocycle`) shows `c θ_A(c⁻¹) = OECocycle.coboundary θ c A`; downstream uses should
    cite `OECocycle.coboundary_mul`.
@isnad1 id=eq.0h6v.s10.2a5eab4d5a01 from=translated src=- shape=4c4dab56 vocab=64dd4a73
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.baseChange_twistFactor_mul {H : Type*} [Group H] (θ : H →* MulAut G) (c : G)
    (A B : H) : c * θ (A * B) c⁻¹ = (c * θ A c⁻¹) * θ A (c * θ B c⁻¹) := by
  simp only [map_mul, MulAut.mul_apply, map_inv]
  group
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
