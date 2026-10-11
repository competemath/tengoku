import Tengoku
/-!
  # Collisions and collision resistance of a function

  The collision vocabulary, stated over an arbitrary function rather than any
  particular hash. A collision is two distinct inputs with the same image;
  collision resistance is the absence of one. Both are interesting independent
  of which function appears — `sha256d`, a merkle node combiner, an abstract
  commitment hash — so they live here once and specialize where needed.

  Collision resistance is never an axiom over a concrete function (it is
  provably false there by pigeonhole). It enters as a *hypothesis*, and from it
  injectivity follows: a collision-resistant function is injective on the nose.
  Composition is the other load-bearing fact — a collision in `g ∘ f` is a
  collision in `f` or in `g` — which is exactly what carries collision
  resistance through Bitcoin's double hashing.

  Checked claims:

  * `CollisionResistant.injective`: a collision-resistant function is injective.
  * `Collision.comp`: a collision in `g ∘ f` yields a collision in `f` or `g`.
  * `CollisionResistant.comp`: collision resistance of `f` and `g` gives
    collision resistance of `g ∘ f`.
-/

namespace BtcVerified

/-- A collision in `h`: two distinct inputs sharing an image. -/
def Collision {α β : Type*} (h : α → β) : Prop := ∃ a b : α, a ≠ b ∧ h a = h b

/-- `h` is collision-resistant when it has no collision. For a concrete function
this is a hypothesis a caller supplies, never an axiom — it is provably false
for any function out of an infinite domain into a finite one. -/
def CollisionResistant {α β : Type*} (h : α → β) : Prop := ¬ Collision h

/-- A collision-resistant function is injective: equal images force equal
inputs. This is the bridge that turns the `… ∨ Collision` disjunct of the
hashing binding theorems into outright injectivity under a resistance
hypothesis.
@isnad1 id=eq.2h5v.s4.571014efcd96 from=translated src=- shape=e5eba5a3 vocab=85814278
-/
theorem CollisionResistant.injective {α β : Type*} {h : α → β}
    (hcr : CollisionResistant h) {a b : α} (hab : h a = h b) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exact absurd ⟨a, b, hne, hab⟩ hcr

/-- A collision in `g ∘ f` is a collision in `f` (its inputs already collide
under `f`) or in `g` (their distinct `f`-images collide under `g`).
@isnad1 id=or.1h5v.s5.a24e1b099575 from=translated src=- shape=b38bb36d vocab=eca21a80
-/
theorem Collision.comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hc : Collision (g ∘ f)) : Collision f ∨ Collision g := by
  match hc with
  | ⟨a, b, hab, h⟩ =>
    by_cases hf : f a = f b
    · exact Or.inl ⟨a, b, hab, hf⟩
    · exact Or.inr ⟨f a, f b, hf, h⟩

/-- Collision resistance composes: if `f` and `g` are each collision-resistant,
so is `g ∘ f`.
@isnad1 id=collisio.2h5v.s5.fe334ce5e991 from=translated src=- shape=6c2e57d7 vocab=351ca5de
-/
theorem CollisionResistant.comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : CollisionResistant f) (hg : CollisionResistant g) :
    CollisionResistant (g ∘ f) :=
  fun hc => (Collision.comp hc).elim hf hg

/-- A collision in the inner function lifts to a collision in the composite:
the colliding inputs already agree under `f`, hence under `g ∘ f`.
@isnad1 id=collisio.1h5v.s4.1b40d7d79abc from=translated src=- shape=1667777c vocab=eca21a80
-/
theorem Collision.comp_inner {α β γ : Type*} {f : α → β} {g : β → γ}
    (hc : Collision f) : Collision (g ∘ f) := by
  match hc with
  | ⟨a, b, hab, h⟩ => exact ⟨a, b, hab, congrArg g h⟩

/-- The partial dual of `CollisionResistant.comp`: resistance of `g ∘ f` forces
resistance of the *inner* `f` (a collision in `f` would lift to one in the
composite). It does **not** force resistance of the outer `g` — `g` may collide
on values outside the range of `f`, where no composite input reaches.
@isnad1 id=collisio.1h5v.s4.b959bb60a367 from=translated src=- shape=d1f5f383 vocab=351ca5de
-/
theorem CollisionResistant.of_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (h : CollisionResistant (g ∘ f)) : CollisionResistant f :=
  fun hc => h hc.comp_inner

end BtcVerified
