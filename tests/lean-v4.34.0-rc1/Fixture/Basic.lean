/-!
The declaration shapes the emitter has to label and locate: one `structure`,
one `inductive`, one `class`, a projection, and a `private` def (whose mangled
internal name must be reported under the name it is written with).
-/

namespace Fixture

/-- A structure. -/
structure Point where
  x : Nat
  y : Nat

/-- An inductive. Matching on it makes the compiler synthesize `Shape.casesOn`
and friends, which the emitter must report as `Shape` rather than leak. -/
inductive Shape where
  | dot : Point → Shape
  | seg : Point → Point → Shape

/-- A class. -/
class Weight (α : Type) where
  weight : α → Nat

/-- A definition. -/
def Point.sum (p : Point) : Nat := p.x + p.y

/-- A private definition: written `Fixture.scale`, stored mangled. -/
private def scale (k : Nat) (p : Point) : Point := ⟨k * p.x, k * p.y⟩

/-- A public definition whose body reaches a private one. -/
def double (p : Point) : Point := scale 2 p

/-- `double`'s first coordinate. `scale` is private, so a downstream module can
only reason about `double` through a public lemma like this one. -/
theorem double_x (p : Point) : (double p).x = 2 * p.x := rfl

instance : Weight Shape where
  weight
    | .dot p => p.sum
    | .seg p q => p.sum + q.sum

end Fixture

namespace Fixture

/-- Size guarantees used to construct an algorithm. -/
structure Sound : Prop where
  valid : 0 = 0

theorem sound : Sound := ⟨rfl⟩

/-- An algorithm carrying a size guarantee. -/
structure Algorithm where
  size : Nat
  valid : size = 0

def Sound.toAlgorithm (h : Sound) : Algorithm := ⟨0, h.valid⟩

def algorithm : Algorithm := sound.toAlgorithm

end Fixture
