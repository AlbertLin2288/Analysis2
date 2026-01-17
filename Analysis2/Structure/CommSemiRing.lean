import Analysis2.Nat
import Analysis2.Structure.SemiRing
noncomputable section
namespace my
open Classical
open Zero One OfNat
open Monoid CommMonoid SemiRing

class CommSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [CommMonoid α] where
  _mul_one : ∀(a : α), a * one = a
  _mul_assoc : ∀(a b c : α), (a * b) * c = a * (b * c)
  _mul_zero : ∀(a : α), a * zero = zero
  _add_mul : ∀(a b c : α), (a + b) * c = a * c + b * c
  _zero_ne_one : (zero : α) ≠ one -- non-trvial
  mul_comm : ∀(a b : α), a * b = b * a

namespace CommSemiRing

  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [CommMonoid α] [CommSemiRing α]

  instance : Std.Commutative (α := α) Mul.mul := ⟨mul_comm⟩

  theorem _one_mul : ∀(a : α), one * a = a := by
    intro a;rw [mul_comm, _mul_one]

  theorem _zero_mul : ∀(a : α), zero * a = zero := by
    intro a;rw [mul_comm, _mul_zero]

  theorem _mul_add : ∀(a b c : α), a * (b + c) = a * b + a * c := by
    intro a b c;simp only [mul_comm a, _add_mul]

  @[default_instance] instance : SemiRing α := ⟨_mul_one, _one_mul, _mul_assoc, _mul_zero, _zero_mul, _mul_add, _add_mul, _zero_ne_one⟩

  theorem mul_right_comm : ∀ (a b c : α), (a * b) * c = (a * c) * b := by
    intros
    ac_nf

  theorem mul_left_comm : ∀ (a b c : α), a * (b * c) = b * (a * c) := by
    intros
    ac_nf

  open ℕ (_zero succ)

  -- def ofNat : ℕ → α
  -- | _zero => zero
  -- | succ n => (ofNat n) + one

  @[default_instance, reducible] instance : OfNat α where
    ofNat := ℕ.rec zero fun _ p => p + one

  -- omit α in
  -- @[reducible] def ofNat' (α : Type) [Zero α] [Add α] [One α] [Mul α] : ℕ → α := ofNat (α:=α)

  omit [Mul α] in
  theorem ofNat_add {n m : ℕ} : ofNat (n + m) = ofNat (α:=α) n + ofNat m :=
    match m with
    | _zero => (add_zero (ofNat n)).symm
    | succ _ => add_assoc _ _ (one:α) ▸ congrArg (·+one) ofNat_add

  theorem ofNat_mul {n m : ℕ} : ofNat (α:=α) n * ofNat m = ofNat (n * m) :=
    match m with
    | _zero => mul_zero (ofNat n)
    | succ m =>
      suffices (ofNat' α n * (ofNat m + one)) = ofNat (n * m + n) from this
      by rw [mul_add, mul_one, ofNat_add, ofNat_mul]


end CommSemiRing

end my
