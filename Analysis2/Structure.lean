import Analysis2.Operator
noncomputable section
namespace my
open Classical
open Zero One


class Monoid (α : Type) [Zero α] [Add α] where
  add_zero : ∀(a : α), a + zero = a
  zero_add : ∀(a : α), zero + a = a
  add_assoc : ∀(a b c : α), (a + b) + c = a + (b + c)

namespace Monoid

  variable {α : Type} [Zero α] [Add α] [Monoid α]

  instance : Std.Associative (α := α) Add.add := ⟨add_assoc⟩

end Monoid



class CommMonoid (α : Type) [Zero α] [Add α] where
  _add_zero : ∀(a : α), a + zero = a
  _add_assoc : ∀(a b c : α), (a + b) + c = a + (b + c)
  add_comm : ∀(a b : α), a + b = b + a

namespace CommMonoid

  variable {α : Type} [Zero α] [Add α] [CommMonoid α]

  instance : Std.Commutative (α := α) Add.add := ⟨add_comm⟩

  theorem _zero_add : ∀(a : α), zero + a = a := by
    intro a;rw [add_comm, _add_zero]

  @[default_instance] instance : Monoid α := ⟨_add_zero, _zero_add, _add_assoc⟩

  theorem add_right_comm : ∀ (a b c : α), (a + b) + c = (a + c) + b := by
    intros
    ac_nf

  theorem add_left_comm : ∀ (a b c : α), a + (b + c) = b + (a + c) := by
    intros
    ac_nf

end CommMonoid


class CommGroup (α : Type) [Zero α] [Add α] [Neg α] [CommMonoid α] where
  add_neg : ∀(a : α), a + (-a) = zero

namespace CommGroup

  open Monoid CommMonoid
  variable {α : Type} [Zero α] [Add α] [Neg α] [CommMonoid α] [CommGroup α]

  @[default_instance, reducible] instance : Sub α where
    sub := fun a b => a + (-b)

  theorem neg_add : ∀(a : α), (-a) + a = zero := by
    intro a
    rw [add_comm, add_neg]

  theorem neg_neg : ∀(a : α), - (-a) = a := by
    intro a
    rw [← add_zero (- -a), ← neg_add a, ← add_assoc, neg_add, zero_add]

  theorem neg_inj {a b : α} : -a = -b → a = b := by
    intro h
    rw [← neg_neg a, h, neg_neg]

  theorem neg_inj_iff {a b : α} : -a = -b ↔ a = b :=
    Iff.intro neg_inj (congrArg _)

  theorem neg_zero : (-zero : α) = zero := by
    rw [← zero_add (-zero), add_neg]

  theorem sub_self : ∀(a : α), a - a = zero := add_neg

  theorem eq_neg_of_eq_neg {a b : α} : a = -b → b = -a := by
    intro h;rw[h,neg_neg]

  theorem eq_neg_comm {a b : α} : a = -b ↔ b = -a :=
    ⟨eq_neg_of_eq_neg, eq_neg_of_eq_neg⟩

  theorem eq_neg_of_sum_zero {a b : α} : a + b = zero → a = -b := by
    intro h
    rw [←zero_add (-b), ←h, add_assoc, add_neg, add_zero]

  theorem sum_zero_of_eq_neg {a b : α} : a = -b → a + b = zero := by
    intro h;rw [h, neg_add]

  theorem sum_zero_iff {a b : α} : a + b = zero ↔ a = -b :=
    ⟨eq_neg_of_sum_zero, sum_zero_of_eq_neg⟩

  set_option linter.unusedSectionVars false in
  theorem add_neg_eq_sub {a b : α} : a + -b = a - b := rfl

  set_option linter.unusedSectionVars false in
  theorem sub_eq_add_neg : ∀(a b : α), a - b = a + (-b) := fun _ _ => rfl

  theorem eq_of_sub_eq_zero : ∀(a b : α), a - b = zero → a = b := by
    intro a b h;
    rw [←add_zero a, ←neg_add b, ←add_assoc, add_neg_eq_sub, h, zero_add]

  set_option linter.unusedSectionVars false in
  theorem add_sub_assoc : ∀(a b c : α), (a + b) - c = a + (b - c) :=
    fun _ _ c => add_assoc _ _ (-c)

  theorem eq_add_of_sub_eq {a b c : α} : a - b = c → a = c + b := by
    intro h
    rw [←add_zero a, ←neg_add b, ←add_assoc, add_neg_eq_sub, h]

  theorem neg_sum : ∀(a b : α), -(a + b) = -a + -b := by
    intro a b
    rw [←add_zero (-a + _), ←add_neg (a + b), ←add_assoc, ←add_assoc, add_right_comm (-a), neg_add, zero_add, neg_add, zero_add]

  theorem neg_sub : ∀(a b : α), -(a - b) = b - a := by
    intro a b
    simp only [sub_eq_add_neg, neg_sum, neg_neg, add_comm]

  theorem sub_add_assoc : ∀(a b c : α), (a - b) + c = a - (b - c) := by
    intros;simp only [sub_eq_add_neg , neg_sum, neg_neg, add_assoc]

  theorem add_sub_right_comm : ∀(a b c : α), a + b - c = a - c + b := by
    intros;simp only [sub_eq_add_neg, add_right_comm]

  theorem sub_add_right_comm : ∀(a b c : α), a - b + c = a + c - b := by
    intros;simp only [sub_eq_add_neg, add_right_comm]

  theorem add_sub_cancel : ∀(a b : α), a + b - b = a := by
    intros;rw [add_sub_assoc, sub_self, add_zero]

  theorem sub_add_cancel : ∀(a b : α), a - b + b = a := by
    intros;rw [sub_add_right_comm, add_sub_cancel]

  theorem add_left_inj {a b : α} : ∀ (c : α), a + c = b + c → a = b := by
    intro c h
    rw [←add_zero a, ←add_zero b, ←add_neg c, ←add_assoc, ←add_assoc, h]

  theorem add_right_inj {a b : α} : ∀ (c : α), c + a = c + b → a = b := by
    intro c h
    rw [←zero_add a, ←zero_add b, ←neg_add c, add_assoc, add_assoc, h]

  theorem add_left_inj_iff {a b c : α} : a + c = b + c ↔ a = b :=
    ⟨add_left_inj _, congrArg (· + _)⟩

  theorem add_right_inj_iff {a b c : α} : c + a = c + b ↔ a = b :=
    ⟨add_right_inj _, congrArg (_ + ·)⟩


end CommGroup



class SemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [CommMonoid α] where
  mul_one : ∀(a : α), a * one = a
  one_mul : ∀(a : α), one * a = a
  mul_assoc : ∀(a b c : α), (a * b) * c = a * (b * c)
  mul_zero : ∀(a : α), a * zero = zero
  zero_mul : ∀(a : α), zero * a = zero
  mul_add : ∀(a b c : α), a * (b + c) = a * b + a * c
  add_mul : ∀(a b c : α), (a + b) * c = a * c + b * c
  zero_ne_one : (zero : α) ≠ one -- non-trvial

namespace SemiRing

  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [CommMonoid α] [SemiRing α]

  instance : Std.Associative (α := α) Mul.mul := ⟨mul_assoc⟩

end SemiRing



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


end CommSemiRing



class CommRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [CommMonoid α] [CommGroup α] where
  _mul_one : ∀(a : α), a * one = a
  _mul_assoc : ∀(a b c : α), (a * b) * c = a * (b * c)
  _add_mul : ∀(a b c : α), (a + b) * c = a * c + b * c
  _zero_ne_one : (zero : α) ≠ one -- non-trvial
  _mul_comm : ∀(a b : α), a * b = b * a

namespace CommRing

  open Monoid CommGroup SemiRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [CommMonoid α] [CommGroup α] [CommRing α]

  private theorem _mul_zero : ∀ (a : α), a * zero = zero := by
    intro a
    rw [←add_right_inj_iff (c := a), add_zero]
    rw (occs := .pos [1]) [←_mul_one a]
    rw [_mul_comm, _mul_comm a, ←_add_mul, add_zero, _mul_comm, _mul_one]

  @[default_instance] instance : CommSemiRing α := ⟨_mul_one, _mul_assoc, _mul_zero, _add_mul, _zero_ne_one, _mul_comm⟩

  theorem mul_neg_left {a b : α} : (-a) * b = -(a * b) := by
    rw [←sum_zero_iff, ←add_mul, neg_add, zero_mul]

  theorem mul_neg_right {a b : α} : a * (-b) = -(a * b) := by
    rw [←sum_zero_iff, ←mul_add, neg_add, mul_zero]

  theorem mul_sub : ∀(a b c : α), a * (b - c) = a * b - a * c := by
    intros;simp only [sub_eq_add_neg, mul_add, mul_neg_right]

  theorem sub_mul : ∀(a b c : α), (a - b) * c = a * c - b * c := by
    intros;simp only [sub_eq_add_neg, add_mul, mul_neg_left]

end CommRing



class CommRing' (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [CommMonoid α] [CommGroup α] [CommRing α] where
  mul_eq_zero {a b : α} : a * b = zero → a = zero ∨ b = zero -- equivalent to mul_pos, see test2

namespace CommRing'
  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]

end CommRing'



class Field (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [CommMonoid α] [CommGroup α] [CommRing α] where
  mul_inv_cancel : ∀(a : α), (h0 : a ≠ zero) → a * ⟨a, h0⟩⁻¹ = one

namespace Field
  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing'
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [CommMonoid α] [CommGroup α] [CommRing α] [Field α]

  theorem inv_mul_cancel : ∀(a : α), (h : a ≠ zero) → ⟨a, h⟩⁻¹ * a = one :=
    fun a h => (mul_comm a ⟨a, h⟩⁻¹) ▸ (mul_inv_cancel a h)

  theorem mul_inv_mul_cancel_right {a b : α} (h : b ≠ zero) : (a * ⟨b, h⟩⁻¹) * b = a := by
    rw [mul_assoc, inv_mul_cancel , mul_one]

  theorem mul_inv_mul_cancel_left {a b : α} (h : a ≠ zero) : a * (⟨a, h⟩⁻¹ * b) = b := by
    rw [←mul_assoc, mul_inv_cancel, one_mul]

  theorem mul_mul_inv_cancel_right {a b : α} (h : b ≠ zero) : (a * b) * ⟨b, h⟩⁻¹ = a := by
    rw [mul_assoc, mul_inv_cancel, mul_one]

  theorem mul_mul_inv_cancel_left1 {a b : α} (h : a ≠ zero) : (a * b) * ⟨a, h⟩⁻¹ = b := by
    rw [mul_right_comm, mul_inv_cancel, one_mul]

  theorem mul_mul_inv_cancel_left2 {a b : α} (h : a ≠ zero) : a * (b * ⟨a, h⟩⁻¹) = b := by
    rw [mul_left_comm, mul_inv_cancel, mul_one]

  theorem _mul_eq_zero {a b : α} : a * b = zero → a = zero ∨ b = zero := by
    intro h
    apply byContradiction _
    intro h'
    replace h' := not_or.mp h'
    replace h := congrArg (.*⟨b,h'.right⟩⁻¹*⟨a,h'.left⟩⁻¹) h
    simp only [zero_mul, mul_mul_inv_cancel_right, mul_inv_cancel] at h
    exact zero_ne_one h.symm

  @[default_instance] instance : CommRing' α where
    mul_eq_zero := _mul_eq_zero

end Field

end my
