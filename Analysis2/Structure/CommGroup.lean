import Analysis2.Structure.CommMonoid
noncomputable section
namespace my
open Classical
open Zero One
open Monoid CommMonoid


class CommGroup (α : Type) [Zero α] [Add α] [Neg α] [CommMonoid α] where
  add_neg : ∀(a : α), a + (-a) = zero

namespace CommGroup

  open Monoid CommMonoid
  variable {α : Type} [Zero α] [Add α] [Neg α] [CommMonoid α] [CommGroup α]

  -- @[default_instance, reducible] instance : Sub α where
  --   sub := fun a b => a + (-b)

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

  theorem sub_zero (a : α) : a - zero = a := by
    rw [neg_zero, add_zero]

  theorem neg_nonzero {a : α} : a ≠ zero → -a ≠ zero :=
    fun h h' => h (neg_inj ((neg_zero (α:=α)).substr h'))

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

  omit [Zero α] in
  theorem add_neg_eq_sub {a b : α} : a + -b = a - b := rfl

  omit [Zero α] in
  theorem sub_eq_add_neg : ∀(a b : α), a - b = a + (-b) := fun _ _ => rfl

  theorem eq_of_sub_eq_zero : ∀(a b : α), a - b = zero → a = b := by
    intro a b h;
    rw [←add_zero a, ←neg_add b, ←add_assoc, add_neg_eq_sub, h, zero_add]

  omit [CommGroup α] in
  theorem add_sub_assoc : ∀(a b c : α), (a + b) - c = a + (b - c) :=
    fun _ _ c => add_assoc _ _ (-c)

  theorem eq_add_of_sub_eq {a b c : α} : a - b = c → a = c + b := by
    intro h
    rw [←add_zero a, ←neg_add b, ←add_assoc, add_neg_eq_sub, h]

  theorem eq_sub_right_of_add_eq {a b c : α} : a + b = c → a = c - b := by
    intro h
    rw [←add_zero a, ←add_neg b, ←add_assoc, add_neg_eq_sub, h]

  theorem eq_sub_left_of_add_eq {a b c : α} : a + b = c → b = c - a := by
    intro h
    rw [←zero_add b, ←neg_add a, add_assoc, add_comm, h]

  theorem neg_sum : ∀(a b : α), -(a + b) = -a + -b := by
    intro a b
    rw [←add_zero (-a + _), ←add_neg (a + b), ←add_assoc, ←add_assoc, add_right_comm (-a), neg_add, zero_add, neg_add, zero_add]

  theorem neg_sub : ∀(a b : α), -(a - b) = b - a := by
    intro a b
    simp only [neg_sum, neg_neg, add_comm]

  theorem sub_add_assoc : ∀(a b c : α), (a - b) + c = a - (b - c) := by
    intros;simp only [neg_sum, neg_neg, add_assoc]

  omit [CommGroup α] in
  theorem add_sub_right_comm : ∀(a b c : α), a + b - c = a - c + b :=
    fun _ _ _ => add_right_comm _ _ _

  omit [CommGroup α] in
  theorem sub_add_right_comm : ∀(a b c : α), a - b + c = a + c - b :=
    fun _ _ _ => add_right_comm _ _ _

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

end my
