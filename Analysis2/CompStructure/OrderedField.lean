import Analysis2.Structure.Field
import Analysis2.CompStructure.OrderedCommRing
noncomputable section
namespace my
open Classical
open Comp
open Zero One Abs
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing' Field
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing OrderedCommRing'


class OrderedField (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] where


namespace OrderedField

  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommGroup CommRing CommRing'
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing OrderedCommGroup OrderedCommRing OrderedCommRing'
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] [Field α]

  @[default_instance] instance : OrderedCommRing' α where

  theorem inv_pos_is_pos {a : α} : (h : zero < a) → zero < ⟨a, ne_of_gt h⟩⁻¹ :=
    fun h => (neg_or_eq_or_pos ⟨a,ne_of_gt h⟩⁻¹).elim
      (fun h' => ((not_lt_of_le zero_le_one) (mul_inv_cancel (ne_of_gt h) ▸ mul_pos_neg_is_neg h h')).elim)
      (·.resolve_left (inv_nonzero (ne_of_gt h)))

  theorem inv_pos_is_nonneg {a : α} : (h : zero < a) → zero ≤ ⟨a, ne_of_gt h⟩⁻¹ :=
    fun h => le_of_lt (inv_pos_is_pos h)

  theorem inv_neg_is_neg {a : α} : (h : a < zero) → ⟨a, ne_of_lt h⟩⁻¹ < zero :=
    fun h => neg_pos_iff_neg.mp (inv_neg a (ne_of_lt h) ▸ inv_pos_is_pos (neg_neg_is_pos h))

  theorem inv_neg_is_nonpos {a : α} : (h : a < zero) → ⟨a, ne_of_lt h⟩⁻¹ ≤ zero :=
    fun h => le_of_lt (inv_neg_is_neg h)

  theorem inv_ge_of_pos_le {a b : α} (h : zero < a) (h' : a ≤ b) : ⟨a, ne_of_gt h⟩⁻¹ ≥ ⟨b, ne_of_lt_le' h h'⟩⁻¹ := by
    refine' le_of_mul_le_mul_pos_left _ (mul_pos h (lt_of_lt_le h h'))
    rw [mul_mul_inv_cancel_right, mul_mul_inv_cancel_left1]
    exact h'

  theorem inv_gt_of_pos_lt {a b : α} (h : zero < a) (h' : a < b) : ⟨a, ne_of_gt h⟩⁻¹ > ⟨b, ne_of_lt_lt' h h'⟩⁻¹ := by
    refine' lt_of_mul_lt_mul_pos_left _ (mul_pos h (lt_of_lt_lt h h'))
    rw [mul_mul_inv_cancel_right, mul_mul_inv_cancel_left1]
    exact h'

  theorem inv_ge_of_pos_lt {a b : α} (h : zero < a) (h' : a < b) : ⟨a, ne_of_gt h⟩⁻¹ ≥ ⟨b, ne_of_lt_lt' h h'⟩⁻¹ :=
    le_of_lt (inv_gt_of_pos_lt h h')

  theorem pos_ge_of_inv_le {a b : α} (ha : zero < a) (hb : zero < b) (h : ⟨a, ne_of_gt ha⟩⁻¹ ≤ ⟨b, ne_of_gt hb⟩⁻¹) : a ≥ b := by
    rw [←inv_inv (ne_of_gt ha), ← inv_inv (ne_of_gt hb)]
    exact inv_ge_of_pos_le (inv_pos_is_pos ha) h

  theorem pos_gt_of_inv_lt {a b : α} (ha : zero < a) (hb : zero < b) (h : ⟨a, ne_of_gt ha⟩⁻¹ < ⟨b, ne_of_gt hb⟩⁻¹) : a > b := by
    rw [←inv_inv (ne_of_gt ha), ← inv_inv (ne_of_gt hb)]
    exact inv_gt_of_pos_lt (inv_pos_is_pos ha) h

  theorem pos_ge_of_inv_lt {a b : α} (ha : zero < a) (hb : zero < b) (h : ⟨a, ne_of_gt ha⟩⁻¹ < ⟨b, ne_of_gt hb⟩⁻¹) : a ≥ b :=
    le_of_lt (pos_gt_of_inv_lt ha hb h)


  section num
  -- open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommGroup CommRing CommRing'
  -- open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing OrderedCommGroup OrderedCommRing OrderedCommRing'
    variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] [CommRing α] [OrderedCommRing α]

    set_option linter.unusedSectionVars false
    def two : α := one + one
    def three : α := one + one + one
    theorem two_pos : (zero : α) < two := pos_add_pos_is_pos zero_lt_one zero_lt_one
    theorem two_nonneg : (zero : α) ≤ two := le_of_lt two_pos
    theorem two_nonzero : two ≠ (zero : α) := ne_of_gt two_pos
    theorem three_pos : (zero : α) < three := pos_add_pos_is_pos two_pos zero_lt_one
    theorem three_nonneg : (zero : α) ≤ three := le_of_lt three_pos
    theorem three_nonzero : three ≠ (zero : α) := ne_of_gt three_pos
    theorem one_lt_two : (one : α) < two := add_zero one (α:=α) ▸ add_lt_add_left one zero_lt_one
    theorem two_lt_three : (two:α) < three := add_zero (α:=α) two ▸ add_lt_add_left two zero_lt_one
    theorem one_lt_three : (one:α) < three := lt_of_lt_lt one_lt_two two_lt_three
    theorem one_le_two : (one:α) ≤ two := le_of_lt one_lt_two
    theorem two_le_three : (two:α) ≤ three := le_of_lt two_lt_three
    theorem one_le_three : (one:α) ≤ three := le_of_lt one_lt_three

    theorem add_eq_mul_two (a : α) : a + a = a * two := by
      rw [two,mul_add,mul_one]
    theorem one_plus_one_eq_two : one + one = two := rfl
    theorem two_plus_one_eq_three : two + one = three := rfl
    theorem one_plus_two_eq_three : (one:α) + two = three := by
      rw [add_comm];rfl

    variable [Inv α] [CommRing α] [Field α]
    def one_half : α := ⟨two, two_nonzero⟩⁻¹
    def one_third : α := ⟨three, three_nonzero⟩⁻¹
    theorem add_one_half : one_half + one_half = (one : α) := eq_of_eq_eq (add_eq_mul_two one_half) (inv_mul_cancel two_nonzero)
    theorem one_half_pos : (zero : α) < one_half := inv_pos_is_pos two_pos
    theorem one_half_nonneg : (zero : α) ≤ one_half := le_of_lt one_half_pos
    theorem one_half_nonzero : one_half ≠ (zero : α) := ne_of_gt one_half_pos
    theorem one_half_lt_one : one_half < (one : α) := inv_of_one (α:=α) ▸ inv_gt_of_pos_lt zero_lt_one one_lt_two
    theorem one_third_pos : (zero : α) < one_third := inv_pos_is_pos three_pos
    theorem one_third_nonneg : (zero : α) ≤ one_third := le_of_lt one_third_pos
    theorem one_third_nonzero : one_third ≠ (zero : α) := ne_of_gt one_third_pos
    theorem one_third_lt_one : one_third < (one : α) := inv_of_one (α:=α) ▸ inv_gt_of_pos_lt zero_lt_one one_lt_three
    theorem one_third_lt_one_half : one_third < (one_half : α) := inv_gt_of_pos_lt two_pos two_lt_three

    def half : α → α :=
      fun a => a * one_half
    theorem twice_half_cancel (a : α) : two * half a = a := mul_mul_inv_cancel_left2 two_nonzero
    theorem half_twice_cancel (a : α) : half (a * two) = a := mul_mul_inv_cancel_right two_nonzero
    theorem half_twice_cancel' (a : α) : (half a) * two = a := mul_inv_mul_cancel_right two_nonzero
    theorem add_half (a : α) : (half a) + (half a) = a :=
      mul_add a one_half one_half ▸ add_one_half (α:=α) ▸ mul_one a
    theorem add_half_half (a b : α) : half (a + b) = half a + half b :=
      add_mul _ _ _
    theorem half_of_pos_is_pos {a : α} : zero < a → zero < half a :=
      (mul_pos · one_half_pos)
    theorem half_of_pos_is_nonzero {a : α} : zero < a → half a ≠ zero :=
      fun h => ne_of_gt (half_of_pos_is_pos h)
    theorem half_of_nonzero_is_nonzero {a : α} : a ≠ zero → half a ≠ zero := by
      intro h h';replace h':=congrArg (two*·) h';simp only[mul_zero,twice_half_cancel] at h';exact h h'
    theorem half_of_pos_lt_self {a : α} : zero < a → half a < a :=
      fun h => lt_of_lt_eq (mul_lt_mul_of_pos_left one_half_lt_one h) (mul_one a)


    set_option linter.unusedSectionVars true

  end num


end OrderedField


end my
