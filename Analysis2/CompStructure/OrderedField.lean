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
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] [Field α]

  @[default_instance] instance : OrderedCommRing' α where

  theorem inv_pos_is_pos {a : α} : (h : zero < a) → zero < ⟨a, ne_of_gt h⟩⁻¹ :=
    fun h => (neg_or_eq_or_pos ⟨a,ne_of_gt h⟩⁻¹).elim
      (fun h' => ((not_lt_of_le zero_le_one) (mul_inv_cancel a (ne_of_gt h) ▸ mul_pos_neg_is_neg h h')).elim)
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

end OrderedField


end my
