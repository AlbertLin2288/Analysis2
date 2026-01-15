import Analysis2.Comp
import Analysis2.Structure.Monoid
noncomputable section
namespace my
open Classical
open Comp
open Zero One
open Monoid


section

  variable {α : Type} [Zero α] [Comp α]

  theorem nonneg_or_nonpos (a : α) : zero ≤ a ∨ a ≤ zero :=
    le_or_ge zero a

  theorem nonneg_or_neg (a : α) : zero ≤ a ∨ a < zero :=
    le_or_gt zero a

  theorem nonpos_or_nonneg (a : α) : a ≤ zero ∨ zero ≤ a :=
    le_or_ge a zero

  theorem nonpos_or_pos (a : α) : a ≤ zero ∨ zero < a :=
    le_or_gt a zero

  theorem pos_or_nonpos (a : α) : zero < a ∨ a ≤ zero :=
    lt_or_ge zero a

  theorem pos_or_zero_or_neg (a : α) : zero < a ∨ a = zero ∨ a < zero :=
    gt_or_eq_or_lt a zero

  theorem neg_or_nonneg (a : α) : a < zero ∨ zero ≤ a :=
    lt_or_ge a zero

  theorem neg_or_eq_or_pos (a : α) : a < zero ∨ a = zero ∨ zero < a :=
    lt_or_eq_or_gt a zero


end


class OrderedMonoid (α : Type) [Zero α] [Add α] [Monoid α] [Comp α] where
  add_le_add_left {a b : α} (c : α) : a ≤ b → c + a ≤ c + b
  add_le_add_right {a b : α} (c : α) : a ≤ b → a + c ≤ b + c


namespace OrderedMonoid

  variable {α : Type} [Zero α] [Add α] [Monoid α] [Comp α] [OrderedMonoid α]


  theorem le_of_add_le_le {a b c d : α} : a ≤ b → c ≤ d → a + c ≤ b + d :=
    fun h h' => le_trans _ _ _ (add_le_add_right c h) (add_le_add_left b h')

  theorem le_of_add_lt_le {a b c d : α} : a < b → c ≤ d → a + c ≤ b + d :=
    fun h h' => le_of_add_le_le (le_of_lt h) h'

  theorem le_of_add_le_lt {a b c d : α} : a ≤ b → c < d → a + c ≤ b + d :=
    fun h h' => le_of_add_le_le h (le_of_lt h')

  theorem le_of_add_lt_lt {a b c d : α} : a < b → c < d → a + c ≤ b + d :=
    fun h h' => le_of_add_le_le (le_of_lt h) (le_of_lt h')

  theorem nonneg_add_nonneg_is_nonneg {a b : α} : zero ≤ a → zero ≤ b → zero ≤ a + b :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_le_le h h'

  theorem nonneg_add_pos_is_nonneg {a b : α} : zero ≤ a → zero < b → zero ≤ a + b :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_le_lt h h'

  theorem pos_add_nonneg_is_nonneg {a b : α} : zero < a → zero ≤ b → zero ≤ a + b :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_lt_le h h'

  theorem pos_add_pos_is_nonneg {a b : α} : zero < a → zero < b → zero ≤ a + b :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_lt_lt h h'

  theorem nonpos_add_nonpos_is_nonpos {a b : α} : a ≤ zero → b ≤ zero → a + b ≤ zero :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_le_le h h'

  theorem nonpos_add_neg_is_nonpos {a b : α} : a ≤ zero → b < zero → a + b ≤ zero :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_le_lt h h'

  theorem neg_add_nonpos_is_nonpos {a b : α} : a < zero → b ≤ zero → a + b ≤ zero :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_lt_le h h'

  theorem neg_add_neg_is_nonpos {a b : α} : a < zero → b < zero → a + b ≤ zero :=
    fun h h' => (add_zero (zero:α)) ▸ le_of_add_lt_lt h h'


end OrderedMonoid

end my
