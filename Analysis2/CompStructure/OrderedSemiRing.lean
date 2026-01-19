import Analysis2.Structure.SemiRing
import Analysis2.CompStructure.OrderedCommMonoid
noncomputable section
namespace my
open Classical
open Comp
open Zero One
open Monoid CommMonoid SemiRing
open OrderedMonoid OrderedCommMonoid


class OrderedSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [SemiRing α] [OrderedCommMonoid α] where
  mul_le_mul_of_nonneg_right {a b c : α} : a ≤ b → zero ≤ c → a * c ≤ b * c
  mul_le_mul_of_nonneg_left {a b c : α} : a ≤ b → zero ≤ c → c * a ≤ c * b
  zero_le_one : (zero : α) ≤ one -- WLOG

namespace OrderedSemiRing

  open Monoid CommMonoid SemiRing
  open OrderedMonoid OrderedCommMonoid
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [SemiRing α] [OrderedCommMonoid α] [OrderedSemiRing α]

  theorem zero_lt_one : (zero : α) < one := lt_of_le_ne zero_le_one zero_ne_one

  theorem mul_nonneg {a b : α} : zero ≤ a → zero ≤ b → zero ≤ a * b :=
    fun h h' => (zero_mul _).subst (motive:=(·≤_*_)) (mul_le_mul_of_nonneg_right h h')

  theorem mul_nonneg_nonneg_is_nonneg {a b : α} : zero ≤ a → zero ≤ b → zero ≤ a * b :=
    mul_nonneg

  theorem mul_nonneg_pos_is_nonneg {a b : α} : zero ≤ a → zero < b → zero ≤ a * b :=
    fun h h' => (mul_nonneg h (le_of_lt h'))

  theorem mul_pos_nonneg_is_nonneg {a b : α} : zero < a → zero ≤ b → zero ≤ a * b :=
    fun h => mul_nonneg (le_of_lt h)

  theorem mul_pos_pos_is_nonneg {a b : α} : zero < a → zero < b → zero ≤ a * b :=
    fun h h' => (mul_nonneg (le_of_lt h) (le_of_lt h'))

  theorem mul_nonneg_nonpos_is_nonpos {a b : α} : zero ≤ a → b ≤ zero → a * b ≤ zero :=
    fun h h' => (mul_zero a) ▸ mul_le_mul_of_nonneg_left h' h

  theorem mul_pos_nonpos_is_nonpos {a b : α} : zero < a → b ≤ zero → a * b ≤ zero :=
    fun h h' => (mul_nonneg_nonpos_is_nonpos (le_of_lt h) h')

  theorem mul_nonneg_neg_is_nonpos {a b : α} : zero ≤ a → b < zero → a * b ≤ zero :=
    fun h h' => (mul_nonneg_nonpos_is_nonpos h (le_of_lt h'))

  theorem mul_pos_neg_is_nonpos {a b : α} : zero < a → b < zero → a * b ≤ zero :=
    fun h h' => (mul_nonneg_nonpos_is_nonpos (le_of_lt h) (le_of_lt h'))

  theorem mul_nonpos_nonneg_is_nonpos {a b : α} : a ≤ zero → zero ≤ b → a * b ≤ zero :=
    fun h h' => (zero_mul b) ▸ mul_le_mul_of_nonneg_right h h'

  theorem mul_nonpos_pos_is_nonpos {a b : α} : a ≤ zero → zero < b → a * b ≤ zero :=
    fun h h' => (mul_nonpos_nonneg_is_nonpos h (le_of_lt h'))

  theorem mul_neg_nonneg_is_nonpos {a b : α} : a < zero → zero ≤ b → a * b ≤ zero :=
    fun h h' => (mul_nonpos_nonneg_is_nonpos (le_of_lt h) h')

  theorem mul_neg_pos_is_nonpos {a b : α} : a < zero → zero < b → a * b ≤ zero :=
    fun h h' => (mul_nonpos_nonneg_is_nonpos (le_of_lt h) (le_of_lt h'))

  theorem mul_le_mul_of_pos_right {a b c : α} : a ≤ b → zero < c → a * c ≤ b * c :=
    fun h h' => mul_le_mul_of_nonneg_right h (le_of_lt h')

  theorem mul_le_mul_of_pos_left {a b c : α} : a ≤ b → zero < c → c * a ≤ c * b :=
    fun h h' => mul_le_mul_of_nonneg_left h (le_of_lt h')

  theorem lt_of_mul_lt_mul_pos_left {a b c : α} : c * a < c * b → zero < c → a < b :=
    fun h h' => byContradiction fun h'' => (not_lt_of_le (mul_le_mul_of_pos_left (le_of_not_lt h'') h')) h

  theorem lt_of_mul_lt_mul_pos_right {a b c : α} : a * c < b * c → zero < c → a < b :=
    fun h h' => byContradiction fun h'' => (not_lt_of_le (mul_le_mul_of_pos_right (le_of_not_lt h'') h')) h

  theorem pos_of_mul_pos_left {a b : α} : zero < a * b → b > zero → zero < a :=
    fun h => lt_of_mul_lt_mul_pos_right ((zero_mul b).substr h)

  theorem pos_of_mul_pos_right {a b : α} : zero < a * b → a > zero → zero < b :=
    fun h => lt_of_mul_lt_mul_pos_left ((mul_zero a).substr h)

  theorem le_of_mul_nonneg_nonneg_le_le {a b c d : α} : zero ≤ a → zero ≤ c → a ≤ b → c ≤ d → a * c ≤ b * d :=
    fun ha hc h h' => le_of_le_le (mul_le_mul_of_nonneg_right h hc) (mul_le_mul_of_nonneg_left h' (le_of_le_le ha h))

  theorem le_of_mul_pos_nonneg_le_le {a b c d : α} : zero < a → zero ≤ c → a ≤ b → c ≤ d → a * c ≤ b * d :=
    fun ha hc h h' => le_of_mul_nonneg_nonneg_le_le (le_of_lt ha) hc h h'

  theorem le_of_mul_nonneg_pos_le_le {a b c d : α} : zero ≤ a → zero < c → a ≤ b → c ≤ d → a * c ≤ b * d :=
    fun ha hc h h' => le_of_mul_nonneg_nonneg_le_le ha (le_of_lt hc) h h'

  theorem le_of_mul_pos_pos_le_le {a b c d : α} : zero < a → zero < c → a ≤ b → c ≤ d → a * c ≤ b * d :=
    fun ha hc h h' => le_of_mul_nonneg_nonneg_le_le (le_of_lt ha) (le_of_lt hc) h h'

end OrderedSemiRing



end my
