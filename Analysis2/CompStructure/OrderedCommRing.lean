import Analysis2.Structure.CommRing
import Analysis2.CompStructure.OrderedCommGroup
import Analysis2.CompStructure.OrderedCommSemiRing
noncomputable section
namespace my
open Classical
open Comp
open Zero One Abs
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing'
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing



class OrderedCommRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α]
  [OrderedCommMonoid α] [OrderedCommGroup α] where
  _mul_nonneg {a b : α} : zero ≤ a → zero ≤ b → zero ≤ a * b
  _zero_le_one : (zero : α) ≤ one -- WLOG

namespace OrderedCommRing

  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommGroup CommRing
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing OrderedCommGroup
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α]

  theorem _mul_le_mul_of_nonneg_right {a b c : α} : a ≤ b → zero ≤ c → a * c ≤ b * c := by
    intro h hc
    rw [←sub_nonneg_iff] at h |-
    rw [←sub_mul]
    exact _mul_nonneg h hc

  @[default_instance] instance : OrderedCommSemiRing α := ⟨_mul_le_mul_of_nonneg_right, _zero_le_one⟩

  theorem mul_nonpos_nonpos_is_nonneg {a b : α} : a ≤ zero → b ≤ zero → zero ≤ a * b :=
    fun h h' => neg_nonpos_iff_nonneg.mp (mul_neg_left (a:=a) ▸ mul_nonneg_nonpos_is_nonpos (neg_nonpos_is_nonneg h) h')

  theorem mul_nonpos_neg_is_nonneg {a b : α} : a ≤ zero → b < zero → zero ≤ a * b :=
    fun h h' => (mul_nonpos_nonpos_is_nonneg h (le_of_lt h'))

  theorem mul_neg_nonpos_is_nonneg {a b : α} : a < zero → b ≤ zero → zero ≤ a * b :=
    fun h h' => (mul_nonpos_nonpos_is_nonneg (le_of_lt h) h')

  theorem mul_neg_neg_is_nonneg {a b : α} : a < zero → b < zero → zero ≤ a * b :=
    fun h h' => (mul_nonpos_nonpos_is_nonneg (le_of_lt h) (le_of_lt h'))

  theorem abs_of_mul_eq_mul_abs {a b : α} : abs (a * b) = (abs a) * (abs b) :=
     Or.elim'_spec (h:=nonneg_or_neg a) (p:=(_=·*_))
      (fun h => Or.elim'_spec (h:=nonneg_or_neg b) (p:=(_=_*·))
        (fun h' => abs_of_nonneg (mul_nonneg_nonneg_is_nonneg h h'))
        (fun h' => @id (_=_*_) (mul_neg_right (a:=a) ▸ (abs_of_nonpos (mul_nonneg_neg_is_nonpos h h')))))
      (fun h => Or.elim'_spec (h:=nonneg_or_neg b) (p:=(_=_*·))
        (fun h'=> @id (_=_*_) (mul_neg_left (a:=a) ▸ abs_of_nonpos (mul_neg_nonneg_is_nonpos h h')))
        (fun h' => (mul_neg_both a b).substr (p:=(_=·)) (abs_of_nonneg (mul_neg_neg_is_nonneg h h'))))

    -- apply Or.elim'_spec (h:=nonneg_or_neg (a*b)) (p:=(·=abs a * abs b))



end OrderedCommRing



class OrderedCommRing' (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] where
  -- mul_eq_zero {a b : α} : a * b = zero → a = zero ∨ b = zero -- equivalent to mul_pos, see test2

namespace OrderedCommRing'

  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommGroup CommRing CommRing'
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing OrderedCommGroup OrderedCommRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] [OrderedCommRing' α]

  set_option linter.unusedSectionVars false in
  theorem mul_pos {a b : α} : a > zero → b > zero → a * b > zero :=
    fun ha hb => lt_of_le_ne (mul_nonneg (le_of_lt ha) (le_of_lt hb)) fun h => (mul_eq_zero h.symm).elim (ne_of_lt ha).symm (ne_of_lt hb).symm

  theorem mul_lt_mul_of_pos_right {a b c : α} : a < b → zero < c → a * c < b * c := by
    intro h h'
    rw [←sub_pos_iff] at h |-
    rw [←sub_mul]
    exact mul_pos h h'

  theorem mul_lt_mul_of_pos_left {a b c : α} : a < b → zero < c → c * a < c * b := by
    intro h h';simp only [mul_comm];exact mul_lt_mul_of_pos_right h h'

  theorem le_of_mul_le_mul_pos_left {a b c : α} : c * a ≤ c * b → zero < c → a ≤ b :=
    fun h h' => byContradiction fun h'' => (not_le_of_lt (mul_lt_mul_of_pos_left (lt_of_not_le h'') h')) h

  theorem le_of_mul_le_mul_pos_right {a b c : α} : a * c ≤ b * c → zero < c → a ≤ b := by
    intro h;simp only [mul_comm _ c] at h;exact le_of_mul_le_mul_pos_left h

  theorem mul_lt_mul_pos_right_iff {a b c : α} : zero < c → (a * c < b * c ↔ a < b) :=
    fun h => ⟨(lt_of_mul_lt_mul_pos_right · h), (mul_lt_mul_of_pos_right · h)⟩

  theorem mul_lt_mul_pos_left {a b c : α} : zero < c → (c * a < c * b ↔ a < b) :=
    fun h => ⟨(lt_of_mul_lt_mul_pos_left · h), (mul_lt_mul_of_pos_left · h)⟩

  theorem mul_le_mul_pos_left_iff {a b c : α} : zero < c → (c * a ≤ c * b ↔ a ≤ b) :=
    fun h => ⟨(le_of_mul_le_mul_pos_left · h), (mul_le_mul_of_pos_left · h)⟩

  theorem mul_le_mul_pos_right_iff {a b c : α} : zero < c → (a * c ≤ b * c ↔ a ≤ b) :=
    fun h => ⟨(le_of_mul_le_mul_pos_right · h), (mul_le_mul_of_pos_right · h)⟩

  theorem nonneg_of_mul_nonneg_left {a b : α} : zero ≤ a * b → b > zero → zero ≤ a :=
    fun h => le_of_mul_le_mul_pos_right ((zero_mul b).substr h)

  theorem nonneg_of_mul_nonneg_right {a b : α} : zero ≤ a * b → a > zero → zero ≤ b :=
    fun h => le_of_mul_le_mul_pos_left ((mul_zero a).substr h)

  theorem mul_pos_neg_is_neg {a b : α} : a > zero → b < zero → a * b < zero := by
    intro h h';rw [←mul_zero a];exact mul_lt_mul_of_pos_left h' h

  theorem mul_neg_neg_is_pos {a b : α} : a < zero → b < zero → a * b > zero :=
    fun h h' => lt_of_lt_eq (mul_pos (neg_neg_is_pos h) (neg_neg_is_pos h')) (mul_neg_both a b)

  theorem mul_neg_pos_is_neg {a b : α} : a < zero → b > zero → a * b < zero := by
    intro h h';rw [←zero_mul b];exact mul_lt_mul_of_pos_right h h'

  theorem lt_of_mul_nonneg_nonneg_lt_lt {a b c d : α} : zero ≤ a → zero ≤ c → a < b → c < d → a * c < b * d :=
    fun ha hc h h' => lt_of_le_lt (mul_le_mul_of_nonneg_right (le_of_lt h) hc) (mul_lt_mul_of_pos_left h' (lt_of_le_lt ha h))

  theorem lt_of_mul_nonneg_pos_lt_le {a b c d : α} : zero ≤ a → zero < c → a < b → c ≤ d → a * c < b * d :=
    fun ha hc h h' => lt_of_lt_le (mul_lt_mul_of_pos_right h hc) (mul_le_mul_of_pos_left h' (lt_of_le_lt ha h))

  theorem lt_of_mul_pos_nonneg_le_lt {a b c d : α} : zero < a → zero ≤ c → a ≤ b → c < d → a * c < b * d :=
    fun ha hc h h' => lt_of_le_lt (mul_le_mul_of_nonneg_right h hc) (mul_lt_mul_of_pos_left h' (lt_of_lt_le ha h))

end OrderedCommRing'


end my
