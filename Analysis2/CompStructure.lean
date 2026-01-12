import Analysis2.Logic
import Analysis2.Operator
import Analysis2.Structure
import Analysis2.Comp
noncomputable section
namespace my
open Classical
open Comp
open Zero One Abs

--definition that doesn't require abs to make sence
section abs
  variable {α : Type} [Zero α] [Neg α] [Comp α]

  private def _abs : α → α :=
      fun a => (le_or_gt zero a).elim' (fun _ => a) (fun _ => -a)

  @[default_instance] instance : Abs α where
    abs := _abs

  theorem abs_def {a : α} : abs a = _abs a := rfl

  theorem abs_of_pos {a : α} : zero < a → abs a = a :=
    fun h => (le_or_gt zero a).elim'_spec (p:=(·=a)) (fun _ => rfl) (fun h' => (not_lt_of_lt h' h).elim)

  theorem abs_of_neg {a : α} : a < zero → abs a = -a :=
    fun h => (le_or_gt zero a).elim'_spec (p:=(·=-a)) (fun h' => (not_lt_of_le h' h).elim) (fun _ => rfl)

  theorem abs_of_nonneg {a : α} : zero ≤ a → abs a = a :=
    fun h => (le_or_gt zero a).elim'_spec (p:=(·=a)) (fun _ => rfl) (fun h' => (not_lt_of_le h h').elim)

  theorem abs_of_zero : abs zero = (zero : α) := abs_of_nonneg (le_refl zero)

end abs



class OrderedMonoid (α : Type) [Zero α] [Add α] [Monoid α] [Comp α] where
  add_le_add_left {a b : α} (c : α) : a ≤ b → c + a ≤ c + b
  add_le_add_right {a b : α} (c : α) : a ≤ b → a + c ≤ b + c


namespace OrderedMonoid

  variable {α : Type} [Zero α] [Add α] [Monoid α] [Comp α] [OrderedMonoid α]

  -- theorem add_lt_add_left {a b : α} (c : α) : a < b → c + a < c + b := by
  --   intro h h'
  --   have := ne_of_lt h
  --   have : c+a = c+b := le_antisymm _ _ (add_le_add_left c (le_of_lt h)) h'
    -- have := (le_or_ge a b).resolve_right h

  -- theorem add_lt_add_right {a b : α} (c : α) : a < b → a + c < b + c := by

  -- theorem add_le_add_iff_right {a b : α} : ∀(c : α), a + c ≤ b + c ↔ a ≤ b := by
  --   intro c
  --   refine' Iff.intro _ (add_le_add_right · c)
  --   intro h
  --   apply byContradiction
  --   intro h'
  --   have := (le_or_gt a b).resolve_left h'
  --   -- intro h'

  -- theorem add_le_add_iff_left {a b : α} : ∀(c : α), c + a ≤ c + b ↔ a ≤ b := sorry

  -- impossible, see test1

end OrderedMonoid



class OrderedCommMonoid (α : Type) [Zero α] [Add α] [Comp α] [CommMonoid α] where
  _add_le_add_left {a b : α} (c : α) : a ≤ b → c + a ≤ c + b

namespace OrderedCommMonoid

  open Monoid CommMonoid
  open OrderedMonoid
  variable {α : Type} [Zero α] [Add α] [Comp α] [CommMonoid α] [OrderedCommMonoid α]

  theorem _add_le_add_right {a b : α} (c : α) : a ≤ b → a + c ≤ b + c := by
    intro h
    simp only [add_comm _ c, _add_le_add_left c h]

  @[default_instance] instance : OrderedMonoid α := ⟨_add_le_add_left, _add_le_add_right⟩

end OrderedCommMonoid



class OrderedCommGroup (α : Type) [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α]

namespace OrderedCommGroup

  open Monoid CommMonoid CommGroup
  open OrderedMonoid OrderedCommMonoid
  variable {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α]

  theorem neg_le_neg_of_le {a b : α} : a ≤ b → -a ≥ -b := by
    intro h
    replace h := add_le_add_right (-a + -b) h
    rw [←add_assoc, add_neg, zero_add, add_left_comm, add_neg, add_zero] at h
    exact h

  theorem le_of_neg_le_neg {a b : α} : -b ≤ -a → a ≤ b := by
    intro h
    rw [←neg_neg a, ← neg_neg b]
    exact neg_le_neg_of_le h

  theorem neg_le_neg_iff {a b : α} : -b ≤ -a ↔ a ≤ b :=
    ⟨le_of_neg_le_neg, neg_le_neg_of_le⟩

  theorem le_of_add_le_add_right {a b c : α} : a + c ≤ b + c → a ≤ b := by
    intro h
    rw [←add_zero a, ←add_zero b, ←add_neg c, ←add_assoc, ←add_assoc]
    exact add_le_add_right (-c) h

  theorem le_of_add_le_add_left {a b c : α} : c + a ≤ c + b → a ≤ b := by
    intro h
    rw [←zero_add a, ←zero_add b, ←neg_add c, add_assoc, add_assoc]
    exact add_le_add_left (-c) h

  theorem add_le_add_right_iff {a b c : α} : a + c ≤ b + c ↔ a ≤ b :=
    ⟨le_of_add_le_add_right, add_le_add_right _⟩

  theorem add_le_add_left_iff {a b c : α} : c + a ≤ c + b ↔ a ≤ b :=
    ⟨le_of_add_le_add_left, add_le_add_left _⟩

  theorem sub_nonneg_of_le {a b : α} : a ≤ b → zero ≤ b - a := by
    intro h
    rw [←add_neg a, sub_eq_add_neg]
    exact add_le_add_right (-a) h

  theorem le_of_sub_noneg {a b : α} : zero ≤ b - a → a ≤ b := by
    intro h
    replace h := add_le_add_right a h
    rw [zero_add, sub_add_cancel] at h
    exact h

  theorem sub_nonneg_iff {a b : α} : zero ≤ b - a ↔ a ≤ b :=
    ⟨le_of_sub_noneg, sub_nonneg_of_le⟩

  theorem add_lt_add_left {a b : α} : ∀(c : α), a < b → c + a < c + b :=
    fun _ => contrapos le_of_add_le_add_left

  theorem add_lt_add_right {a b : α} : ∀(c : α), a < b → a + c < b + c :=
    fun _ => contrapos le_of_add_le_add_right

  theorem neg_lt_neg_of_lt {a b : α} : a < b → -a > -b := by
    intro h
    replace h := add_lt_add_right (-a + -b) h
    rw [←add_assoc, add_neg, zero_add, add_left_comm, add_neg, add_zero] at h
    exact h

  theorem lt_of_neg_lt_neg {a b : α} : -b < -a → a < b := by
    intro h
    rw [←neg_neg a, ← neg_neg b]
    exact neg_lt_neg_of_lt h

  theorem neg_lt_neg_iff {a b : α} : -b < -a ↔ a < b :=
    ⟨lt_of_neg_lt_neg, neg_lt_neg_of_lt⟩

  theorem sub_pos_of_lt {a b : α} : a < b → zero < b - a := by
    intro h
    rw [←add_neg a, sub_eq_add_neg]
    exact add_lt_add_right (-a) h

  theorem lt_of_sub_pos {a b : α} : zero < b - a → a < b := by
    intro h
    replace h := add_lt_add_right a h
    rw [zero_add, sub_add_cancel] at h
    exact h

  theorem sub_pos_iff {a b : α} : zero < b - a ↔ a < b :=
    ⟨lt_of_sub_pos, sub_pos_of_lt⟩

  theorem neg_nonneg_is_nonpos {a : α} : zero ≤ a → -a ≤ zero := by
    intro;rwa [←neg_zero, neg_le_neg_iff]

  theorem neg_nonpos_is_nonneg {a : α} : a ≤ zero → zero ≤ -a := by
    intro;rwa [←neg_zero, neg_le_neg_iff]

  theorem neg_pos_is_neg {a : α} : zero < a → -a < zero := by
    intro;rwa [←neg_zero, neg_lt_neg_iff]

  theorem neg_pos_is_nonpos {a : α} : zero < a → -a ≤ zero :=
    fun h => le_of_lt (neg_pos_is_neg h)

  theorem neg_neg_is_pos {a : α} : a < zero → zero < -a := by
    intro;rwa [←neg_zero, neg_lt_neg_iff]

  theorem neg_neg_is_nonneg {a : α} : a < zero → zero ≤ -a :=
    fun h => le_of_lt (neg_neg_is_pos h)

  theorem abs_nonneg : ∀(a : α), zero ≤ abs a :=
    fun a => (le_or_gt zero a).elim'_spec id neg_neg_is_nonneg

  set_option linter.unusedSectionVars false in
  theorem abs_of_nonpos {a : α} : a ≤ zero → abs a = -a :=
    fun h => (lt_or_eq_of_le h).elim abs_of_neg (fun h => (by rw [h,abs_of_zero,neg_zero]))

  set_option linter.unusedSectionVars false in
  theorem abs_of_pos_is_pos {a : α} : zero < a → zero < abs a :=
    fun h => (abs_of_pos h).substr h

  theorem abs_of_neg_is_pos {a : α} : a < zero → zero < abs a :=
    fun h => (abs_of_neg h).substr neg_neg_is_pos h

  theorem abs_of_nonzero_is_pos {a : α} : a ≠ zero → abs a > zero :=
    fun h => (lt_or_eq_or_gt a zero).elim abs_of_neg_is_pos (·.elim (fun h' => (h h').elim) abs_of_pos_is_pos)

  theorem eq_zero_of_abs_eq_zero {a : α} : abs a = zero → a = zero :=
    fun h => (eq_or_lt_or_gt a zero).elim (id) (fun h' => False.elim (h'.elim
      (fun h'' => ne_of_lt (abs_of_neg_is_pos h'') h.symm)
      (fun h'' => ne_of_lt (abs_of_pos_is_pos h'') h.symm)))

  theorem abs_eq_zero_iff {a : α} : abs a = zero ↔ a = zero :=
    ⟨eq_zero_of_abs_eq_zero, (·.substr abs_of_zero)⟩


end OrderedCommGroup



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

end OrderedSemiRing



class OrderedCommSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [CommSemiRing α] [OrderedCommMonoid α] where
  _mul_le_mul_of_nonneg_right {a b c : α} : a ≤ b → zero ≤ c → a * c ≤ b * c
  _zero_le_one : (zero : α) ≤ one -- WLOG


namespace OrderedCommSemiRing

  open CommSemiRing
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [CommSemiRing α] [OrderedCommMonoid α] [OrderedCommSemiRing α]

  theorem _mul_le_mul_of_nonneg_left {a b c : α} : a ≤ b → c ≥ zero → c * a ≤ c * b := by
    intro h h'
    simp only [mul_comm]
    exact _mul_le_mul_of_nonneg_right h h'

  @[default_instance] instance : OrderedSemiRing α := ⟨_mul_le_mul_of_nonneg_right, _mul_le_mul_of_nonneg_left, _zero_le_one⟩

end OrderedCommSemiRing



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

  -- theorem mul_neg_neg_is_pos {a b : α} : a < zero → b < zero → a * b > zero := by
  --   intro h h';rw [←mul_zero a];exact mul_lt_mul_of_neg_left h' h

  theorem mul_neg_pos_is_neg {a b : α} : a < zero → b > zero → a * b < zero := by
    intro h h';rw [←zero_mul b];exact mul_lt_mul_of_pos_right h h'
  --  by
  --   intro h h'
  --   rw [←zero_mul b] at h
  --   exact le_of_mul_le_mul_pos_right h h'

end OrderedCommRing'



class OrderedField (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] where


namespace OrderedField

  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommGroup CommRing CommRing'
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing OrderedCommGroup OrderedCommRing OrderedCommRing'
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [Comp α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommRing α] [Field α]

  @[default_instance] instance : OrderedCommRing' α where


end OrderedField


end my
