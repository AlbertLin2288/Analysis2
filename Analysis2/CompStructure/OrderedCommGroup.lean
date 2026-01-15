import Analysis2.Structure.CommGroup
import Analysis2.CompStructure.OrderedCommMonoid
noncomputable section
namespace my
open Classical
open Comp
open Zero One Abs
open Monoid CommMonoid CommGroup
open OrderedMonoid OrderedCommMonoid


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

  theorem abs_of_eq_zero_is_zero {a : α} : a = zero → abs a = zero :=
    (· ▸ abs_of_zero (α:=α))

end abs


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

  theorem le_neg_of_le_neg {a b : α} : a ≤ -b → b ≤ -a :=
    fun h => neg_neg b ▸ neg_le_neg_of_le h

  theorem neg_le_of_neg_le {a b : α} : -a ≤ b → -b ≤ a :=
    fun h => neg_neg a ▸ neg_le_neg_of_le h

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

  theorem le_of_sub_nonneg {a b : α} : zero ≤ b - a → a ≤ b := by
    intro h
    replace h := add_le_add_right a h
    rw [zero_add, sub_add_cancel] at h
    exact h

  theorem sub_nonneg_iff {a b : α} : zero ≤ b - a ↔ a ≤ b :=
    ⟨le_of_sub_nonneg, sub_nonneg_of_le⟩

  theorem sub_nonpos_of_le {a b : α} : a ≤ b → a - b ≤ zero :=
    (add_neg b ▸ add_le_add_right (-b) ·)

  theorem le_of_sub_nonpos {a b : α} : a - b ≤ zero → a ≤ b :=
    (zero_add b ▸ sub_add_cancel a b ▸ add_le_add_right b ·)

  theorem sub_nonpos_iff {a b : α} : a - b ≤ zero ↔ a ≤ b :=
    ⟨le_of_sub_nonpos, sub_nonpos_of_le⟩

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

  theorem lt_neg_of_lt_neg {a b : α} : a < -b → b < -a :=
    fun h => neg_neg b ▸ neg_lt_neg_of_lt h

  theorem neg_lt_of_neg_lt {a b : α} : -a < b → -b < a :=
    fun h => neg_neg a ▸ neg_lt_neg_of_lt h

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

  theorem neg_nonpos_iff_nonneg {a : α} : -a ≤ zero ↔ zero ≤ a :=
    ⟨(neg_neg a ▸ neg_nonpos_is_nonneg ·), neg_nonneg_is_nonpos⟩

  theorem neg_nonneg_iff_nonpos {a : α} : zero ≤ -a ↔ a ≤ zero :=
    ⟨(neg_neg a ▸ neg_nonneg_is_nonpos ·), neg_nonpos_is_nonneg⟩

  theorem neg_neg_iff_pos {a : α} : -a < zero ↔ zero < a :=
    ⟨(neg_neg a ▸ neg_neg_is_pos ·), neg_pos_is_neg⟩

  theorem neg_pos_iff_neg {a : α} : zero < -a ↔ a < zero :=
    ⟨(neg_neg a ▸ neg_pos_is_neg ·), neg_neg_is_pos⟩

  theorem lt_of_add_lt_le {a b c d : α} : a < b → c ≤ d → a + c < b + d :=
    fun h h' => lt_of_lt_le (add_lt_add_right c h) (add_le_add_left b h')

  theorem lt_of_add_le_lt {a b c d : α} : a ≤ b → c < d → a + c < b + d :=
    fun h h' => lt_of_le_lt (add_le_add_right c h) (add_lt_add_left b h')

  theorem lt_of_add_lt_lt {a b c d : α} : a < b → c < d → a + c < b + d :=
    fun h h' => lt_of_add_le_lt (le_of_lt h) h'

  theorem nonneg_add_pos_is_pos {a b : α} : zero ≤ a → zero < b → zero < a + b :=
    fun h h' => (add_zero (zero:α)) ▸ lt_of_add_le_lt h h'

  theorem pos_add_nonneg_is_pos {a b : α} : zero < a → zero ≤ b → zero < a + b :=
    fun h h' => (add_zero (zero:α)) ▸ lt_of_add_lt_le h h'

  theorem pos_add_pos_is_pos {a b : α} : zero < a → zero < b → zero < a + b :=
    fun h h' => (add_zero (zero:α)) ▸ lt_of_add_lt_lt h h'

  theorem nonpos_add_neg_is_neg {a b : α} : a ≤ zero → b < zero → a + b < zero :=
    fun h h' => (add_zero (zero:α)) ▸ lt_of_add_le_lt h h'

  theorem neg_add_nonpos_is_neg {a b : α} : a < zero → b ≤ zero → a + b < zero :=
    fun h h' => (add_zero (zero:α)) ▸ lt_of_add_lt_le h h'

  theorem neg_add_neg_is_neg {a b : α} : a < zero → b < zero → a + b < zero :=
    fun h h' => (add_zero (zero:α)) ▸ lt_of_add_lt_lt h h'

  theorem le_add_of_sub_right_le {a b c : α} : a - c ≤ b → a ≤ b + c :=
    fun h => sub_add_cancel a c ▸ add_le_add_right c h

  theorem le_add_of_sub_left_le {a b c : α} : a - b ≤ c → a ≤ b + c :=
    fun h => add_comm b c ▸ le_add_of_sub_right_le h

  theorem sub_right_le_of_le_add {a b c : α} : a ≤ b + c → a - c ≤ b :=
    fun h => add_sub_cancel b c ▸ add_le_add_right (-c) h

  theorem sub_left_le_of_le_add {a b c : α} : a ≤ b + c → a - b ≤ c :=
    fun h => sub_right_le_of_le_add (add_comm b c ▸ h)

  theorem sub_le_iff_le_add_left {a b c : α} : a - b ≤ c ↔ a ≤ b + c :=
    ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩

  theorem sub_le_iff_le_add_right {a b c : α} : a - c ≤ b ↔ a ≤ b + c :=
    ⟨le_add_of_sub_right_le, sub_right_le_of_le_add⟩

  theorem sub_le_of_sub_le {a b c : α} : a - b ≤ c → a - c ≤ b :=
    fun h => sub_right_le_of_le_add (le_add_of_sub_left_le h)

  theorem lt_add_of_sub_right_lt {a b c : α} : a - c < b → a < b + c :=
    fun h => sub_add_cancel a c ▸ add_lt_add_right c h

  theorem lt_add_of_sub_left_lt {a b c : α} : a - b < c → a < b + c :=
    fun h => add_comm b c ▸ lt_add_of_sub_right_lt h

  theorem sub_right_lt_of_lt_add {a b c : α} : a < b + c → a - c < b :=
    fun h => add_sub_cancel b c ▸ add_lt_add_right (-c) h

  theorem sub_left_lt_of_lt_add {a b c : α} : a < b + c → a - b < c :=
    fun h => sub_right_lt_of_lt_add (add_comm b c ▸ h)

  theorem sub_lt_iff_lt_add_left {a b c : α} : a - b < c ↔ a < b + c :=
    ⟨lt_add_of_sub_left_lt, sub_left_lt_of_lt_add⟩

  theorem sub_lt_iff_lt_add_right {a b c : α} : a - c < b ↔ a < b + c :=
    ⟨lt_add_of_sub_right_lt, sub_right_lt_of_lt_add⟩

  theorem sub_lt_of_sub_lt {a b c : α} : a - b < c → a - c < b :=
    fun h => sub_right_lt_of_lt_add (lt_add_of_sub_left_lt h)

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

  theorem abs_of_nonzero_is_nonzero {a : α} : a ≠ zero → abs a ≠ zero :=
    fun h => ne_of_gt (abs_of_nonzero_is_pos h)

  omit [Add α] in
  theorem nonzero_of_abs_nonzero {a : α} : abs a ≠ zero → a ≠ zero :=
    fun h h' => h (abs_of_eq_zero_is_zero h')

  theorem abs_nonzero_iff {a : α} : abs a ≠ zero ↔ a ≠ zero :=
    ⟨nonzero_of_abs_nonzero, abs_of_nonzero_is_nonzero⟩

  theorem abs_neg_eq_abs (a : α) : abs (-a) = abs a :=
    (le_or_gt zero a).elim'_spec (c:=α) (p:=(abs (-a)=·))
      (fun h => ((neg_neg a).subst (abs_of_nonpos (neg_nonneg_is_nonpos h))))
      (fun h => (abs_of_pos (neg_neg_is_pos h)))

  theorem self_le_abs_self (a : α) : a ≤ abs a :=
    (le_or_ge zero a).elim (fun h => le_of_eq (abs_of_nonneg h).symm) (le_trans _ _ _ · (abs_nonneg a))

  theorem self_le_abs_neg_self (a : α) : a ≤ abs (-a) :=
    (abs_neg_eq_abs a) ▸ (self_le_abs_self a)

  theorem neg_self_le_abs_self (a : α) : -a ≤ abs a :=
    (abs_neg_eq_abs a) ▸ (self_le_abs_self (-a))

  theorem neg_self_le_abs_neg_self (a : α) : -a ≤ abs (-a) :=
    self_le_abs_self (-a)

  theorem triangle_add_le_add (a b : α) : abs (a + b) ≤ abs a + abs b :=
    (nonneg_or_nonpos (a+b)).elim
      (fun h => (abs_of_nonneg h).substr (le_of_add_le_le (self_le_abs_self a) (self_le_abs_self b)))
      (fun h => ((neg_sum a b) ▸ abs_of_nonpos h) ▸ le_of_add_le_le (neg_self_le_abs_self a) (neg_self_le_abs_self b))

  theorem triangle_sub_le_add (a b : α) : abs (a - b) ≤ abs a + abs b :=
    (nonneg_or_nonpos (a-b)).elim
      (fun h => (abs_of_nonneg h).substr (le_of_add_le_le (self_le_abs_self a) (neg_self_le_abs_self b)))
      (fun h => (neg_neg b ▸ neg_sum a (-b) ▸ abs_of_nonpos h) ▸ (le_of_add_le_le (neg_self_le_abs_self a) (self_le_abs_self b)))

  theorem triangle_add_ge_sub (a b : α) : abs (a + b) ≥ abs a - abs b :=
    sub_right_le_of_le_add ((add_sub_cancel a b).subst (motive:=(abs ·≤_)) (triangle_sub_le_add (a + b) b))

  theorem triangle_add_ge_sub' (a b : α) : abs (a + b) ≥ abs b - abs a :=
    add_comm a b ▸ triangle_add_ge_sub b a

  theorem triangle_sub_ge_sub (a b : α) : abs (a - b) ≥ abs a - abs b :=
    sub_right_le_of_le_add ((sub_add_cancel a b).subst (motive:=(abs ·≤_)) (triangle_add_le_add (a - b) b))

  theorem triangle_sub_ge_sub' (a b : α) : abs (a - b) ≥ abs b - abs a :=
    abs_neg_eq_abs (a - b) ▸ neg_sub a b ▸ triangle_sub_ge_sub b a

  theorem triangle_add_ge_abs_sub (a b : α) : abs (a + b) ≥ abs (abs a - abs b) :=
    (nonneg_or_nonpos (abs a - abs b)).elim
      (fun h => (abs_of_nonneg h).substr (triangle_add_ge_sub a b))
      (fun h =>abs_of_nonpos h ▸ neg_sub (abs a) _ ▸ triangle_add_ge_sub' a b)

  theorem triangle_sub_ge_abs_sub (a b : α) : abs (a - b) ≥ abs (abs a - abs b) :=
    (nonneg_or_nonpos (abs a - abs b)).elim
      (fun h => (abs_of_nonneg h).substr (triangle_sub_ge_sub a b))
      (fun h =>abs_of_nonpos h ▸ neg_sub (abs a) _ ▸ triangle_sub_ge_sub' a b)

end OrderedCommGroup

end my
