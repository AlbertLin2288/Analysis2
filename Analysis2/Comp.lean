noncomputable section
namespace my
open Classical

class Comp (α : Type) where
  le : α → α → Prop
  le_refl : ∀(a : α), le a a
  le_trans : ∀(a b c : α), le a b → le b c → le a c
  le_antisymm : ∀(a b: α), le a b → le b a → a = b
  le_total : ∀(a b : α), le a b ∨ le b a

namespace Comp

  variable {α : Type} [Comp α]

  @[reducible] def ge (n m : α) : Prop := le m n

  def lt : α → α → Prop :=
    fun n m => ¬ le m n

  @[reducible] def gt (n m : α) : Prop := lt m n

  notation:50 (priority := high) lhs:51 " ≥ " rhs:51 => le rhs lhs
  notation:50 (priority := high) lhs:51 " > " rhs:51 => lt rhs lhs
  notation:50 (priority := high) lhs:51 " ≤ " rhs:51 => le lhs rhs
  notation:50 (priority := high) lhs:51 " < " rhs:51 => lt lhs rhs

  -- alternative name
  theorem le_self : ∀(n : α), n ≤ n := le_refl

  theorem le_of_eq {n m : α} : n = m → n ≤ m :=
   (·.substr (le_self m))

  theorem not_lt_self (n : α) : ¬ n < n :=
    (· (le_refl _))

  theorem le_of_lt {n m : α} : n < m → n ≤ m :=
    (le_total n m).resolve_right

  theorem ne_of_lt {n m : α} : n < m → n ≠ m :=
    fun h h' => not_lt_self _ (h'.substr (p:=(n<·)) h)

  theorem lt_of_le_ne {n m : α} : n ≤ m → n ≠ m → n < m :=
    fun h h' h'' => h' (le_antisymm _ _ h h'')

  theorem lt_or_eq_of_le {n m : α} : n ≤ m → n < m ∨ n = m :=
    fun h => (em (n = m)).elim (Or.inr ·) fun h' => (Or.inl (lt_of_le_ne h h'))

  theorem eq_or_gt_of_ge {n m : α} : n ≥ m → n = m ∨ n > m :=
    fun h => (lt_or_eq_of_le h).elim (Or.inr ·) (Or.inl ·.symm)

  theorem lt_or_eq_or_gt : ∀ (n m : α), n < m ∨ n = m ∨ n > m :=
    fun n m => (le_total n m).elim
      (fun h => (lt_or_eq_of_le h).elim Or.inl fun h' => Or.inr (Or.inl h'))
      fun h => Or.inr (eq_or_gt_of_ge h)

  theorem eq_or_lt_or_gt : ∀ (n m : α), n = m ∨ n < m ∨ n > m :=
    fun n m => (lt_or_eq_or_gt n m).elim (fun h => Or.inr (Or.inl h)) (·.elim Or.inl (fun h => Or.inr (Or.inr h)))

  theorem le_or_ge : ∀ (n m : α), n ≤ m ∨ n ≥ m :=
    fun n m => (lt_or_eq_or_gt n m).elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (h.elim (le_of_eq ·.symm) (le_of_lt ·)))

  theorem le_or_gt : ∀ (n m : α), n ≤ m ∨ n > m :=
    fun n m => (lt_or_eq_or_gt n m).elim (fun h => Or.inl (le_of_lt h)) (Or.elim · (fun h => Or.inl (le_of_eq h)) Or.inr)

  theorem lt_or_ge : ∀ (n m : α), n< m ∨ n ≥ m :=
    fun n m => (lt_or_eq_or_gt n m).elim Or.inl (fun h => Or.inr (h.elim (le_of_eq ·.symm) (le_of_lt ·)))

  theorem not_le_of_lt {a b : α} : a < b → ¬(b ≤ a) := id

  theorem not_lt_of_le {a b : α} : a ≤ b → ¬(b < a) :=
    imp_not_comm.mp id

  theorem not_lt_of_lt {a b : α} : a < b → ¬(b < a) :=
    fun h => not_lt_of_le (le_of_lt h)

  theorem lt_of_not_le {a b : α} : ¬(a ≤ b) → b< a := id

  theorem le_of_not_lt {a b : α} : ¬(a < b) → b ≤ a :=
    ((lt_or_ge a b).resolve_left ·)

  theorem le_of_not_le {a b : α} : ¬(a ≤ b) → b ≤ a :=
    ((le_or_ge a b).resolve_left ·)

  theorem lt_of_lt_le {a b c : α} : a < b → b ≤ c → a < c :=
    fun h h' h'' => h (le_trans _ _ _ h' h'')

  theorem lt_of_le_lt {a b c : α} : a ≤ b → b < c → a < c :=
    fun h h' h'' => h' (le_trans _ _ _ h'' h)

  theorem lt_of_lt_lt {a b c : α} : a < b → b < c → a < c :=
    fun h => lt_of_le_lt (le_of_lt h)

  theorem lt_trans {a b c : α} : a < b → b < c → a < c :=  lt_of_lt_lt

  theorem le_of_le_le {a b c : α} : a ≤ b → b ≤ c → a ≤ c :=
    le_trans _ _ _

  theorem le_of_le_lt {a b c : α} : a ≤ b → b < c → a ≤ c :=
    fun h h' => le_of_lt (lt_of_le_lt h h')

  theorem le_of_lt_le {a b c : α} : a < b → b ≤ c → a ≤ c :=
    fun h h' => le_of_lt (lt_of_lt_le h h')

  theorem le_of_lt_lt {a b c : α} : a < b → b < c → a ≤ c :=
    fun h h' => le_of_lt (lt_of_lt_lt h h')


#check Std.IsLinearOrder

end Comp

end my
