import Analysis2.logic
noncomputable section
namespace my
open Classical
open Max Min

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

  @[reducible] private def _max : α → α → α := fun a b => (le_total a b).elim' (fun _ => b) (fun _ => a)
  @[reducible] private def _min : α → α → α := fun a b => (le_total a b).elim' (fun _ => a) (fun _ => b)

  @[default_instance, reducible] instance : Max α where
    max := _max

  @[default_instance, reducible] instance : Min α where
    min := _min

  private theorem max_def {a b : α} : max a b = _max a b := rfl
  private theorem min_def {a b : α} : min a b = _min a b := rfl

  theorem max_le_is_snd {a b : α} : a ≤ b → max a b = b :=
    fun h => Or.elim'_spec (h:=le_total _ _) (p:=(·=b)) (fun _ => rfl) (le_antisymm _ _ h)

  theorem max_ge_is_fst {a b : α} : a ≥ b → max a b = a :=
    fun h => Or.elim'_spec (h:=le_total _ _) (p:=(·=a)) (le_antisymm _ _ h) (fun _ => rfl)

  theorem min_le_is_fst {a b : α} : a ≤ b → min a b = a :=
    fun h => Or.elim'_spec (h:=le_total _ _) (p:=(·=a)) (fun _ => rfl) (le_antisymm _ _ · h)

  theorem min_ge_is_snd {a b : α} : a ≥ b → min a b = b :=
    fun h => Or.elim'_spec (h:=le_total _ _) (p:=(·=b)) (le_antisymm _ _ · h) (fun _ => rfl)

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

  theorem ne_of_gt {n m : α} : n > m → n ≠ m :=
    fun h => (ne_of_lt h).symm

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

  theorem gt_or_eq_or_lt (n m : α) : n > m ∨ n = m ∨ n < m :=
    (lt_or_eq_or_gt m n).elim Or.inl fun h => Or.inr (h.elim (Or.inl ·.symm) Or.inr)

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

  section chain

    variable {a b : α}

    -- theorem le_of_eq
    -- theorem le_of_lt

    variable {c : α}

    omit [Comp α] in
    theorem eq_of_eq_eq : a = b → b = c → a = c :=
      Eq.trans

    theorem lt_of_lt_eq : a < b → b = c → a < c :=
      fun h h' => h' ▸ h

    theorem lt_of_eq_lt : a = b → b < c → a < c :=
      fun h h' => h ▸ h'

    theorem le_of_eq_eq : a = b → b = c → a ≤ c :=
      fun h h' => h ▸ le_of_eq h'

    theorem le_of_le_eq : a ≤ b → b = c → a ≤ c :=
      fun h h' => h' ▸ h

    theorem le_of_eq_le : a = b → b ≤ c → a ≤ c :=
      fun h h' => h ▸ h'

    theorem le_of_eq_lt : a = b → b < c → a ≤ c :=
      fun h h' => h ▸ le_of_lt h'

    theorem le_of_lt_eq : a < b → b = c → a ≤ c :=
      fun h h' => h' ▸ le_of_lt h

    theorem lt_of_lt_le : a < b → b ≤ c → a < c :=
      fun h h' h'' => h (le_trans _ _ _ h' h'')

    theorem lt_of_le_lt : a ≤ b → b < c → a < c :=
      fun h h' h'' => h' (le_trans _ _ _ h'' h)

    theorem lt_of_lt_lt : a < b → b < c → a < c :=
      fun h => lt_of_le_lt (le_of_lt h)

    theorem le_of_le_le : a ≤ b → b ≤ c → a ≤ c :=
      le_trans _ _ _

    theorem le_of_le_lt : a ≤ b → b < c → a ≤ c :=
      fun h h' => le_of_lt (lt_of_le_lt h h')

    theorem le_of_lt_le : a < b → b ≤ c → a ≤ c :=
      fun h h' => le_of_lt (lt_of_lt_le h h')

    theorem le_of_lt_lt : a < b → b < c → a ≤ c :=
      fun h h' => le_of_lt (lt_of_lt_lt h h')

    variable {d : α}

    theorem lt_of_lt_lt_lt : a < b → b < c → c < d → a < d :=
      fun h h' h'' => lt_of_lt_lt h (lt_of_lt_lt h' h'')
    theorem le_of_lt_lt_lt : a < b → b < c → c < d → a ≤ d :=
      fun h h' h'' => le_of_lt_lt h (lt_of_lt_lt h' h'')
    theorem lt_of_lt_lt_le : a < b → b < c → c ≤ d → a < d :=
      fun h h' h'' => lt_of_lt_lt h (lt_of_lt_le h' h'')
    theorem le_of_lt_lt_le : a < b → b < c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_lt_lt h (lt_of_lt_le h' h'')
    theorem lt_of_lt_lt_eq : a < b → b < c → c = d → a < d :=
      fun h h' h'' => lt_of_lt_lt h (lt_of_lt_eq h' h'')
    theorem le_of_lt_lt_eq : a < b → b < c → c = d → a ≤ d :=
      fun h h' h'' => le_of_lt_lt h (lt_of_lt_eq h' h'')
    theorem lt_of_lt_le_lt : a < b → b ≤ c → c < d → a < d :=
      fun h h' h'' => lt_of_lt_lt h (lt_of_le_lt h' h'')
    theorem le_of_lt_le_lt : a < b → b ≤ c → c < d → a ≤ d :=
      fun h h' h'' => le_of_lt_lt h (lt_of_le_lt h' h'')
    theorem lt_of_lt_le_le : a < b → b ≤ c → c ≤ d → a < d :=
      fun h h' h'' => lt_of_lt_le h (le_of_le_le h' h'')
    theorem le_of_lt_le_le : a < b → b ≤ c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_lt_le h (le_of_le_le h' h'')
    theorem lt_of_lt_le_eq : a < b → b ≤ c → c = d → a < d :=
      fun h h' h'' => lt_of_lt_le h (le_of_le_eq h' h'')
    theorem le_of_lt_le_eq : a < b → b ≤ c → c = d → a ≤ d :=
      fun h h' h'' => le_of_lt_le h (le_of_le_eq h' h'')
    theorem lt_of_lt_eq_lt : a < b → b = c → c < d → a < d :=
      fun h h' h'' => lt_of_lt_lt h (lt_of_eq_lt h' h'')
    theorem le_of_lt_eq_lt : a < b → b = c → c < d → a ≤ d :=
      fun h h' h'' => le_of_lt_lt h (lt_of_eq_lt h' h'')
    theorem lt_of_lt_eq_le : a < b → b = c → c ≤ d → a < d :=
      fun h h' h'' => lt_of_lt_le h (le_of_eq_le h' h'')
    theorem le_of_lt_eq_le : a < b → b = c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_lt_le h (le_of_eq_le h' h'')
    theorem lt_of_lt_eq_eq : a < b → b = c → c = d → a < d :=
      fun h h' h'' => lt_of_lt_le h (le_of_eq_eq h' h'')
    theorem le_of_lt_eq_eq : a < b → b = c → c = d → a ≤ d :=
      fun h h' h'' => le_of_lt_le h (le_of_eq_eq h' h'')
    theorem lt_of_le_lt_lt : a ≤ b → b < c → c < d → a < d :=
      fun h h' h'' => lt_of_le_lt h (lt_of_lt_lt h' h'')
    theorem le_of_le_lt_lt : a ≤ b → b < c → c < d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_lt_lt h' h'')
    theorem lt_of_le_lt_le : a ≤ b → b < c → c ≤ d → a < d :=
      fun h h' h'' => lt_of_le_lt h (lt_of_lt_le h' h'')
    theorem le_of_le_lt_le : a ≤ b → b < c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_le_lt h (lt_of_lt_le h' h'')
    theorem lt_of_le_lt_eq : a ≤ b → b < c → c = d → a < d :=
      fun h h' h'' => lt_of_le_lt h (lt_of_lt_eq h' h'')
    theorem le_of_le_lt_eq : a ≤ b → b < c → c = d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_lt_eq h' h'')
    theorem lt_of_le_le_lt : a ≤ b → b ≤ c → c < d → a < d :=
      fun h h' h'' => lt_of_le_lt h (lt_of_le_lt h' h'')
    theorem le_of_le_le_lt : a ≤ b → b ≤ c → c < d → a ≤ d :=
      fun h h' h'' => le_of_le_lt h (lt_of_le_lt h' h'')
    theorem le_of_le_le_le : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_le_le h' h'')
    theorem le_of_le_le_eq : a ≤ b → b ≤ c → c = d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_le_eq h' h'')
    theorem lt_of_le_eq_lt : a ≤ b → b = c → c < d → a < d :=
      fun h h' h'' => lt_of_le_lt h (lt_of_eq_lt h' h'')
    theorem le_of_le_eq_lt : a ≤ b → b = c → c < d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_eq_lt h' h'')
    theorem le_of_le_eq_le : a ≤ b → b = c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_eq_le h' h'')
    theorem le_of_le_eq_eq : a ≤ b → b = c → c = d → a ≤ d :=
      fun h h' h'' => le_of_le_le h (le_of_eq_eq h' h'')
    theorem lt_of_eq_lt_lt : a = b → b < c → c < d → a < d :=
      fun h h' h'' => lt_of_eq_lt h (lt_of_lt_lt h' h'')
    theorem le_of_eq_lt_lt : a = b → b < c → c < d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_lt_lt h' h'')
    theorem lt_of_eq_lt_le : a = b → b < c → c ≤ d → a < d :=
      fun h h' h'' => lt_of_eq_lt h (lt_of_lt_le h' h'')
    theorem le_of_eq_lt_le : a = b → b < c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_lt_le h' h'')
    theorem lt_of_eq_lt_eq : a = b → b < c → c = d → a < d :=
      fun h h' h'' => lt_of_eq_lt h (lt_of_lt_eq h' h'')
    theorem le_of_eq_lt_eq : a = b → b < c → c = d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_lt_eq h' h'')
    theorem lt_of_eq_le_lt : a = b → b ≤ c → c < d → a < d :=
      fun h h' h'' => lt_of_eq_lt h (lt_of_le_lt h' h'')
    theorem le_of_eq_le_lt : a = b → b ≤ c → c < d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_le_lt h' h'')
    theorem le_of_eq_le_le : a = b → b ≤ c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_le_le h' h'')
    theorem le_of_eq_le_eq : a = b → b ≤ c → c = d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_le_eq h' h'')
    theorem lt_of_eq_eq_lt : a = b → b = c → c < d → a < d :=
      fun h h' h'' => lt_of_eq_lt h (lt_of_eq_lt h' h'')
    theorem le_of_eq_eq_lt : a = b → b = c → c < d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_eq_lt h' h'')
    theorem le_of_eq_eq_le : a = b → b = c → c ≤ d → a ≤ d :=
      fun h h' h'' => le_of_eq_le h (le_of_eq_le h' h'')
    theorem le_of_eq_eq_eq : a = b → b = c → c = d → a ≤ d :=
      fun h h' h'' => le_of_eq_eq h (eq_of_eq_eq h' h'')
    omit [Comp α] in
    theorem eq_of_eq_eq_eq : a = b → b = c → c = d → a = d :=
      fun h h' h'' => eq_of_eq_eq h (eq_of_eq_eq h' h'')

  end chain

  theorem lt_trans {a b c : α} : a < b → b < c → a < c :=  lt_of_lt_lt

  theorem max_lt_is_snd {a b : α} : a < b → max a b = b :=
    fun h => max_le_is_snd (le_of_lt h)

  theorem max_gt_is_fst {a b : α} : a > b → max a b = a :=
    fun h => max_ge_is_fst (le_of_lt h)

  theorem min_lt_is_fst {a b : α} : a < b → min a b = a :=
    fun h => min_le_is_fst (le_of_lt h)

  theorem min_gt_is_snd {a b : α} : a > b → min a b = b :=
    fun h => min_ge_is_snd (le_of_lt h)

  theorem max_ge_fst {a b : α} : a ≤ max a b :=
    Or.elim'_spec (h:=le_total _ _) (·) (fun _ => le_self _)

  theorem max_ge_snd {a b : α} : b ≤ max a b :=
    Or.elim'_spec (h:=le_total _ _) (fun _ => le_self _) (·)

  theorem min_le_fst {a b : α} : min a b ≤ a :=
    Or.elim'_spec (h:=le_total _ _) (p:=(·≤a)) (fun _ => le_self _) id

  theorem min_le_snd {a b : α} : min a b ≤ b :=
    Or.elim'_spec (h:=le_total _ _) (p:=(·≤b)) (·) (fun _ => le_self _)


-- #check Std.IsLinearOrder

end Comp

end my
