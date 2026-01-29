import Analysis2.Operator
import Analysis2.Comp
noncomputable section
namespace my
open Classical
open Comp
open Zero One

inductive ℕ where
  | _zero
  | succ : ℕ → ℕ


namespace ℕ

  -- axiom _zero : ℕ

  @[default_instance, reducible] instance : Zero ℕ := ⟨_zero⟩

  -- axiom succ : ℕ → ℕ

  theorem succ_ne_zero {n : ℕ} : ¬(succ n = zero) :=
    ℕ.noConfusion

  theorem succ_inj (a b : ℕ) : succ a = succ b → a = b :=
    succ.inj

  -- axiom ind' {h : ℕ → Prop} (h0 : h zero) (h_ind : ∀(a : ℕ), h a → h (succ a)) : ∀(a : ℕ), h a



  section basic

    section nums

      def _one : ℕ := zero.succ
      @[default_instance] instance : One ℕ := ⟨_one⟩
      theorem one_def : one = _one := rfl

      def num.two : ℕ := one.succ
      def num.three : ℕ := two.succ
      def num.four : ℕ := three.succ
      def num.five : ℕ := four.succ
      def num.six : ℕ := five.succ
      def num.seven : ℕ := six.succ

      open num

      theorem one_eq_succ_zero : one = zero.succ := rfl
      theorem two_eq_succ_one : two = one.succ := rfl
      theorem three_eq_succ_two : three = two.succ := rfl
      theorem four_eq_succ_three : four = three.succ := rfl
      theorem five_eq_succ_four : five = four.succ := rfl
      theorem six_eq_succ_five : six = five.succ := rfl
      theorem seven_eq_succ_six : seven = six.succ := rfl

      theorem zero_ne_one : zero ≠ one :=
        fun h => succ_ne_zero (n:=_zero) (h ▸ one_eq_succ_zero.symm)


    end nums

    theorem zero_or_is_succ : ∀(a : ℕ), a = zero ∨ ∃(b : ℕ), a = succ b
    | _zero => Or.inl rfl
    | succ n => Or.inr ⟨n, rfl⟩

    theorem nonzero_is_succ {a : ℕ} : a ≠ zero → ∃(b : ℕ), a = succ b :=
      a.zero_or_is_succ.resolve_left

    theorem succ_ne_self : ∀ (n : ℕ), n.succ ≠ n :=
      ℕ.rec succ_ne_zero fun _ h h' => h (succ_inj _ _ h')

  end basic

  section add

    def add : ℕ → ℕ → ℕ := fun n m => match m with
    | _zero => n
    | succ m => (add n m).succ

    @[default_instance] instance : Add ℕ := {add}

    theorem add_zero (n : ℕ) : n + zero = n := rfl

    theorem add_succ (n m : ℕ) : n + m.succ = (n + m).succ := rfl

    theorem zero_add : ∀(n : ℕ), zero + n = n
    | _zero => rfl
    | succ n => congrArg succ n.zero_add

    theorem succ_add : ∀(n m : ℕ), n.succ + m = (n + m).succ
    | _, _zero => rfl
    | _, succ _ => congrArg succ (succ_add _ _)

    theorem add_comm : ∀(n m : ℕ), n + m = m + n
    | _, _zero => (zero_add _).symm
    | n, succ m => (add_comm n m).substr (p:=(·.succ=_)) (succ_add m n).symm

    theorem add_assoc : ∀ (a b c : ℕ), (a + b) + c = a + (b + c)
    | _, _, _zero => rfl
    | _, _, succ c => congrArg succ (add_assoc _ _ c)

    instance : Std.Associative (α := ℕ) (.+.) := ⟨ℕ.add_assoc⟩
    instance : Std.Commutative (α := ℕ) (.+.) := ⟨ℕ.add_comm⟩

    theorem add_right_comm : ∀ (a b c : ℕ), (a + b) + c = (a + c) + b := by
      intros
      ac_nf

    theorem add_left_comm : ∀ (a b c : ℕ), a + (b + c) = b + (a + c) := by
      intros
      ac_nf

    theorem add_left_inj {a b : ℕ} : ∀ (c : ℕ), a + c = b + c → a = b
    | _zero => id
    | succ _ => fun h => add_left_inj _ (succ_inj _ _ h)

    theorem add_left_inj_iff {a b : ℕ} : ∀ (c : ℕ), a + c = b + c ↔ a = b :=
     fun c => ⟨add_left_inj c, congrArg (·+c)⟩

    theorem add_right_inj {a b : ℕ} : ∀ (c : ℕ), c + a = c + b → a = b := by
      intro c
      simp only [c.add_comm]
      exact add_left_inj c

    theorem add_right_inj_iff {a b : ℕ} : ∀ (c : ℕ), c + a = c + b ↔ a = b :=
      fun c => ⟨add_right_inj c, congrArg (c+·)⟩

    theorem eq_zero_of_add_eq_zero_right {a b : ℕ} : a + b = zero → b = zero :=
      fun h => match b with
        | _zero => rfl
        | succ _ => (succ_ne_zero h).elim

    theorem eq_zero_of_add_eq_zero_left {a b : ℕ} : a + b = zero → a = zero :=
      fun h => eq_zero_of_add_eq_zero_right (h.subst (a.add_comm b).symm)

    theorem add_left_eq_self_is_zero {a b : ℕ} : a + b = b → a = zero :=
      fun h => match b with
        | _zero => h
        | succ _ => add_left_eq_self_is_zero (succ_inj _ _ h)

    theorem add_right_eq_self_is_zero {a b : ℕ} : a + b = a → b = zero :=
      (add_comm _ _).substr add_left_eq_self_is_zero

    section num

      theorem add_one_eq_succ : ∀ (n : ℕ), n + one = n.succ := by
        intro n
        rw [one_eq_succ_zero, add_succ, add_zero]

    end num

  end add

  section mul

    def mul : ℕ → ℕ → ℕ :=
      fun a b => match b with
       | _zero => _zero
       | succ b => (mul a b) + a

    instance : Mul ℕ := {mul}

    theorem mul_zero (n : ℕ) : n * zero = zero := rfl

    theorem mul_succ (n m : ℕ) : n * m.succ = (n * m) + n := rfl

    theorem mul_one : ∀(n : ℕ), n * one = n := by
      intro n
      rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

    theorem zero_mul : ∀(n : ℕ), zero * n = zero
    | _zero => rfl
    | succ n => zero_mul n

    theorem succ_mul : ∀(n m : ℕ), n.succ * m = (n * m) + m :=
      fun n m => match m with
      | _zero => rfl
      | succ m =>
        suffices ((n.succ * m) + n).succ = ((n * m) + n + m).succ from this
        add_right_comm _ _ _ ▸ congrArg (fun x => succ (x+n)) (succ_mul n m)

    theorem mul_comm : ∀(n m : ℕ), n * m = m * n
    | _, _zero => (zero_mul _).symm
    | _, succ _ => succ_mul _ _ ▸ congrArg (·+_) (mul_comm _ _)

    theorem add_mul : ∀(a b c : ℕ), (a + b) * c = (a * c) + (b * c)
    | _, _, _zero => rfl
    | a, b, succ c =>
      show (a + b) * c + (a + b) = a * c + a + (b * c + b) from
        add_assoc _ _ _ ▸ add_assoc _ _ _ ▸ add_right_comm _ (b*c) a ▸ congrArg (·+a+b) (add_mul a b c)

    theorem mul_add : ∀(a b c : ℕ), a * (b + c) = (a * b) + (a * c) := by
      intro a _ _
      rw [mul_comm, add_mul, mul_comm a, mul_comm a]

    theorem mul_assoc : ∀ (a b c : ℕ), (a * b) * c = a * (b * c)
    | _, _, _zero => rfl
    | _, _, succ _ => mul_add _ _ _ ▸ congrArg (·+_) (mul_assoc _ _ _)

    instance : Std.Associative (α := ℕ) (.*.) := ⟨ℕ.mul_assoc⟩
    instance : Std.Commutative (α := ℕ) (.*.) := ⟨ℕ.mul_comm⟩

    theorem mul_eq_zero {a b : ℕ} : a * b = zero → a = zero ∨ b = zero :=
      fun h => (em (a = _zero)).elim Or.inl fun h0 => Or.inr (eq_zero_of_add_eq_zero_right (((nonzero_is_succ h0).choose_spec.subst (motive := (· * b = _zero)) h).subst (ℕ.succ_mul _ _).symm))

  end mul

  section comp

    def le : ℕ → ℕ → Prop :=
      fun n m => ∃(x : ℕ), m = n + x

    theorem _le_refl : ∀ (a : ℕ), a.le a :=
      (⟨_zero, ·.add_zero.symm⟩)

    theorem _le_trans : ∀(a b c : ℕ), a.le b → b.le c → a.le c :=
      fun _ _ _ ⟨x1, hx1⟩ ⟨x2, hx2⟩ => ⟨x1 + x2, hx2.substr (hx1.substr (add_assoc _ x1 x2))⟩

    theorem _le_antisymm : ∀(a b : ℕ), a.le b → b.le a → a = b := by
      intro _ _ ⟨_, hx⟩ ⟨_, hx'⟩
      rw [hx, add_assoc] at hx'
      replace hx' := eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero hx'.symm)
      rw [hx, hx', add_zero]

    theorem _le_total : ∀(a b : ℕ), a.le b ∨ b.le a := by
      intro a b
      apply byContradiction
      simp only [not_or]
      intro ⟨hnab, hnba⟩
      have h : ∀(n : ℕ), ¬(a.le (b + n)) := ℕ.rec (b.add_zero.substr hnab) (by
        intro n hn ⟨x, hx⟩
        cases x.zero_or_is_succ
        case inl h0 =>
          rw [h0, add_zero] at hx
          exact hnba ⟨n.succ, hx.symm⟩
        case inr hn0 =>
          have ⟨x', hx'⟩ := hn0
          rw [hx', add_succ, add_succ] at hx
          exact hn ⟨x', (succ_inj _ _ hx)⟩
      )
      exact (h a) ((add_comm b a).substr ⟨b, rfl⟩)

    @[default_instance] instance : Comp ℕ :=
      ⟨le, _le_refl, _le_trans, _le_antisymm, _le_total⟩

    theorem zero_le : ∀(n : ℕ), zero ≤ n :=
      fun n => ⟨n, (zero_add n).symm⟩

    theorem not_lt_zero (n : ℕ) : ¬n < zero :=
      fun h => (not_le_of_lt h) (zero_le n)

    theorem eq_zero_of_le_zero {n : ℕ} : n ≤ zero → n = zero :=
      fun h => le_antisymm _ _ h (zero_le n)

    @[reducible] def pos (n : ℕ) : Prop := zero < n

    theorem pos_of_nonzero {n : ℕ} : n ≠ zero → zero < n :=
      fun h => lt_of_le_ne n.zero_le h.symm

    theorem nonzero_of_pos {n : ℕ} : zero < n → n ≠ zero :=
      ne_of_gt

    theorem pos_iff_nonzero : ∀(n : ℕ), zero < n ↔ n ≠ zero :=
      fun _ => ⟨nonzero_of_pos, pos_of_nonzero⟩

    theorem le_succ : ∀ (n : ℕ), n ≤ n.succ :=
      fun n => ⟨one, n.add_one_eq_succ.symm⟩

    theorem lt_succ : ∀ (n : ℕ), n < n.succ :=
      fun n => lt_of_le_ne n.le_succ n.succ_ne_self.symm

    theorem le_succ_of_le {n m : ℕ} : n ≤ m → n ≤ m.succ :=
      fun ⟨x, hx⟩ => ⟨x.succ, hx.substr (n.add_succ x).symm⟩

    theorem lt_succ_of_le {n m : ℕ} : n ≤ m → n < m.succ :=
      fun ⟨x, hx⟩ => lt_of_le_ne (le_succ_of_le ⟨x, hx⟩) fun he => (succ_ne_zero (add_right_eq_self_is_zero ((n.add_succ x).substr (hx.subst (motive := (·.succ = n)) he.symm)))).elim

    theorem lt_succ_of_lt {n m : ℕ} : n < m → n < m.succ :=
      fun h => lt_succ_of_le (le_of_lt h)

    theorem le_succ_of_lt {n m : ℕ} : n < m → n ≤ m.succ :=
      fun h => le_of_lt (lt_succ_of_lt h)

    theorem succ_le_succ_of_le {n m} : n ≤ m → n.succ ≤ m.succ :=
      fun ⟨x, hx⟩ => ⟨x, hx ▸ (succ_add _ _).symm⟩

    theorem succ_lt_succ_of_lt {n m} : n < m → n.succ < m.succ :=
      fun h => lt_of_le_ne (succ_le_succ_of_le (le_of_lt h)) fun h' => (ne_of_lt h) (succ_inj _ _ h')

    theorem le_of_succ_le_succ {n m} : n.succ ≤ m.succ → n ≤ m :=
      fun ⟨x, hx⟩ => ⟨x, succ_inj  _ _ (succ_add _ _ ▸ hx)⟩

    theorem lt_of_succ_lt_succ {n m} : n.succ < m.succ → n < m :=
      fun h => lt_of_le_ne (le_of_succ_le_succ (le_of_lt h)) fun h' => (ne_of_lt h) (congrArg succ h')

    theorem le_of_succ_le {n m : ℕ} : n.succ ≤ m → n ≤ m :=
      fun ⟨x, hx⟩ => ⟨x.succ, add_succ _ _ ▸ succ_add _ _ ▸ hx⟩

    theorem le_of_succ_lt {n m : ℕ} : n.succ < m → n ≤ m :=
      fun h => le_of_succ_le (le_of_lt h)

    theorem lt_of_succ_le {n m : ℕ} : n.succ ≤ m → n < m :=
      fun h => lt_of_le_ne (le_of_succ_le h) fun h' =>
        ne_of_lt (lt_succ_of_le h) (congrArg succ h')

    theorem lt_of_succ_lt {n m : ℕ} : n.succ < m → n < m :=
      fun h => lt_of_succ_le (le_of_lt h)

    theorem succ_pos (n : ℕ) : zero < succ n :=
      lt_succ_of_le (zero_le n)

    theorem pos_is_succ {n : ℕ} : pos n → ∃ (m : ℕ), n = m.succ :=
      fun h => n.zero_or_is_succ.resolve_left (ne_of_lt h ·.symm)

    theorem le_of_lt_succ {n m : ℕ} : n < m.succ → n ≤ m := by
      intro h
      have ⟨x, hx⟩ := le_of_lt h
      have ⟨x', hx'⟩ := @nonzero_is_succ x (fun h' => ne_of_lt h (h' ▸ hx).symm)
      refine' ⟨x', succ_inj _ _ _⟩
      rw [hx, hx', add_succ]

    theorem succ_le_of_lt {n m : ℕ} : n < m → n.succ ≤ m :=
      fun h => le_of_not_lt fun h' => h (le_of_lt_succ h')

    theorem le_add (n m : ℕ) : n ≤ (n + m) :=
      ⟨m, Eq.symm rfl⟩

    theorem le_add_right {a b : ℕ} : ∀ (c : ℕ), a ≤ b → a ≤ (b + c) :=
      fun c ⟨x, hx⟩ => ⟨x + c, hx.substr (add_assoc _ _ _)⟩

    theorem le_add_left {a b : ℕ} : ∀ (c : ℕ), a ≤ b → a ≤ (c + b) :=
      fun c h => (add_comm _ _).substr (le_add_right c h)

    theorem add_le_self_is_zero {a b : ℕ} : (a + b) ≤ a → b = zero :=
      fun ⟨x, hx⟩ => eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero ((a.add_assoc b x).subst hx).symm)

    theorem lt_add_right {a b : ℕ} : ∀ (c : ℕ), a < b → a < (b + c) := by
      intro c h;
      refine' lt_of_le_ne (le_add_right _ (le_of_lt h)) _
      intro h'
      have ⟨x, hx⟩ := le_of_lt h
      rw [hx, add_assoc] at h'
      rw [eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero h'.symm), add_zero] at hx
      rw [hx] at h
      exact not_lt_self a h

    theorem lt_add_left {a b : ℕ} : ∀ (c : ℕ), a < b → a < (c + b) :=
      fun c h => (add_comm c b).substr (lt_add_right c h)

    theorem pos_add_neq_self {n : ℕ} : pos n → ∀ (m : ℕ), n + m ≠ m :=
      fun h _ h' => succ_ne_zero ((add_left_eq_self_is_zero h').subst (pos_is_succ h).choose_spec.symm)

    theorem add_pos_neq_self {n : ℕ} : pos n → ∀ (m : ℕ), m + n ≠ m :=
      fun h _ h' => succ_ne_zero ((add_right_eq_self_is_zero h').subst (pos_is_succ h).choose_spec.symm)

    theorem add_le_add_iff_left {a b c : ℕ} : (a + b) ≤ (a + c) ↔ b ≤ c := by
      apply Iff.intro
      <;> intro ⟨x, h⟩
      <;> exists x
      <;> apply add_right_inj a
      <;> rw [h, add_assoc]

    theorem add_le_add_of_le_left (a : ℕ) {b c : ℕ} : b ≤ c → (a + b) ≤ (a + c) :=
      add_le_add_iff_left.mpr

    theorem le_of_add_le_add_left {a b c : ℕ} :  (a + b) ≤ (a + c) → b ≤ c :=
      add_le_add_iff_left.mp

    theorem add_le_add_iff_right {a b c : ℕ} : (a + c) ≤ (b + c) ↔ a ≤ b := by
      rw [add_comm, add_comm b, add_le_add_iff_left]

    theorem add_le_add_of_le_right {a b : ℕ} (c : ℕ) : a ≤ b → (a + c) ≤ (b + c) :=
      add_le_add_iff_right.mpr

    theorem le_of_add_le_add_right {a b c : ℕ} : (a + c) ≤ (b + c) → a ≤ b :=
      add_le_add_iff_right.mp

    theorem add_lt_add_iff_left {a b c : ℕ} :  (c + a) < (c + b) ↔ a < b := by
      rw [←not_le_iff, ←not_le_iff, add_le_add_iff_left]

    theorem add_lt_add_of_lt_left {a b : ℕ} (c : ℕ) : a < b → (c + a) < (c + b) :=
      add_lt_add_iff_left.mpr

    theorem lt_of_add_lt_add_left {a b c : ℕ} :  (c + a) < (c + b) → a < b :=
      add_lt_add_iff_left.mp

    theorem add_lt_add_iff_right {a b c : ℕ} : (a + c) < (b + c) ↔ a < b := by
      rw [←not_le_iff, ←not_le_iff, add_le_add_iff_right]

    theorem lt_of_add_lt_add_right {a b c : ℕ} : (a + c) < (b + c) → a < b :=
      add_lt_add_iff_right.mp

    theorem add_lt_add_of_lt_right {a b : ℕ} (c : ℕ) : a < b → (a + c) < (b + c) :=
      add_lt_add_iff_right.mpr

    theorem add_le_le_le {a b c d : ℕ} : (a ≤ b) → (c ≤ d) → (a + c) ≤ (b + d) :=
      fun h1 h2 => le_trans _ _ _ ((add_le_add_iff_right (c := c)).mpr h1) ((add_le_add_iff_left (a := b)).mpr h2)

    theorem le_of_add_le_le {a b c d : ℕ} : (a ≤ b) → (c ≤ d) → (a + c) ≤ (b + d) :=
      fun h1 h2 => le_trans _ _ _ ((add_le_add_iff_right (c := c)).mpr h1) ((add_le_add_iff_left (a := b)).mpr h2)

    theorem le_of_add_lt_le {a b c d : ℕ} : (a < b) → (c ≤ d) → (a + c) ≤ (b + d) :=
      fun h h' => le_of_add_le_le (le_of_lt h) h'

    theorem le_of_add_le_lt {a b c d : ℕ} : (a ≤ b) → (c < d) → (a + c) ≤ (b + d) :=
      fun h h' => le_of_add_le_le h (le_of_lt h')

    theorem le_of_add_lt_lt {a b c d : ℕ} : (a < b) → (c < d) → (a + c) ≤ (b + d) :=
      fun h h' => le_of_add_le_le (le_of_lt h) (le_of_lt h')

    theorem lt_of_add_lt_le {a b c d : ℕ} : (a < b) → (c ≤ d) → (a + c) < (b + d) :=
      fun h h' => lt_of_lt_le (add_lt_add_of_lt_right c h) (add_le_add_of_le_left b h')

    theorem lt_of_add_le_lt {a b c d : ℕ} : (a ≤ b) → (c < d) → (a + c) < (b + d) :=
      fun h h' => lt_of_le_lt (add_le_add_of_le_right c h) (add_lt_add_of_lt_left b h')

    theorem lt_of_add_lt_lt {a b c d : ℕ} : (a < b) → (c < d) → (a + c) < (b + d) :=
      fun h h' => lt_of_add_le_lt (le_of_lt h) h'

    theorem zero_le_one : zero ≤ one := _zero.le_succ

    theorem zero_lt_one : zero < one := _zero.lt_succ

    theorem mul_le_mul_of_le_left {b c : ℕ} (a : ℕ) : b ≤ c → (a * b) ≤ (a * c) := by
      intro ⟨x, h⟩
      exists a * x
      rw [h, mul_add]

    theorem mul_le_mul_of_le_right {a b : ℕ} (c : ℕ) : a ≤ b → (a * c) ≤ (b * c) := by
      intro ⟨x, h⟩
      exists x * c
      rw [h, add_mul]

    theorem le_of_mul_le_mul_left {a b c : ℕ} (h0 : a ≠ zero): (a * b) ≤ (a * c) → b ≤ c := by
      intro ⟨x, h⟩
      cases le_or_ge b c
      assumption
      case inr h' =>
        have ⟨x', hx'⟩ := h'
        rw [hx', mul_add, add_assoc] at h
        replace h := eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero h.symm)
        replace h := (mul_eq_zero h).resolve_left h0
        rw [hx', h, add_zero]
        exact le_refl _

    theorem le_of_mul_le_mul_right {a b c : ℕ} (h0 : c ≠ zero): (a * c) ≤ (b * c) → a ≤ b := by
      intro h
      apply le_of_mul_le_mul_left h0
      simp only [mul_comm c, h]

    theorem mul_le_mul_iff_left {a b c : ℕ} (h0 : a ≠ zero) : (a * b) ≤ (a * c) ↔ b ≤ c :=
      Iff.intro (le_of_mul_le_mul_left h0) (mul_le_mul_of_le_left a)

    theorem mul_le_mul_iff_right {a b c : ℕ} (h0 : c ≠ zero) : (a * c) ≤ (b * c) ↔ a ≤ b :=
      Iff.intro (le_of_mul_le_mul_right h0) (mul_le_mul_of_le_right c)

    theorem mul_le_le_le {a b c d : ℕ} : (a ≤ b) → (c ≤ d) → (a * c) ≤ (b * d) :=
      fun h1 h2 => le_trans _ _ _ (mul_le_mul_of_le_right c h1) (mul_le_mul_of_le_left b h2)




    section num

    end num

  end comp

    theorem mul_left_inj {a b c : ℕ} (hc : c ≠ zero): a * c = b * c ↔ a = b := by
      apply Iff.intro
      case mp =>
        intro h
        have p1 (a b c : ℕ) (hc : c ≠ _zero) (hl : a ≤ b) : a * c = b * c → a = b := by
          have ⟨x, hx⟩ := hl
          rw [hx, add_mul]
          intro h
          replace h := (mul_eq_zero (add_right_eq_self_is_zero h.symm)).resolve_right hc
          rw [h, add_zero]
        cases le_or_ge a b
        case inl h' => exact p1 a b c hc h' h
        case inr h' => symm;exact p1 b a c hc h' h.symm
      case mpr =>
        intro h;simp only [h]

    theorem mul_right_inj {a b c : ℕ} (hc : c ≠ zero) : c * a = c * b ↔ a = b := by
      simp only [c.mul_comm]
      exact mul_left_inj hc

end ℕ

structure ℕp where
  n : ℕ
  p : zero < n

class OfNat (α : Type) where
  ofNat : ℕ → α

@[reducible] def OfNat.ofNat' (α : Type) [OfNat α] := ofNat (α:=α)

end my
