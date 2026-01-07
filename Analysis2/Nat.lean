-- import Analysis2.Logic
noncomputable section
namespace my
open Classical

axiom ℕ : Type

namespace ℕ

  axiom zero : ℕ

  axiom succ : ℕ → ℕ

  axiom succ_ne_zero : ¬(succ a = zero)

  axiom succ_inj (a b : ℕ) : succ a = succ b → a = b

  axiom ind' {h : ℕ → Prop} (h0 : h zero) (h_ind : ∀(a : ℕ), h a → h (succ a)) : ∀(a : ℕ), h a



  section basic

    section nums

      def one : ℕ := zero.succ
      def two : ℕ := one.succ
      def three : ℕ := two.succ
      def four : ℕ := three.succ
      def five : ℕ := four.succ
      def six : ℕ := five.succ
      def seven : ℕ := six.succ


      theorem one_eq_succ_zero : one = zero.succ := rfl
      theorem two_eq_succ_one : two = one.succ := rfl
      theorem three_eq_succ_two : three = two.succ := rfl
      theorem four_eq_succ_three : four = three.succ := rfl
      theorem five_eq_succ_four : five = four.succ := rfl
      theorem six_eq_succ_five : six = five.succ := rfl
      theorem seven_eq_succ_six : seven = six.succ := rfl

    end nums


    @[reducible] def ind_prop.{u} {h : ℕ → Sort u} (h0 : h zero) (h_ind : (a : ℕ) → h a → h (succ a)) (f : (a : ℕ) → h a) := f zero = h0 ∧ (∀(n : ℕ), f n.succ = h_ind n (f n))

    def ind''.{u} {h : ℕ → Sort u} (h0 : h zero) (h_ind : (a : ℕ) → h a → h (succ a)) : ∃(f : (a : ℕ) → h a), ind_prop h0 h_ind f := sorry

    def ind.{u} {h : ℕ → Sort u} (h0 : h zero) (h_ind : (a : ℕ) → h a → h (succ a)) : (a : ℕ) → h a := (ind'' h0 h_ind).choose

    theorem ind_spec.{u} {h : ℕ → Sort u} (h0 : h zero) (h_ind : (a : ℕ) → h a → h (succ a)) : ind_prop h0 h_ind (ind h0 h_ind) :=
      Exists.choose_spec (ind'' h0 h_ind)

    theorem zero_or_is_succ (a : ℕ) : a = zero ∨ ∃(b : ℕ), a = succ b :=
      ind' (Or.inl (Eq.refl zero)) (fun b (_ : b = zero ∨ ∃(b' : ℕ), b = succ b') => Or.inr ⟨b, Eq.refl _⟩) a

    theorem nonzero_is_succ {a : ℕ} : a ≠ zero → ∃(b : ℕ), a = succ b :=
      a.zero_or_is_succ.resolve_left

    theorem succ_ne_self : ∀ (n : ℕ), n.succ ≠ n :=
      ind succ_ne_zero fun _ ha ha' => ha (succ_inj _ _ ha')

  end basic

  section add

    def add : ℕ → ℕ → ℕ :=
      fun a => ind a (fun _ x => x.succ)

    theorem add_zero : ∀(n : ℕ), n.add zero = n :=
      fun _ => (ind_spec _ _).left

    theorem add_succ : ∀(n m : ℕ), n.add m.succ = (n.add m).succ :=
      fun _ m => (ind_spec _ _).right m

    theorem zero_add : ∀(n : ℕ), zero.add n = n :=
      ind zero.add_zero (fun m (hm : zero.add m = m) => Eq.subst (motive := (zero.add m.succ = succ .)) hm (add_succ zero m))

    theorem succ_add : ∀(n m : ℕ), n.succ.add m = (n.add m).succ := by
        intro n
        apply ind
        simp only [add_zero]
        intro a ha
        simp only [add_succ, ha]

    theorem add_comm : ∀(n m : ℕ), n.add m = m.add n := by
      intro n
      apply ind
      case h0 => simp only [add_zero,zero_add]
      case h_ind =>
        intro m hm
        simp only [add_succ, succ_add, hm]

    theorem add_assoc : ∀ (a b c : ℕ), (a.add b).add c = a.add (b.add c) := by
      intro a b
      apply ind
      case h0 => simp only [add_zero]
      case h_ind =>
        intro c hc
        simp only [add_succ, hc]

    instance : Std.Associative (α := ℕ) add := ⟨add_assoc⟩
    instance : Std.Commutative (α := ℕ) add := ⟨add_comm⟩

    theorem add_right_comm : ∀ (a b c : ℕ), (a.add b).add c = (a.add c).add b := by
      intros
      ac_nf

    theorem add_left_comm : ∀ (a b c : ℕ), a.add (b.add c) = b.add (a.add c) := by
      intros
      ac_nf

    theorem add_left_inj {a b : ℕ} : ∀ (c : ℕ), a.add c = b.add c ↔ a = b := by
      intro c
      apply Iff.intro
      case mp =>
        apply ind _ _ c
        simp only [add_zero, imp_self]
        intro a' ha ha'
        simp only [add_succ] at ha'
        exact ha (succ_inj _ _ ha')
      case mpr =>
        intro h;simp only [h]

    theorem add_right_inj {a b : ℕ} : ∀ (c : ℕ), c.add a = c.add b ↔ a = b := by
      intro c
      simp only [c.add_comm]
      exact add_left_inj c

    theorem eq_zero_of_add_eq_zero_left {a b : ℕ} : a.add b = zero → a = zero :=
      ind (h := fun b => a.add b = zero → a = zero) (fun h => h.subst a.add_zero.symm) (fun b' _ h => (succ_ne_zero (h.subst (a.add_succ b').symm)).elim) b

    theorem eq_zero_of_add_eq_zero_right {a b : ℕ} : a.add b = zero → b = zero :=
      fun h => eq_zero_of_add_eq_zero_left (h.subst (a.add_comm b).symm)

    theorem add_right_eq_self_is_zero {a b : ℕ} : a.add b = a → b = zero :=
      ind (h := fun a' => a'.add b = a' → b = zero) (fun h => h.subst b.zero_add.symm) (fun a' h h' => h (succ_inj _ a' (h'.subst (a'.succ_add _).symm))) a

    theorem add_left_eq_self_is_zero {a b : ℕ} : a.add b = b → a = zero :=
      (add_comm _ _).substr add_right_eq_self_is_zero

    section num

      theorem add_one_eq_succ : ∀ (n : ℕ), n.add one = n.succ := by
        intro n
        rw [one_eq_succ_zero, add_succ, add_zero]

    end num

  end add

  section mul

    def mul : ℕ → ℕ → ℕ :=
      fun a => ind zero (fun _ x => x.add a)

    theorem mul_zero : ∀(n : ℕ), n.mul zero = zero :=
      fun _ => (ind_spec _ _).left

    theorem mul_succ : ∀(n m : ℕ), n.mul m.succ = (n.mul m).add n :=
      fun _ m => (ind_spec _ _).right m

    theorem mul_one : ∀(n : ℕ), n.mul one = n := by
      intro n
      rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

    theorem zero_mul : ∀(n : ℕ), zero.mul n = zero :=
      ind zero.mul_zero fun n hn => Eq.substr (zero.mul_succ n) (Eq.substr (zero.mul n).add_zero hn)

    theorem succ_mul : ∀(n m : ℕ), n.succ.mul m = (n.mul m).add m := by
      intro n
      apply ind
      case h0 => simp only [mul_zero, add_zero]
      case h_ind =>
        intro m hm
        simp only [mul_succ, hm, add_succ, add_right_comm]

    theorem one_mul : ∀(n : ℕ), one.mul n = n := by
      intro n
      rw [one_eq_succ_zero, succ_mul, zero_mul, zero_add]

    theorem mul_comm : ∀(n m : ℕ), n.mul m = m.mul n := by
      intro n
      apply ind
      case h0 => simp only [mul_zero,zero_mul]
      case h_ind =>
        intro m hm
        simp only [mul_succ, succ_mul, hm]

    theorem add_mul : ∀(a b c : ℕ), (a.add b).mul c = (a.mul c).add (b.mul c) := by
      intro a b
      apply ind
      case h0 => simp only [mul_zero, add_zero]
      case h_ind =>
        intro c hc
        rw [
          mul_succ, mul_succ, mul_succ, hc,
          ← add_assoc,
          ← add_assoc,
          add_right_comm (a.mul c)
        ]

    theorem mul_add : ∀(a b c : ℕ), a.mul (b.add c) = (a.mul b).add (a.mul c) := by
      intro a _ _
      rw [mul_comm, add_mul, mul_comm a, mul_comm a]

    theorem mul_assoc : ∀ (a b c : ℕ), (a.mul b).mul c = a.mul (b.mul c) := by
      intro a b
      apply ind
      case h0 => simp only [mul_zero]
      case h_ind =>
        intro c hc
        simp only [mul_succ, hc, mul_add]

    instance : Std.Associative (α := ℕ) mul := ⟨mul_assoc⟩
    instance : Std.Commutative (α := ℕ) mul := ⟨mul_comm⟩

    theorem mul_eq_zero {a b : ℕ} : a.mul b = zero → a = zero ∨ b = zero :=
      fun h => (em (a = zero)).elim Or.inl fun h0 => Or.inr (eq_zero_of_add_eq_zero_right (((nonzero_is_succ h0).choose_spec.subst (motive := (·.mul b = zero)) h).subst (ℕ.succ_mul _ _).symm))

  end mul

  section comp

    def le : ℕ → ℕ → Prop :=
      fun n m => ∃(x : ℕ), m = n.add x

    @[reducible] def ge (n m : ℕ) : Prop := le m n

    def lt : ℕ → ℕ → Prop :=
      fun n m => n.le m ∧ n ≠ m

    @[reducible] def gt (n m : ℕ) : Prop := lt m n

    theorem le_of_eq {n m : ℕ} : n = m → n.le m :=
      fun h => ⟨zero, n.add_zero.substr h.symm⟩

    theorem le_self : ∀ (n : ℕ), n.le n := fun _ => le_of_eq rfl

    theorem le_of_lt {n m : ℕ} : n.lt m → n.le m := And.left

    theorem ne_of_lt {n m : ℕ} : n.lt m → n ≠ m := And.right

    theorem not_lt_self : ∀ (n : ℕ), ¬ n.lt n := fun _ h => h.right rfl

    theorem lt_or_eq_of_le {n m : ℕ} : n.le m → n.lt m ∨ n = m :=
      fun h => (em (n = m)).elim (Or.inr ·) (Or.inl ⟨h, ·⟩)

    theorem eq_or_gt_of_ge {n m : ℕ} : n.ge m → n = m ∨ n.gt m :=
      fun h => (lt_or_eq_of_le h).elim (Or.inr ·) (Or.inl ·.symm)

    theorem zero_le : ∀(n : ℕ), zero.le n :=
      fun n => ⟨n, n.zero_add.symm⟩

    @[reducible] def pos (n : ℕ) : Prop := lt zero n

    theorem pos_iff_neq_zero : ∀(n : ℕ), n.pos ↔ n ≠ zero :=
      fun n => Iff.intro
        (fun h => (And.right h).symm)
        (fun h => And.intro n.zero_le h.symm)

    theorem le_succ : ∀ (n : ℕ), n.le n.succ :=
      fun n => ⟨one, n.add_one_eq_succ.symm⟩

    theorem lt_succ : ∀ (n : ℕ), n.lt n.succ :=
      fun n => ⟨n.le_succ, n.succ_ne_self.symm⟩

    theorem le_succ_le {n m : ℕ} : n.le m → n.le m.succ :=
      fun ⟨x, hx⟩ => ⟨x.succ, hx.substr (n.add_succ x).symm⟩

    theorem lt_succ_le {n m : ℕ} : n.le m → n.lt m.succ :=
      fun ⟨x, hx⟩ => ⟨le_succ_le ⟨x, hx⟩, fun he => (succ_ne_zero (add_right_eq_self_is_zero ((n.add_succ x).substr (hx.subst (motive := (·.succ = n)) he.symm)))).elim⟩

    theorem lt_succ_lt {n m : ℕ} : n.lt m → n.lt m.succ :=
      fun h => lt_succ_le (le_of_lt h)

    theorem lt_or_eq_or_gt : ∀ (n m : ℕ), n.lt m ∨ n = m ∨ n.gt m :=
      by
        intro n
        apply ind
        case h0 => exact Or.inr (eq_or_gt_of_ge n.zero_le)
        case h_ind =>
          intro m hor
          cases hor
          case inl h =>
            exact Or.inl (lt_succ_lt h)
          case inr h =>
            cases h
            case inl h =>
              exact h.substr (Or.inl (lt_succ m))
            case inr h =>
              apply Or.inr
              have ⟨⟨x, hx⟩, ne0⟩ := h
              cases x.zero_or_is_succ
              case inl x0 => rw [x0, add_zero] at hx; exact absurd hx.symm ne0
              case inr xn0 =>
                have ⟨x', hx'⟩ := xn0
                refine' eq_or_gt_of_ge ⟨x', _⟩
                rw [hx, hx', add_succ, succ_add]

    theorem le_or_ge : ∀ (n m : ℕ), n.le m ∨ n.ge m :=
      fun n m => (lt_or_eq_or_gt n m).elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (h.elim (le_of_eq ·.symm) (le_of_lt ·)))

    theorem le_or_gt : ∀ (n m : ℕ), n.le m ∨ n.gt m :=
      fun n m => (lt_or_eq_or_gt n m).elim (fun h => Or.inl (le_of_lt h)) (Or.elim · (fun h => Or.inl (le_of_eq h)) Or.inr)

    theorem lt_or_ge : ∀ (n m : ℕ), n.lt m ∨ n.ge m :=
      fun n m => (lt_or_eq_or_gt n m).elim Or.inl (fun h => Or.inr (h.elim (le_of_eq ·.symm) (le_of_lt ·)))

    theorem not_le_of_lt {a b : ℕ} : a.lt b → ¬(b.le a) :=
      by
      intro h ⟨x, hx⟩
      have ⟨x', hx'⟩ := le_of_lt h
      rw [hx', add_assoc] at hx
      rw [eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero hx.symm), add_zero] at hx'
      exact h.right hx'.symm

    theorem not_lt_of_le {a b : ℕ} : a.le b → ¬(b.lt a) :=
      imp_not_comm.mp not_le_of_lt

    theorem lt_of_not_le {a b : ℕ} : ¬(a.le b) → b.lt a :=
      ((le_or_gt a b).resolve_left ·)

    theorem le_of_not_lt {a b : ℕ} : ¬(a.lt b) → b.le a :=
      ((lt_or_ge a b).resolve_left ·)

    theorem le_of_not_le {a b : ℕ} : ¬(a.le b) → b.le a :=
      ((le_or_ge a b).resolve_left ·)

    theorem pos_is_succ {n : ℕ} : pos n → ∃ (m : ℕ), n = m.succ :=
      fun h => n.zero_or_is_succ.resolve_left (h.right ·.symm)

    theorem le_add (n m : ℕ) : n.le (n.add m) :=
      ⟨m, Eq.symm rfl⟩

    theorem le_add_right {a b : ℕ} : ∀ (c : ℕ), a.le b → a.le (b.add c) :=
      fun c ⟨x, hx⟩ => ⟨x.add c, hx.substr (add_assoc _ _ _)⟩

    theorem le_add_left {a b : ℕ} : ∀ (c : ℕ), a.le b → a.le (c.add b) :=
      fun c h => (add_comm _ _).substr (le_add_right c h)

    theorem add_le_self_is_zero {a b : ℕ} : (a.add b).le a → b = zero :=
      fun ⟨x, hx⟩ => eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero ((a.add_assoc b x).subst hx).symm)

    theorem lt_add_right {a b : ℕ} : ∀ (c : ℕ), a.lt b → a.lt (b.add c) := by
      intro c h;
      refine' And.intro (le_add_right _ (le_of_lt h)) _
      intro h'
      have ⟨x, hx⟩ := le_of_lt h
      rw [hx, add_assoc] at h'
      rw [eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero h'.symm), add_zero] at hx
      rw [hx] at h
      exact not_lt_self a h

    theorem lt_add_left {a b : ℕ} : ∀ (c : ℕ), a.lt b → a.lt (c.add b) :=
      fun c h => (add_comm c b).substr (lt_add_right c h)

    theorem pos_add_neq_self {n : ℕ} : pos n → ∀ (m : ℕ), n.add m ≠ m :=
      fun h _ h' => succ_ne_zero ((add_left_eq_self_is_zero h').subst (pos_is_succ h).choose_spec.symm)

    theorem add_pos_neq_self {n : ℕ} : pos n → ∀ (m : ℕ), m.add n ≠ m :=
      fun h _ h' => succ_ne_zero ((add_right_eq_self_is_zero h').subst (pos_is_succ h).choose_spec.symm)

    theorem add_le_add_iff_left {a b c : ℕ} : (a.add b).le (a.add c) ↔ b.le c := by
      unfold le
      apply Iff.intro
      <;> intro ⟨x, h⟩
      <;> exists x
      <;> apply (add_right_inj a).mp
      <;> rw [h, add_assoc]

    theorem add_le_add_iff_right {a b c : ℕ} : (a.add c).le (b.add c) ↔ a.le b := by
      rw [add_comm, add_comm b, add_le_add_iff_left]

  -- #check Nat.lt_or
    -- theorem

    section num

      -- theorem

    end num
    -- def ge

  end comp

    theorem mul_left_inj {a b c : ℕ} (hc : c ≠ zero): a.mul c = b.mul c ↔ a = b := by
      apply Iff.intro
      case mp =>
        intro h
        have p1 (a b c : ℕ) (hc : c ≠ zero) (hl : a.le b) : a.mul c = b.mul c → a = b := by
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

    theorem mul_right_inj {a b c : ℕ} (hc : c ≠ zero) : c.mul a = c.mul b ↔ a = b := by
      simp only [c.mul_comm]
      exact mul_left_inj hc

end ℕ
end my
-- noncomputable
