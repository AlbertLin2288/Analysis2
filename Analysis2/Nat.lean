import Analysis2.CompStructure.OrderedCommSemiRing
noncomputable section
namespace my
open Classical
open Comp
open Zero One
open Monoid CommMonoid SemiRing CommSemiRing
open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing

axiom ℕ : Type

namespace ℕ

  axiom _zero : ℕ

  @[default_instance] instance : Zero ℕ := ⟨_zero⟩

  axiom succ : ℕ → ℕ

  axiom succ_ne_zero : ¬(succ a = zero)

  axiom succ_inj (a b : ℕ) : succ a = succ b → a = b

  axiom ind' {h : ℕ → Prop} (h0 : h zero) (h_ind : ∀(a : ℕ), h a → h (succ a)) : ∀(a : ℕ), h a



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
        fun h => succ_ne_zero (h.substr one_eq_succ_zero)


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

    instance : Add ℕ := {add}

    theorem add_zero : ∀(n : ℕ), n + zero = n :=
      fun _ => (ind_spec _ _).left

    theorem add_succ : ∀(n m : ℕ), n + m.succ = (n + m).succ :=
      fun _ m => (ind_spec _ _).right m

    theorem _zero_add : ∀(n : ℕ), zero + n = n :=
      ind zero.add_zero (fun m (hm : zero + m = m) => Eq.subst (motive := (zero + m.succ = succ .)) hm (add_succ zero m))

    theorem succ_add : ∀(n m : ℕ), n.succ + m = (n + m).succ := by
        intro n
        apply ind
        simp only [add_zero]
        intro a ha
        simp only [add_succ, ha]

    theorem add_comm : ∀(n m : ℕ), n + m = m + n := by
      intro n
      apply ind
      case h0 => simp only [add_zero, _zero_add]
      case h_ind =>
        intro m hm
        simp only [add_succ, succ_add, hm]

    theorem add_assoc : ∀ (a b c : ℕ), (a + b) + c = a + (b + c) := by
      intro a b
      apply ind
      case h0 => simp only [add_zero]
      case h_ind =>
        intro c hc
        simp only [add_succ, hc]

    instance : CommMonoid ℕ where
      _add_zero := add_zero
      _add_assoc := add_assoc
      add_comm := add_comm

    theorem add_left_inj {a b : ℕ} : ∀ (c : ℕ), a + c = b + c ↔ a = b := by
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

    theorem add_right_inj {a b : ℕ} : ∀ (c : ℕ), c + a = c + b ↔ a = b := by
      intro c
      simp only [c.add_comm]
      exact add_left_inj c

    theorem eq_zero_of_add_eq_zero_left {a b : ℕ} : a + b = zero → a = zero :=
      ind (h := fun b => a + b = zero → a = zero) (fun h => h.subst a.add_zero.symm) (fun b' _ h => (succ_ne_zero (h.subst (a.add_succ b').symm)).elim) b

    theorem eq_zero_of_add_eq_zero_right {a b : ℕ} : a + b = zero → b = zero :=
      fun h => eq_zero_of_add_eq_zero_left (h.subst (a.add_comm b).symm)

    theorem add_right_eq_self_is_zero {a b : ℕ} : a + b = a → b = zero :=
      ind (h := fun a' => a' + b = a' → b = zero) (fun h => h.subst (zero_add b).symm) (fun a' h h' => h (succ_inj _ a' (h'.subst (a'.succ_add _).symm))) a

    theorem add_left_eq_self_is_zero {a b : ℕ} : a + b = b → a = zero :=
      (add_comm _ _).substr add_right_eq_self_is_zero

    section num

      theorem add_one_eq_succ : ∀ (n : ℕ), n + one = n.succ := by
        intro n
        rw [one_eq_succ_zero, add_succ, add_zero]

    end num

  end add

  section mul

    def mul : ℕ → ℕ → ℕ :=
      fun a => ind zero (fun _ x => x + a)

    instance : Mul ℕ := {mul}

    theorem mul_zero : ∀(n : ℕ), n * zero = zero :=
      fun _ => (ind_spec _ _).left

    theorem mul_succ : ∀(n m : ℕ), n * m.succ = (n * m) + n :=
      fun _ m => (ind_spec _ _).right m

    theorem mul_one : ∀(n : ℕ), n * one = n := by
      intro n
      rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

    theorem _zero_mul : ∀(n : ℕ), zero * n = zero :=
      ind (ℕ.mul_zero zero) fun n hn => Eq.substr (ℕ.mul_succ zero n) (Eq.substr (zero * n).add_zero hn)

    theorem succ_mul : ∀(n m : ℕ), n.succ * m = (n * m) + m := by
      intro n
      apply ind
      case h0 => simp only [mul_zero, add_zero]
      case h_ind =>
        intro m hm
        simp only [mul_succ, hm, add_succ, add_right_comm]

    theorem mul_comm : ∀(n m : ℕ), n * m = m * n := by
      intro n
      apply ind
      case h0 => simp only [mul_zero,_zero_mul]
      case h_ind =>
        intro m hm
        simp only [mul_succ, succ_mul, hm]

    theorem add_mul : ∀(a b c : ℕ), (a + b) * c = (a * c) + (b * c) := by
      intro a b
      apply ind
      case h0 => simp only [mul_zero, add_zero]
      case h_ind =>
        intro c hc
        rw [
          mul_succ, mul_succ, mul_succ, hc,
          ← add_assoc,
          ← add_assoc,
          add_right_comm (a * c)
        ]

    theorem _mul_add : ∀(a b c : ℕ), a * (b + c) = (a * b) + (a * c) := by
      intro a _ _
      rw [mul_comm, add_mul, mul_comm a, mul_comm a]

    theorem mul_assoc : ∀ (a b c : ℕ), (a * b) * c = a * (b * c) := by
      intro a b
      apply ind
      case h0 => simp only [mul_zero]
      case h_ind =>
        intro c hc
        simp only [mul_succ, hc, _mul_add]

    instance : CommSemiRing ℕ where
      _mul_one := mul_one
      _mul_assoc := mul_assoc
      _mul_zero := mul_zero
      _add_mul := add_mul
      _zero_ne_one := zero_ne_one
      mul_comm := mul_comm

    theorem mul_eq_zero {a b : ℕ} : a * b = zero → a = zero ∨ b = zero :=
      fun h => (em (a = zero)).elim Or.inl fun h0 => Or.inr (eq_zero_of_add_eq_zero_right (((nonzero_is_succ h0).choose_spec.subst (motive := (· * b = zero)) h).subst (ℕ.succ_mul _ _).symm))

  end mul

  section comp

    def le : ℕ → ℕ → Prop :=
      fun n m => ∃(x : ℕ), m = n + x

    theorem le_refl : ∀ (a : ℕ), a.le a :=
      (⟨zero, ·.add_zero.symm⟩)

    theorem le_trans : ∀(a b c : ℕ), a.le b → b.le c → a.le c :=
      fun _ _ _ ⟨x1, hx1⟩ ⟨x2, hx2⟩ => ⟨x1 + x2, hx2.substr (hx1.substr (add_assoc _ x1 x2))⟩

    theorem le_antisymm : ∀(a b : ℕ), a.le b → b.le a → a = b := by
      intro _ _ ⟨_, hx⟩ ⟨_, hx'⟩
      rw [hx, add_assoc] at hx'
      replace hx' := eq_zero_of_add_eq_zero_left (add_right_eq_self_is_zero hx'.symm)
      rw [hx, hx', add_zero]

    theorem le_total : ∀(a b : ℕ), a.le b ∨ b.le a := by
      intro a b
      apply byContradiction
      simp only [not_or]
      intro ⟨hnab, hnba⟩
      have h : ∀(n : ℕ), ¬(a.le (b + n)) := ind (b.add_zero.substr hnab) (by
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
      {le, le_refl, le_trans, le_antisymm, le_total}

    theorem zero_le : ∀(n : ℕ), zero ≤ n :=
      fun n => ⟨n, (zero_add n).symm⟩

    @[reducible] def pos (n : ℕ) : Prop := zero < n

    theorem pos_iff_neq_zero : ∀(n : ℕ), n.pos ↔ n ≠ zero :=
      fun n => Iff.intro
        (fun h => (ne_of_lt h).symm)
        (fun h => lt_of_le_ne n.zero_le h.symm)

    theorem le_succ : ∀ (n : ℕ), n ≤ n.succ :=
      fun n => ⟨one, n.add_one_eq_succ.symm⟩

    theorem lt_succ : ∀ (n : ℕ), n < n.succ :=
      fun n => lt_of_le_ne n.le_succ n.succ_ne_self.symm

    theorem le_succ_le {n m : ℕ} : n ≤ m → n ≤ m.succ :=
      fun ⟨x, hx⟩ => ⟨x.succ, hx.substr (n.add_succ x).symm⟩

    theorem lt_succ_le {n m : ℕ} : n ≤ m → n < m.succ :=
      fun ⟨x, hx⟩ => lt_of_le_ne (le_succ_le ⟨x, hx⟩) fun he => (succ_ne_zero (add_right_eq_self_is_zero ((n.add_succ x).substr (hx.subst (motive := (·.succ = n)) he.symm)))).elim

    theorem lt_succ_lt {n m : ℕ} : n< m → n < m.succ :=
      fun h => lt_succ_le (le_of_lt h)

    theorem pos_is_succ {n : ℕ} : pos n → ∃ (m : ℕ), n = m.succ :=
      fun h => n.zero_or_is_succ.resolve_left (ne_of_lt h ·.symm)

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
      <;> apply (add_right_inj a).mp
      <;> rw [h, add_assoc]

    theorem add_le_add_of_le_left (a : ℕ) {b c : ℕ} : b ≤ c → (a + b) ≤ (a + c) :=
      add_le_add_iff_left.mpr

    theorem le_of_add_le_add_left {a b c : ℕ} :  (a + b) ≤ (a + c) → b ≤ c :=
      add_le_add_iff_left.mp

    theorem add_le_add_iff_right {a b c : ℕ} : (a + c) ≤ (b + c) ↔ a ≤ b := by
      rw [add_comm, add_comm b, add_le_add_iff_left]


    theorem le_of_add_le_add_right {a b c : ℕ} :  (a + c) ≤ (b + c) → a ≤ b :=
      add_le_add_iff_right.mp

    @[default_instance] instance : OrderedCommMonoid ℕ where
      _add_le_add_left := (@add_le_add_of_le_left · _ _)

    theorem add_le_le_le {a b c d : ℕ} : (a ≤ b) → (c ≤ d) → (a + c) ≤ (b + d) :=
      fun h1 h2 => le_trans _ _ _ ((add_le_add_iff_right (c := c)).mpr h1) ((add_le_add_iff_left (a := b)).mpr h2)

    theorem zero_le_one : zero ≤ one := zero.le_succ

    theorem zero_lt_one : zero < one := zero.lt_succ

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
        have p1 (a b c : ℕ) (hc : c ≠ zero) (hl : a ≤ b) : a * c = b * c → a = b := by
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
end my
