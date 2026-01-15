import Analysis2.Nat
import Analysis2.CompStructure.OrderedField
-- import Analysis2.Int
-- import Analysis2.Rat

noncomputable section
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing' Field
open Comp
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing OrderedCommRing' OrderedField
open Zero One Abs

-- open my renaming EquivalentClass → EC

@[reducible] def Seq (α : Type) : Type := ℕ → α

namespace Seq

  @[reducible] instance {α : Type} [Zero α] : Zero (Seq α) :=
    ⟨fun _ => zero⟩

  @[reducible] instance {α : Type} [One α] : One (Seq α) :=
    ⟨fun _ => one⟩

  @[reducible] instance {α : Type} [Add α] : Add (Seq α) :=
    ⟨fun s1 s2 n => (s1 n) + (s2 n)⟩

  theorem add_def {α : Type} [Add α] {s s' : Seq α} : s + s' = fun n => s n + s' n := rfl

  @[reducible] instance {α : Type} [Neg α] : Neg (Seq α) :=
    ⟨fun s n => - (s n)⟩

  theorem neg_def {α : Type} [Neg α] {s : Seq α} : - s = fun n => - s n := rfl

  @[reducible] instance {α : Type} [Zero α] [Neg α] [Comp α] : Abs (Seq α) :=
    ⟨fun s n => abs (s n)⟩

  theorem abs_def {α : Type} [Zero α] [Neg α] [Comp α] {s : Seq α} : abs s = fun n => abs (s n) := rfl

  @[reducible] instance {α : Type} [Mul α] : Mul (Seq α) :=
    ⟨fun s1 s2 n => (s1 n) * (s2 n)⟩

  theorem mul_def {α : Type} [Mul α] {s s' : Seq α} : s * s' = fun n => s n * s' n := rfl

  section
    variable {α : Type} [Zero α] [Add α] [CommMonoid α]

    instance : CommMonoid (Seq α) where
      _add_zero := fun _ => funext fun _ => add_zero _
      _add_assoc := fun _ _ _ => funext fun _ => add_assoc _ _ _
      add_comm := fun _ _ => funext fun _ => add_comm _ _

    variable [Neg α] [CommGroup α]

    instance : CommGroup (Seq α) where
      add_neg := fun _ => funext fun _ => add_neg _

    variable [One α] [Mul α] [CommRing α]

    instance : CommRing (Seq α) where
      _mul_one := fun _ => funext fun _ => mul_one _
      _mul_assoc := fun _ _ _ => funext fun _ => mul_assoc _ _ _
      _add_mul := fun _ _ _ => funext fun _ => add_mul _ _ _
      _zero_ne_one := fun h => zero_ne_one ((funext_iff.mp h) zero)
      _mul_comm := fun _ _ => funext fun _ => mul_comm _ _

  end

  section Seq

    variable {α : Type}

    @[reducible] def const_seq : α → Seq α := fun a _ => a

    def is_const  : Seq α → Prop :=
      fun s => ∃(a : α), ∀(n : ℕ), s n = a

    theorem is_const_seq_of_is_const {s : Seq α} (h : is_const s) : s = const_seq (s zero) :=
      funext (((h.choose_spec zero) ▸ h.choose_spec) ·)

    theorem is_const_of_const_seq {a : Seq α} : is_const (const_seq a) :=
      ⟨a, fun _ => rfl⟩

    theorem zero_is_const [Zero α] : is_const (zero : Seq α) :=
      ⟨zero, fun _ => rfl⟩

    theorem zero_is_const_zero [Zero α] : zero = const_seq zero :=
      is_const_seq_of_is_const zero_is_const

    theorem one_is_const [One α] : is_const (one : Seq α) :=
      ⟨one, fun _ => rfl⟩

    theorem one_is_const_one [One α] : one = const_seq one :=
      is_const_seq_of_is_const one_is_const

  end Seq

end Seq

class Cauchy_type (α : Type) [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommGroup α]

@[reducible] def is_cauchy {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α]
  [OrderedCommMonoid α] [OrderedCommGroup α] [OrderedCommGroup α] : Seq α → Prop :=
    fun s => ∀(ε : α), ε > zero → ∃(N :ℕ), ∀(n m : ℕ), n ≥ N → m ≥ N → abs ((s n) - (s m)) < ε

section conv

  open Seq

  variable {α : Type} [Zero α] [Add α] [Neg α] [Comp α]-- [CommMonoid α] [CommGroup α]
    --[OrderedCommMonoid α] -- [OrderedCommGroup α] -- [OrderedCommGroup α]

  @[reducible] def conv_to : Seq α → α → Prop :=
      fun s a => ∀(ε : α), ε > zero → ∃(N :ℕ), ∀(n : ℕ), n ≥ N → abs ((s n) - a) < ε

  @[reducible] def is_conv : Seq α → Prop :=
      fun s => ∃(a : α), conv_to s a

  theorem is_conv_of_conv_to {s : Seq α} {a : α} : conv_to s a → is_conv s := (⟨a, ·⟩)

  variable [CommMonoid α] [CommGroup α]

  theorem conv_to_of_const : ∀(a : α), conv_to (const_seq a) a :=
    fun a _ h => ⟨zero, fun _ _ => (add_neg a) ▸ (abs_of_zero.substr h)⟩

  theorem conv_to_of_const' : ∀(s : Seq α), is_const s → conv_to s (s zero) :=
    fun s h => (is_const_seq_of_is_const h) ▸ (conv_to_of_const (s zero))

  theorem conv_of_const : ∀(a : α), is_conv (const_seq a) :=
    fun a => is_conv_of_conv_to (conv_to_of_const a)

  theorem conv_of_const' : ∀(s : Seq α), is_const s → is_conv s :=
    fun s h => is_conv_of_conv_to (conv_to_of_const' s h)

  variable [OrderedCommMonoid α]

  theorem conv_to_neg_of_neg {s : Seq α} {a : α} : conv_to s a  → conv_to (-s) (-a) := by
    intro h ε hε
    replace ⟨x, hx⟩ := h ε hε
    refine' ⟨x, _⟩
    intro n
    rw [neg_def, ←neg_sum, abs_neg_eq_abs]
    exact hx n

  theorem is_conv_of_neg {s : Seq α} : is_conv s → is_conv (-s) :=
    fun h => is_conv_of_conv_to (conv_to_neg_of_neg h.choose_spec)

  theorem conv_to_sum_of_sum {s s' : Seq α} {a a' : α} : conv_to s a → conv_to s' a' → conv_to (s + s') (a + a') := by
    intro h h' ε hε
    by_cases h'' : ∃ε1 : α, zero < ε1 ∧ ε1 < ε
    case neg =>
      replace ⟨x, hx⟩ := h ε hε
      replace ⟨x', hx'⟩ := h' ε hε
      let xm := max x x'
      exists xm
      intro n hn
      replace hx := abs_eq_zero_iff.mp (le_antisymm _ _ (le_of_not_lt (not_and'.mp (not_exists.mp h'' (abs (s n + -a))) (hx n (le_trans _ _ _ max_ge_fst hn)))) (abs_nonneg _))
      replace hx' := abs_eq_zero_iff.mp (le_antisymm _ _ (le_of_not_lt (not_and'.mp (not_exists.mp h'' (abs (s' n + -a'))) (hx' n (le_trans _ _ _ max_ge_snd hn)))) (abs_nonneg _))
      rw [neg_sum, add_def, add_assoc, add_left_comm (s' n), hx', add_zero, hx, abs_of_zero]
      exact hε
    case pos =>
      replace ⟨ε', ⟨hε', hε''⟩⟩ := h''
      let ε'' := ε - ε'
      replace hε'' : zero < ε'' := sub_pos_of_lt hε''
      have hεε : ε' + ε'' = ε := by unfold ε'';rw [add_comm,sub_add_cancel]
      replace ⟨x, hx⟩ := h ε' hε'
      replace ⟨x', hx'⟩ := h' ε'' hε''
      let xm := max x x'
      exists xm
      intro n hn
      replace hx := hx n (le_trans _ _ _ max_ge_fst hn)
      replace hx' := hx' n (le_trans _ _ _ max_ge_snd hn)
      replace hx := hεε ▸ (lt_of_le_lt (triangle_add_le_add _ _) (lt_of_add_lt_lt hx hx'))
      simp only [add_def, neg_sum]
      ac_nf at hx |-

  theorem is_conv_of_sum {s s' : Seq α} : is_conv s → is_conv s' → is_conv (s + s') :=
    fun h h' => is_conv_of_conv_to (conv_to_sum_of_sum h.choose_spec h'.choose_spec)

  variable [OrderedCommGroup α]

  theorem conv_is_cauchy {s : Seq α} : is_conv s → is_cauchy s := by
    intro h ε hε
    replace ⟨a, h⟩ := h
    by_cases h' : ∃ε1 : α, zero < ε1 ∧ ε1 < ε
    case neg =>
      replace ⟨x, hx⟩ := h ε hε
      exists x
      replace hx : ∀ (n : ℕ), x ≤ n → s n = a := by
        intro n hn
        exact eq_of_sub_eq_zero _ _ (abs_eq_zero_iff.mp (le_antisymm _ _ (le_of_not_lt (not_and'.mp (not_exists.mp h' _) (hx n hn))) (abs_nonneg _)))
      intro n m hn hm
      rw [hx n hn, hx m hm, add_neg, abs_of_zero]
      exact hε
    case pos =>
      replace ⟨ε', ⟨hε', hε''⟩⟩ := h'
      replace ⟨ε', ⟨hε0, hε'⟩⟩ : ∃(ε' : α), ε' > zero ∧ ε' + ε' ≤ ε := (lt_or_ge (ε' + ε') ε).elim (⟨ε', hε', le_of_lt ·⟩) fun hε2' => ⟨ε - ε', ⟨sub_pos_of_lt hε'', add_assoc ε _ _ ▸ (add_zero ε).subst (add_le_add_left ε (add_left_comm ε _ _ ▸ neg_sum ε' ε' ▸ (sub_nonpos_of_le hε2')))⟩⟩
      replace ⟨N, h⟩ := h ε' hε0
      exists N
      intro n m hn hm
      have h := lt_of_le_lt (triangle_sub_le_add _ _) (lt_of_lt_le (lt_of_add_lt_lt (h n hn) (h m hm)) hε')
      rw [neg_sub, ←add_assoc, sub_add_cancel] at h
      exact h

end conv

section cauchy

  open Seq
  variable {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α]
    [OrderedCommMonoid α] [OrderedCommGroup α]

  theorem is_cauchy_of_const : ∀(a : α), is_cauchy (const_seq a) :=
    fun a => conv_is_cauchy (conv_of_const a)

  theorem is_cauchy_of_const' : ∀(s : Seq α), is_const s → is_cauchy s :=
    fun s h => conv_is_cauchy (conv_of_const' s h)

  theorem is_cauchy_of_neg {s : Seq α} : is_cauchy s → is_cauchy (-s) := by
    intro h ε
    simp only [neg_def, ←neg_sum, abs_neg_eq_abs]
    exact h ε

  theorem is_cauchy_of_abs {s : Seq α} : is_cauchy s → is_cauchy (abs s) :=
   fun h ε hε => ⟨(h ε hε).choose, fun n m hn hm => lt_of_le_lt (triangle_sub_ge_abs_sub (s n) (s m)) ((h ε hε).choose_spec n m hn hm)⟩

  theorem is_cauchy_of_sum {s s' : Seq α} : is_cauchy s → is_cauchy s' → is_cauchy (s + s') := by
    intro h h' ε hε
    by_cases h'' : ∃ε1 : α, zero < ε1 ∧ ε1 < ε
    case neg =>
      replace ⟨x, hx⟩ := h ε hε
      replace ⟨x', hx'⟩ := h' ε hε
      let xm := max x x'
      exists xm
      intro n m hn hm
      replace h'' := fun {x} (h : abs x < ε) => abs_eq_zero_iff.mp (le_antisymm _ _ (le_of_not_lt (not_and'.mp (not_exists.mp h'' (abs x)) h)) (abs_nonneg x))
      replace hx := h'' (hx n m (le_trans _ _ _ max_ge_fst hn) (le_trans _ _ _ max_ge_fst hm))
      replace hx' := h'' (hx' n m (le_trans _ _ _ max_ge_snd hn) (le_trans _ _ _ max_ge_snd hm))
      rw [add_def, neg_sum, add_assoc, add_left_comm (s' n), hx', add_zero, hx, abs_of_zero]
      exact hε
    case pos =>
      replace ⟨ε', ⟨hε', hε''⟩⟩ := h''
      let ε'' := ε - ε'
      replace hε'' : zero < ε'' := sub_pos_of_lt hε''
      have hεε : ε' + ε'' = ε := by unfold ε'';rw [add_comm,sub_add_cancel]
      replace ⟨x, hx⟩ := h ε' hε'
      replace ⟨x', hx'⟩ := h' ε'' hε''
      let xm := max x x'
      exists xm
      intro n m hn hm
      replace hx := hx n m (le_trans _ _ _ max_ge_fst hn) (le_trans _ _ _ max_ge_fst hm)
      replace hx' := hx' n m (le_trans _ _ _ max_ge_snd hn) (le_trans _ _ _ max_ge_snd hm)
      replace hx := hεε ▸ (lt_of_le_lt (triangle_add_le_add _ _) (lt_of_add_lt_lt hx hx'))
      simp only [add_def, neg_sum]
      ac_nf at hx |-

  variable [One α] [Mul α] [Inv α] [CommRing α] [Field α]
    [OrderedCommRing α] [OrderedField α]

  private def two := (one : α) + one
  set_option linter.unusedSectionVars false in
  private theorem zero_lt_two : (zero:α) < two :=
    pos_add_pos_is_pos zero_lt_one (zero_lt_one (α:=α))

  private theorem two_ne_zero : two ≠ (zero:α) :=
    (ne_of_lt (zero_lt_two (α := α))).symm

  set_option linter.unusedSectionVars false in
  private theorem mul_two_eq_add (a : α) : a * two = a + a := by
    unfold two;simp only [mul_add,mul_one]

  private def half := ⟨(two:α), two_ne_zero⟩⁻¹

  private theorem half_pos : (zero : α) < half :=
    inv_pos_is_pos zero_lt_two

  private theorem add_half : half + half = (one : α) :=
    Eq.trans (mul_two_eq_add half).symm (inv_mul_cancel two two_ne_zero)

  omit [OrderedField α] in
  theorem is_cauchy_of_mul {s s' : Seq α} : is_cauchy s → is_cauchy s' → is_cauchy (s * s') := by
    intro h h' ε hε
    conv in abs _ =>
      rw [mul_def]
      simp only
      rw [←add_zero (_*_), ←neg_add (s n * s' m), ←add_assoc, add_assoc]
      rw [←mul_neg_right, ←mul_neg_left, ←mul_add, ←add_mul]
    have ⟨N2, hN2⟩ := h one zero_lt_one
    have ⟨N2', hN2'⟩ := h' one zero_lt_one
    let N2m := max N2 N2'
    let a := s N2m
    let a' := s' N2m
    replace hN2 := fun m (hm:N2m≤m) => lt_add_of_sub_left_lt (lt_of_le_lt (triangle_sub_ge_sub _ _) (hN2 m N2m (le_of_le_le max_ge_fst hm) max_ge_fst))
    replace hN2' := fun m (hm:N2m≤m) => lt_add_of_sub_left_lt (lt_of_le_lt (triangle_sub_ge_sub _ _) (hN2' m N2m (le_of_le_le max_ge_snd hm) max_ge_snd))
    let d := (abs (s N2m) + one) + (abs (s' N2m) + one)
    have hd : d > zero := pos_add_pos_is_pos (nonneg_add_pos_is_pos (abs_nonneg _) zero_lt_one) (nonneg_add_pos_is_pos (abs_nonneg _) zero_lt_one)
    let ε2 := ε * ⟨d, ne_of_gt hd⟩⁻¹
    have hε2 : zero < ε2 := mul_pos hε (inv_pos_is_pos hd)
    have ⟨N, hN⟩ := h ε2 hε2
    have ⟨N', hN'⟩ := h' ε2 hε2
    let Nm := max N N'
    let Nm' := max Nm N2m
    exists Nm'
    intro n m hn hm
    replace hN := hN n m (le_of_le_le_le max_ge_fst max_ge_fst hn) (le_of_le_le_le max_ge_fst max_ge_fst hm)
    replace hN' := hN' n m (le_of_le_le_le max_ge_snd max_ge_fst hn) (le_of_le_le_le max_ge_snd max_ge_fst hm)
    replace hN2 := hN2 n (le_of_le_le max_ge_snd hn)
    replace hN2' := hN2' m (le_of_le_le max_ge_snd hm)
    refine' lt_of_le_lt_eq (triangle_add_le_add _ _) _ (mul_mul_inv_cancel_left2 (ne_of_gt hd))
    rw [abs_of_mul_eq_mul_abs, abs_of_mul_eq_mul_abs, add_mul, mul_comm _ (abs (s' m))]
    exact lt_of_add_lt_lt
      (lt_of_mul_nonneg_nonneg_lt_lt (abs_nonneg _) (abs_nonneg _) hN2 hN')
      (lt_of_mul_nonneg_nonneg_lt_lt (abs_nonneg _) (abs_nonneg _) hN2' hN)

end cauchy


-- class Seq_ring_type (α : Type) extends
--   CommRing α,
--   LE α, LT α,
--   IsLinearOrder α, Std.LawfulOrderLT α,
--   OrderedRing α

-- namespace Seq_ring_type
--   instance {α : Type} [Seq_ring_type α] : Seq_type α where
-- end Seq_ring_type

-- class Seq_field_type (α : Type) extends
--   Field α,
--   LE α, LT α,
--   IsLinearOrder α, Std.LawfulOrderLT α,
--   OrderedRing α

-- namespace Seq_field_type
--   instance {α : Type} [Seq_field_type α] : Seq_ring_type α where
-- end Seq_field_type


-- namespace Sequ

--   section Group

--     variable {α : Type} [Seq_type α]

--     protected def add: Seq α → Seq α → Seq α :=
--       fun s1 s2 n => (s1 n) + (s2 n)

--     instance : Add (Seq α) where
--       add := Sequ.add

--     theorem add_def {a b : Seq α} : a + b = Sequ.add a b := rfl

--     protected def zero : Seq α := fun _ => OfNat.ofNat 0

--     instance : Zero (Seq α) where
--       zero := Sequ.zero

--     theorem zero_def : (0 : Seq α) = @Sequ.zero α _ := rfl

--     theorem add_zero (a : Seq α) : a + 0 = a := by
--       rw [add_def, zero_def]
--       unfold Sequ.add Sequ.zero
--       simp only [AddCommMonoid.add_zero]

--     theorem add_comm (a b : Seq α) : a + b = b + a := by
--       repeat rw [add_def]
--       unfold Sequ.add
--       simp only [AddCommMonoid.add_comm]

--     theorem add_assoc (a b c : Seq α) : (a + b) + c = a + (b + c) := by
--       repeat rw [add_def]
--       unfold Sequ.add
--       simp [AddCommMonoid.add_assoc]

--     protected def neg: Seq α → Seq α := fun s n => -s n

--     instance : Neg (Seq α) where
--       neg := Sequ.neg

--     theorem neg_def {a : Seq α} : -a = Sequ.neg a := rfl

--     instance : AddCommMonoid (Seq α) where
--       add_zero := add_zero
--       add_comm := add_comm
--       add_assoc := add_assoc

--     protected def sub : Seq α → Seq α → Seq α :=
--       fun a => (fun b => Sequ.add a (Sequ.neg b))

--     instance : Sub (Seq α) where
--       sub := Sequ.sub

--     theorem sub_def (a b : Seq α) : a - b = Sequ.sub a b := rfl

--     theorem neg_add_cancel (a : Seq α) : -a + a = 0 := by
--       rw [add_def, neg_def, zero_def]
--       unfold Sequ.add Sequ.neg Sequ.zero
--       simp only [AddCommGroup.neg_add_cancel]

--     theorem sub_eq_add_neg (a b : Seq α) : a - b = a + -b := by
--       rw [add_def, sub_def, neg_def]
--       unfold Sequ.sub
--       rfl

--     instance : AddCommGroup (Seq α) where
--     neg_add_cancel := neg_add_cancel
--     sub_eq_add_neg := sub_eq_add_neg


--   end Group


--   section Ring

--     variable {α : Type} [Seq_ring_type α]


--     -- Semiring

--     protected def mul : Seq α → Seq α → Seq α :=
--       fun a b n => a n * b n

--     instance : Mul (Seq α) where
--       mul := Sequ.mul

--     theorem mul_def {a b : Seq α} : a * b = Sequ.mul a b := rfl

--     protected def ofNat : Nat → Seq α :=
--       fun n _ => OfNat.ofNat n

--     @[default_instance] instance : NatCast (Seq α) where
--       natCast := Sequ.ofNat

--     theorem natCast_def {a : Nat} :
--       Nat.cast a = Sequ.ofNat (α := α) a := rfl

--     instance (n : Nat) : OfNat (Seq α) n where
--       ofNat := Sequ.ofNat n

--     theorem ofNat_def (a : Nat) :
--       OfNat.ofNat a = Sequ.ofNat (α := α) a := rfl

--     protected def nsmul : Nat → Seq α → Seq α :=
--       fun n a m => Semiring.nsmul.smul n (a m)

--     instance : SMul Nat (Seq α) where
--       smul := Sequ.nsmul

--     theorem nsmul_def {n : Nat} {a : Seq α} : n • a = Sequ.nsmul n a := rfl

--     protected def hPow : Seq α → Nat → Seq α :=
--       fun a n m => Semiring.npow.hPow (a m) n

--     instance : HPow (Seq α) Nat (Seq α) where
--       hPow := Sequ.hPow

--     theorem mul_assoc (a b c : Seq α) :  a * b * c = a * (b * c) := by
--       funext n
--       exact Semiring.mul_assoc (a n) (b n) (c n)

--     theorem mul_one (a : Seq α) : a * 1 = a := by
--       funext n
--       exact Semiring.mul_one (a n)

--     theorem one_mul (a : Seq α) : 1 * a = a := by
--       funext n
--       exact Semiring.one_mul (a n)

--     theorem left_distrib (a b c : Seq α) :
--       a * (b + c) = a * b + a * c := by
--         funext n
--         exact Semiring.left_distrib (a n) (b n) (c n)

--     theorem right_distrib (a b c : Seq α) :
--       (a + b) * c = a * c + b * c := by
--         funext n
--         exact Semiring.right_distrib (a n) (b n) (c n)

--     theorem zero_mul (a : Seq α) : 0 * a = 0 := by
--       funext n
--       exact Semiring.zero_mul (a n)

--     theorem mul_zero (a : Seq α) : a * 0 = 0 := by
--       funext n
--       exact Semiring.mul_zero (a n)

--     theorem pow_zero (a : Seq α) : a ^ 0 = 1 := by
--       funext n
--       exact Semiring.pow_zero (a n)

--     theorem pow_succ (a : Seq α) (n : Nat) :
--       a ^ (n + 1) = (a ^ n) * a := by
--         funext x
--         exact Semiring.pow_succ (a x) n

--     theorem ofNat_succ (a : Nat) :
--       OfNat.ofNat (α := Seq α) (a + 1) = OfNat.ofNat a + 1 := by
--       funext n
--       exact Semiring.ofNat_succ a

--     theorem ofNat_eq_natCast (n : Nat) :
--       OfNat.ofNat (α := Seq α) n = Nat.cast n := rfl

--     theorem nsmul_eq_natCast_mul (n : Nat) (a : Seq α) :
--       n • a = Nat.cast n * a := by
--       funext x
--       rw [nsmul_def, Sequ.nsmul, mul_def, Sequ.mul,
--         natCast_def, Sequ.ofNat, Semiring.ofNat_eq_natCast]
--       exact Semiring.nsmul_eq_natCast_mul n (a x)

--     instance : Semiring (Seq α) where
--       add_zero := Sequ.add_zero
--       add_comm := Sequ.add_comm
--       add_assoc := Sequ.add_assoc
--       mul_assoc := Sequ.mul_assoc
--       mul_one := mul_one
--       one_mul := one_mul
--       left_distrib := left_distrib
--       right_distrib := right_distrib
--       zero_mul := zero_mul
--       mul_zero := mul_zero
--       pow_zero := pow_zero
--       pow_succ := pow_succ
--       ofNat_succ := ofNat_succ
--       ofNat_eq_natCast := ofNat_eq_natCast
--       nsmul_eq_natCast_mul := nsmul_eq_natCast_mul


--     -- Ring

--     protected def intCast : Int → Seq α :=
--       fun i _ => Ring.intCast.intCast i

--     @[default_instance] instance : IntCast (Seq α) where
--       intCast := Sequ.intCast

--     theorem intCast_def {i : Int} :
--       Int.cast i = Sequ.intCast (α := α) i := rfl

--     protected def zsmul : Int → Seq α → Seq α :=
--       fun i a n => Ring.zsmul.smul i (a n)

--     instance : SMul Int (Seq α) where
--       smul := Sequ.zsmul

--     theorem zsmul_def {i : Int} {a : Seq α} : i • a = Sequ.zsmul i a := rfl

--     theorem neg_zsmul (i : Int) (a : Seq α) : -i • a = -(i • a) := by
--       funext n
--       exact Ring.neg_zsmul i (a n)

--     theorem zsmul_natCast_eq_nsmul (n : Nat) (a : Seq α) :
--       (n : Int) • a = n • a  := by
--         funext x
--         exact Ring.zsmul_natCast_eq_nsmul n (a x)

--     theorem intCast_ofNat (n : Nat) :
--       Int.cast (OfNat.ofNat (α := Int) n) = OfNat.ofNat (α := Seq α) n := by
--         funext x
--         exact Ring.intCast_ofNat n

--     theorem intCast_neg (i : Int) :
--       Int.cast (R := Seq α) (-i) = -Int.cast i := by
--         funext
--         exact Ring.intCast_neg i

--     instance : Ring (Seq α) where
--       neg_add_cancel := neg_add_cancel
--       sub_eq_add_neg := sub_eq_add_neg
--       neg_zsmul := neg_zsmul
--       zsmul_natCast_eq_nsmul := zsmul_natCast_eq_nsmul
--       intCast_ofNat := intCast_ofNat
--       intCast_neg := intCast_neg


--     -- CommSemiring

--     theorem mul_comm (a b : Seq α) : a * b = b * a := by
--       funext n
--       exact CommSemiring.mul_comm (a n) (b n)

--     instance : CommSemiring (Seq α) where
--       mul_comm := mul_comm


--     -- CommRing

--     instance : CommRing (Seq α) where

--   end Ring


--   section Field

--     variable {α : Type} [Seq_field_type α]

--     protected def div : Seq α → Seq α → Seq α :=
--       fun s1 s2 n => (s1 n) / (s2 n)

--     instance : Div (Seq α) where
--       div := Sequ.div

--     theorem div_def {a b : Seq α} : a / b = Sequ.div a b := rfl

--     protected def inv : Seq α → Seq α := fun s n => (s n)⁻¹

--     instance : Inv (Seq α) where
--       inv := Sequ.inv

--     theorem inv_def {a : Seq α} : a⁻¹ = Sequ.inv a := rfl

--     protected def zpow : Seq α → Int → Seq α :=
--       fun s i n => Field.zpow.hPow (s n) i

--     instance : HPow (Seq α) Int (Seq α) where
--       hPow := Sequ.zpow

--     theorem div_eq_mul_inv (a b : Seq α) : a / b = a * b⁻¹ := by
--       funext n
--       exact Field.div_eq_mul_inv _ _

--     theorem zero_ne_one : (0 : Seq α) ≠ 1 := by
--       intro seq
--       exact Field.zero_ne_one (funext_iff.mp seq 0)

--     theorem inv_zero : (0 : Seq α)⁻¹ = 0 := by
--       funext n; exact Field.inv_zero

--     theorem zpow_zero (a : Seq α) : a ^ (0 : Int) = 1 := by
--       funext n;exact Field.zpow_zero _

--     theorem zpow_succ (a : Seq α) (n : Nat) :
--       a ^ (n + 1 : Int) = a ^ (n : Int) * a := by
--         funext m;exact Field.zpow_succ _ _

--     theorem zpow_neg (a : Seq α) (n : Int) : a ^ (-n) = (a ^ n)⁻¹ := by
--       funext m;exact Field.zpow_neg _ _

--     -- instance : Field (Seq α) where
--     --   div_eq_mul_inv := div_eq_mul_inv
--     --   zero_ne_one := zero_ne_one
--     --   inv_zero := inv_zero
--     --   mul_inv_cancel := sorry
--     --   zpow_zero := zpow_zero
--     --   zpow_succ := zpow_succ
--     --   zpow_neg := zpow_neg

--   end Field


-- end Sequ


-- structure Cauchy (α : Type) [Seq_type α] where
--   s : Seq α
--   h : ∀ε : α, ε > (0 : α) →
--         ∃N : Nat, ∀(m n : Nat), (m ≥ N ∧ n ≥ N) →
--           abs (s m - s n) < ε


-- namespace Cauchy

--   section Group

--     variable {α : Type} [Seq_type α]

--     theorem ach {α : Type} [Seq_type α] (ε : α) (hε0 : 0 < ε) (hε : ¬(∃x : α, 0 < x ∧ x < ε)) :
--       (c : Cauchy α) → (∃(N : Nat) (a : α), ∀n : Nat, N ≤ n → c.s n = a) := by
--         simp at hε
--         replace hε := fun x p => Std.not_lt.mp (imp_not_comm.mp (hε x) p)
--         intro ⟨s, hc⟩; simp only
--         replace ⟨N, hc⟩ := hc ε hε0
--         exists N
--         exists s N
--         intro n hn
--         replace hc := hε (abs (s N - s n)) (hc N n ⟨IsPreorder.le_refl N, hn⟩)
--         replace hc :=  abs_zero_iff_zero.mp (Std.le_antisymm hc (abs_ge_zero (s N - s n)))
--         exact (AddCommGroup.sub_eq_zero_iff.mp hc).symm

--     protected def add: Cauchy α → Cauchy α → Cauchy α := by
--       intro ⟨s1, h1⟩ ⟨s2, h2⟩
--       let s3 := s1 + s2
--       apply Cauchy.mk
--       case s => exact s3
--       intro ε hep
--       cases em (∃ε2 : α, 0 < ε2 ∧ ε2 < ε) with
--       | inr hne =>
--         have hach := ach ε hep hne
--         let ⟨N1, ⟨v1, h1c⟩⟩ := hach ⟨s1, h1⟩
--         let ⟨N2, ⟨v2, h2c⟩⟩ := hach ⟨s2, h2⟩
--         simp only at h1c h2c
--         let (eq := hN) N := max N1 N2
--         exists N; intro m n hmn
--         have ⟨⟨hN1m, hN1n⟩, ⟨hN2m, hN2n⟩⟩ := ge_max_imp_ge_left_right hN hmn
--         simp only [s3, Sequ.add_def, Sequ.add]
--         rwa [
--           h1c m hN1m, h2c m hN2m, h1c n hN1n, h2c n hN2n,
--           AddCommGroup.sub_eq_zero_iff.mpr rfl,
--           abs_zero_iff_zero.mpr rfl
--         ]
--       | inl he =>
--         let ⟨ε1, hε1⟩ := he
--         let ⟨hε10, hε1ε⟩ := hε1
--         let ε2 := ε - ε1
--         have hε20 : 0 < ε2 := by
--           unfold ε2;
--           rw [← AddCommGroup.add_neg_cancel ε1];
--           repeat rw [AddCommGroup.sub_eq_add_neg]
--           apply (OrderedAdd.add_lt_left_iff (-ε1)).mp
--           exact hε1ε
--         replace ⟨N1, h1⟩ := h1 ε1 hε10
--         replace ⟨N2, h2⟩ := h2 ε2 hε20
--         let (eq := hNeq) N := max N1 N2
--         exists N
--         intro m n hmn
--         have ⟨hN1,hN2⟩ := ge_max_imp_ge_left_right hNeq hmn
--         replace h1 := h1 m n hN1
--         replace h2 := h2 m n hN2
--         unfold s3
--         rw [Sequ.add_def]
--         simp only [Sequ.add]
--         rw [sum_sub_sum_eq_dif_add_dif]
--         have ε12 : ε = ε1 + ε2 := by
--           unfold ε2
--           rw [
--             AddCommGroup.sub_eq_add_neg, AddCommMonoid.add_comm,
--             AddCommMonoid.add_assoc,AddCommGroup.neg_add_cancel
--           ]
--           exact (AddCommMonoid.add_zero ε).symm
--         rw [ε12]
--         exact Std.lt_of_le_of_lt abs_sum_le_sum_abs (OrderedAdd.add_lt_add h1 h2)

--     instance : Add (Cauchy α) where
--       add := Cauchy.add

--     theorem add_def {a b : Cauchy α} : a + b = Cauchy.add a b := rfl

--     protected def zero : Cauchy α := by
--       apply Cauchy.mk 0
--       intro ε hε;exists 0;intros;rw [Sequ.zero_def];unfold Sequ.zero;
--       simp [AddCommGroup.sub_zero, abs_zero_iff_zero.mpr, hε]

--     instance : Zero (Cauchy α) where
--       zero := Cauchy.zero

--     theorem zero_def : (0 : Cauchy α) = @Cauchy.zero α _ := rfl

--     theorem add_zero (a : Cauchy α) : a + 0 = a := by
--       rw [add_def]
--       unfold Cauchy.add
--       repeat split
--       case h_1 eq0 =>
--         cases eq0
--         simp only [AddCommMonoid.add_zero]

--     theorem add_comm (a b : Cauchy α) : a + b = b + a := by
--       repeat rw [add_def]
--       unfold Cauchy.add
--       repeat split
--       case h_1 eqb =>
--         cases eqb
--         simp only [AddCommMonoid.add_comm]

--     theorem add_assoc (a b c : Cauchy α) : (a + b) + c = a + (b + c) := by
--       repeat rw [add_def]
--       unfold Cauchy.add
--       repeat split
--       simp [AddCommMonoid.add_assoc]

--     protected def neg: Cauchy α → Cauchy α := by
--       intro ⟨s, h⟩
--       apply Cauchy.mk (-s)
--       rw [Sequ.neg_def]
--       unfold Sequ.neg
--       simp (singlePass := true) only [← abs_neg_eq_abs]
--       simp only [AddCommGroup.sub_eq_add_neg, AddCommGroup.neg_add, AddCommGroup.neg_neg]
--       simp only [← AddCommGroup.sub_eq_add_neg]
--       exact h

--     instance : Neg (Cauchy α) where
--       neg := Cauchy.neg

--     theorem neg_def {a : Cauchy α} : -a = Cauchy.neg a := rfl

--     instance : AddCommMonoid (Cauchy α) where
--       add_zero := add_zero
--       add_comm := add_comm
--       add_assoc := add_assoc

--     protected def sub : Cauchy α → Cauchy α → Cauchy α :=
--       fun a => (fun b => Cauchy.add a (Cauchy.neg b))

--     instance : Sub (Cauchy α) where
--       sub := Cauchy.sub

--     theorem sub_def (a b : Cauchy α) : a - b = Cauchy.sub a b := rfl

--     theorem neg_add_cancel (a : Cauchy α) : -a + a = 0 := by
--       rw [add_def, neg_def, zero_def]
--       unfold Cauchy.add Cauchy.neg Cauchy.zero
--       repeat split
--       case h_1 heq =>
--       cases heq
--       simp only [AddCommGroup.neg_add_cancel]

--     theorem sub_eq_add_neg (a b : Cauchy α) : a - b = a + -b := by
--       rw [add_def, sub_def, neg_def]
--       unfold Cauchy.sub Cauchy.neg Cauchy.add
--       repeat split
--       simp only []

--     instance : AddCommGroup (Cauchy α) where
--       neg_add_cancel := neg_add_cancel
--       sub_eq_add_neg := sub_eq_add_neg

--   end Group


--   section Ring

--     -- require field

--     variable {α : Type} [Seq_field_type α]


--     -- Semiring

--     -- protected def mul : Cauchy α → Cauchy α → Cauchy α := by
--     --   intro ⟨s1, h1⟩ ⟨s2, h2⟩
--     --   apply Cauchy.mk (s1 * s2)
--     --   intro ε hε0
--     --   have (eq := hεh) εh := ε / 2
--     --   have h2εh : ε = εh + εh := by
--     --     rw [hεh, Field.div_eq_mul_inv, ← Semiring.right_distrib, ← Semiring.mul_two, Semiring.mul_assoc, Field.mul_inv_cancel, Semiring.mul_one]
--     --   have ⟨N1', hN1'⟩ := h1 1 OrderedRing.zero_lt_one
--     --   have ⟨N2', hN2'⟩ := h2 1 OrderedRing.zero_lt_one
--     --   have (eq := deq) d := abs (s1 N1') + abs (s2 N2') + 1
--     --   have hd0 : 0 < d := by
--     --     rw [deq, ← AddCommMonoid.add_zero (0 : α),
--     --     ← AddCommMonoid.add_zero (0 + 0 : α)]
--     --     exact OrderedAdd.add_le_lt_add
--     --       (OrderedAdd.add_le_add (abs.abs_ge_zero _) (abs.abs_ge_zero _))
--     --       OrderedRing.zero_lt_one
--     --   have hdinv0 := Field.IsOrdered.inv_pos_iff.mpr hd0
--     --   let (eq := ε'eq) ε' := ε * d⁻¹
--     --   have hε'0 : 0 < ε' := OrderedRing.mul_pos hε0 hdinv0
--     --   replace ⟨N1, h1⟩ := h1 ε' hε'0
--     --   replace ⟨N2, h2⟩ := h2 ε' hε'0
--     --   let (eq := defN) N := max N1 N2
--     --   exists N
--     --   intro m n hmn
--     --   have ⟨hm, hn⟩ := hmn
--     --   rw [Sequ.mul_def]
--     --   unfold Sequ.mul
--     --   rw [
--     --     -- ← AddCommMonoid.add_zero (s1 m * s2 m),
--     --     ← AddCommGroup.sub_add_cancel (a := s1 m * s2 m) (b := s1 m * s2 n),
--     --     ← AddCommGroup.add_diff_eq_add_sub,
--     --   ]
--     --   refine abs.abs_sum_le_sum_abs
--     --   -- have hms : abs (s1 m * s2 m - s1 m * s2 n) < εh := sorry
--     --   -- have hsn : abs (s1 m * s2 n - s1 n * s2 n) < εh := sorry


--   end Ring

--   section Field
--     -- Worse and Worse
--   end Field
-- end Cauchy


-- def Converge.converge {α : Type} [Seq_type α] (s : Seq α) (l : α) : Prop :=
--   ∀ε : α, ε > 0 →
--     ∃N : Nat, ∀n : Nat, N ≤ n →
--       abs (s n - l) < ε

-- structure Converge (α : Type) [Seq_type α] where
--   s : Seq α
--   l : α
--   h : Converge.converge s l

-- namespace Converge

--   section Group

--     variable {α : Type} [Seq_type α]

--     theorem ach {α : Type} [Seq_type α] (ε : α) (hε0 : 0 < ε) (hε : ¬(∃x : α, 0 < x ∧ x < ε)) :
--       (c : Converge α) → (∃(N : Nat), ∀n : Nat, N ≤ n → c.s n = c.l) := by
--         simp at hε
--         intro ⟨s, l, hc⟩; simp only
--         replace ⟨N, hc⟩ := hc ε hε0
--         replace hε := fun x p => Std.not_lt.mp (imp_not_comm.mp (hε x) p)
--         exists N
--         intro n hn
--         exact AddCommGroup.sub_eq_zero_iff.mp (
--           abs_zero_iff_zero.mp (
--             Std.le_antisymm
--               (hε (abs (s n - l)) (hc n hn))
--               (abs_ge_zero (s n - l))
--           )
--         )


--     protected def add : Converge α → Converge α → Converge α := by
--         intro ⟨s1, l1, h1⟩ ⟨s2, l2, h2⟩
--         apply Converge.mk (s1+s2) (l1+l2)
--         intro ε hε0
--         simp only [Sequ.add_def];unfold Sequ.add
--         simp only [sum_sub_sum_eq_dif_add_dif]
--         by_cases h : ∃ε1 : α, 0 < ε1 ∧ ε1 < ε
--         case pos =>
--           let ⟨ε1, ⟨hε10, hε1ε⟩⟩ := h
--           let (eq := hε12) ε2 := ε - ε1
--           have hε20 : 0 < ε2 := OrderedAdd.sub_pos_iff.mpr hε1ε
--           let ⟨N1, h1⟩ := h1 ε1 hε10
--           let ⟨N2, h2⟩ := h2 ε2 hε20
--           let (eq := hMax) N := max N1 N2
--           exists N;intro n hn
--           simp only [AddCommGroup.sub_eq_iff.mp hε12.symm]
--           replace h1 := h1 n (Std.le_trans Std.left_le_max hn)
--           replace h2 := h2 n (Std.le_trans Std.right_le_max hn)
--           rw (occs := .pos [2]) [AddCommMonoid.add_comm]
--           apply (Std.lt_of_le_of_lt abs.abs_sum_le_sum_abs)
--           exact OrderedAdd.add_lt_add h1 h2
--         case neg =>
--           have hach := ach ε hε0 h
--           replace ⟨N1, h1⟩ := hach ⟨s1, l1, h1⟩
--           replace ⟨N2, h2⟩ := hach ⟨s2, l2, h2⟩
--           simp only at h1 h2
--           let (eq := hMax) N := max N1 N2
--           exists N; intro n hn
--           replace h1 := h1 n (Std.le_trans Std.left_le_max hn)
--           replace h2 := h2 n (Std.le_trans Std.right_le_max hn)
--           simp only [h1, h2, AddCommGroup.sub_eq_zero_iff.mpr,
--             AddCommMonoid.add_zero, abs_zero_iff_zero.mpr, hε0]

--     instance : Add (Converge α) where
--       add := Converge.add

--     theorem add_def {a b : Converge α} : a + b = Converge.add a b := rfl

--     protected def zero : Converge α := by
--       apply Converge.mk 0 0
--       intro ε hε;exists 0;intros;rw [Sequ.zero_def];unfold Sequ.zero;
--       simp [AddCommGroup.sub_zero, abs_zero_iff_zero.mpr, hε]

--     instance : Zero (Converge α) where
--       zero := Converge.zero

--     theorem zero_def : (0 : Converge α) = @Converge.zero α _ := rfl

--     theorem add_zero (a : Converge α) : a + 0 = a := by
--       rw [add_def]
--       unfold Converge.add
--       repeat split
--       case h_1 eq0 =>
--         cases eq0
--         simp only [AddCommMonoid.add_zero]

--     theorem add_assoc (a b c : Converge α) : (a + b) + c = a + (b + c) := by
--       repeat rw [add_def]
--       unfold Converge.add
--       repeat split
--       simp [AddCommMonoid.add_assoc]

--     protected def neg : Converge α → Converge α := by
--       intro ⟨s, l, h⟩
--       apply Converge.mk (-s) (-l)
--       rw [Sequ.neg_def]
--       unfold Sequ.neg
--       intro ε hε0
--       let ⟨N, h⟩ := h ε hε0
--       exists N
--       intro n hn
--       simp only [AddCommGroup.sub_eq_add_neg, ←AddCommGroup.neg_add, abs.abs_neg_eq_abs]
--       rw [← AddCommGroup.sub_eq_add_neg]
--       exact h n hn

--     instance : Neg (Converge α) where
--       neg := Converge.neg

--     theorem neg_def {a : Converge α} : -a = Converge.neg a := rfl

--     theorem add_comm (a b : Converge α) : a + b = b + a := by
--       repeat rw [add_def]
--       unfold Converge.add
--       repeat split
--       case h_1 eqb =>
--         cases eqb
--         simp only [AddCommMonoid.add_comm]

--     instance : AddCommMonoid (Converge α) where
--       add_zero := add_zero
--       add_comm := add_comm
--       add_assoc := add_assoc

--     protected def sub : Converge α → Converge α → Converge α :=
--       fun c1 c2 => Converge.add c1 (Converge.neg c2)

--     instance : Sub (Converge α) where
--       sub := Converge.sub

--     theorem sub_def (a b : Converge α) : a - b = Converge.sub a b := rfl

--     theorem neg_add_cancel (a : Converge α) : -a + a = 0 := by
--       rw [add_def, neg_def, zero_def]
--       unfold Converge.add Converge.neg Converge.zero
--       repeat split
--       case h_1 heq =>
--       cases heq
--       simp only [AddCommGroup.neg_add_cancel]

--     theorem sub_eq_add_neg (a b : Converge α) : a - b = a + -b := by
--       rw [add_def, sub_def, neg_def]
--       unfold Converge.sub Converge.neg Converge.add
--       repeat split
--       simp only []

--     instance : AddCommGroup (Converge α) where
--       neg_add_cancel := neg_add_cancel
--       sub_eq_add_neg := sub_eq_add_neg

--   end Group
-- end Converge

-- structure ℤ_pair where
--   fst : ℤ
--   snd : ℤ

-- structure ℚ_con where
--   fst : ℤ
--   snd : ℤ
--   h : snd > zero


-- def ℚ.eqv : ℚ_con → ℚ_con → Prop :=
--   fun a b => a.fst * b.snd = a.snd * b.fst

-- namespace ℚ.eqv

--   theorem refl : ∀ (a : ℚ_con), ℚ.eqv a a :=
--     fun ⟨a1, a2, _⟩ => mul_comm a1 a2

--   theorem symm : ∀ {a b : ℚ_con}, ℚ.eqv a b → ℚ.eqv b a := by
--     unfold eqv
--     intro ⟨a1, a2, _⟩ ⟨b1, b2, _⟩ h
--     simp only [mul_comm a1, mul_comm a2] at *
--     exact h.symm

--   theorem trans : ∀ {a b c : ℚ_con}, ℚ.eqv a b → ℚ.eqv b c → ℚ.eqv a c := by
--     unfold eqv
--     intro ⟨a1, a2, _⟩ ⟨b1, b2, hb⟩ ⟨c1, c2, hc⟩ h1 h2
--     simp only [] at *
--     by_cases hb0 : b1 = zero
--     case pos =>
--       simp only [hb0, mul_zero, zero_mul] at h1 h2
--       have ha0 : a1 = zero := (mul_eq_zero h1).resolve_right (ne_of_lt hb).symm
--       have hc0 : c1 = zero := (mul_eq_zero h2.symm).resolve_left (ne_of_lt hb).symm
--       rw [ha0, hc0, mul_zero, zero_mul]
--     case neg =>
--       replace h1 := congrArg (· * c1) h1--(ℤ.mul_left_inj (b2.mul c1)).mpr h1
--       simp only [mul_assoc, ←h2] at h1
--       replace h1 := congrArg (· * c2) h1--(ℤ.mul_left_inj (b2.mul c1)).mpr h1
--       simp only [ℤ.mul_left_inj (ne_of_lt hc).symm] at h1
--       simp only [mul_left_comm _ b1, ℤ.mul_right_inj hb0] at h1
--       exact h1

--   def eqv : Equivalence ℚ.eqv where
--     refl := refl
--     symm := symm
--     trans := trans

-- end ℚ.eqv

-- def ℚ := EquivalentClass ℚ.eqv

-- namespace ℚ

--   abbrev mk' (a : ℚ_con) := EquivalentClass.from_elm eqv.eqv a

--   section nums

--     def zero_repr : ℚ_con := ⟨zero, one, zero_lt_one⟩
--     def _zero : ℚ := mk' zero_repr
--     @[default_instance] instance : Zero ℚ := ⟨_zero⟩
--     theorem zero_is_member_zero : zero.is_member zero_repr := EC.is_member_of_from_elm _ eqv.eqv


--     def one_repr : ℚ_con := ⟨one, one, zero_lt_one⟩
--     def _one : ℚ := mk' one_repr
--     @[default_instance] instance : One ℚ := ⟨_one⟩
--     theorem one_is_member_one : one.is_member one_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def two_repr : ℚ_con := ⟨ℤ.two, one, zero_lt_one⟩
--     def two : ℚ := mk' two_repr
--     theorem two_is_member_two : two.is_member two_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def three_repr : ℚ_con := ⟨ℤ.three, one, zero_lt_one⟩
--     def three : ℚ := mk' three_repr
--     theorem three_is_member_three : three.is_member three_repr := EC.is_member_of_from_elm _ eqv.eqv

--     def neg_one_repr : ℚ_con := ⟨ℤ.neg_one, one, zero_lt_one⟩
--     def neg_one : ℚ := mk' neg_one_repr
--     theorem neg_one_is_member_neg_one : neg_one.is_member neg_one_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def neg_two_repr : ℚ_con := ⟨ℤ.neg_two, one, zero_lt_one⟩
--     def neg_two : ℚ := mk' neg_two_repr
--     theorem neg_two_is_member_neg_two : neg_two.is_member neg_two_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def neg_three_repr : ℚ_con := ⟨ℤ.neg_three, one, zero_lt_one⟩
--     def neg_three : ℚ := mk' neg_three_repr
--     theorem neg_three_is_member_neg_three : neg_three.is_member neg_three_repr := EC.is_member_of_from_elm _ eqv.eqv

--   end nums

--   section basic

--     theorem num_eq_zero {a : ℤ} {h : zero < a} : EC.from_elm eqv.eqv ⟨zero, a, h⟩ = (zero : ℚ) := by
--       apply EC.sound eqv.eqv _
--       unfold eqv zero_repr
--       simp only [zero_mul, mul_zero]

--     theorem num_eq_zero' {a : ℚ_con} {S : ℚ} (h : S.is_member a) : a.fst = zero → S = zero := by
--       intro h'
--       apply EC.sound' eqv.eqv h zero_is_member_zero _
--       unfold eqv zero_repr
--       simp only [h', zero_mul, mul_zero]

--     theorem num_eq_zero_of_eq_zero {a b : ℤ} {h : zero < b} : EC.from_elm eqv.eqv ⟨a, b, h⟩ = (zero : ℚ) → a = zero := by
--       intro h'
--       replace h' := EC.sound_inv eqv.eqv h'
--       simp only [eqv, zero_repr, mul_one, mul_zero] at h'
--       exact h'

--     theorem num_eq_zero_of_eq_zero' {a : ℚ_con} {S : ℚ} (h : S.is_member a) : S = zero → a.fst = zero := by
--       intro h'
--       replace h' := EC.sound_inv' h zero_is_member_zero h'
--       simp only [eqv, zero_repr, mul_one, mul_zero] at h'
--       exact h'

--   end basic

--   section add

--     def add_fn_fn_fn : ℚ_con → ℚ_con → ℚ_con :=
--       fun a b => ⟨(a.fst * b.snd) + (a.snd * b.fst), a.snd * b.snd, mul_pos a.h b.h⟩

--     def add_fn_fn : ℚ_con → ℚ_con → ℚ :=
--       fun a b => ℚ.mk' (add_fn_fn_fn a b)

--     private theorem add_fn_respect (a : ℚ_con) : ∀ (b c : ℚ_con), eqv b c → add_fn_fn a b = add_fn_fn a c := by
--       intro ⟨b1, b2, h⟩ ⟨b1', b2', h'⟩ h''
--       apply EquivalentClass.sound
--       unfold eqv add_fn_fn_fn at *
--       simp only [mul_add,add_mul]
--       ac_nf
--       simp [←mul_assoc]
--       congr 3

--     def add_fn : ℚ_con → ℚ → ℚ :=
--       fun a => EquivalentClass.lift (β := ℚ) eqv.eqv (add_fn_fn a) (add_fn_respect a)

--     private theorem add_respect : ∀ (a b : ℚ_con), eqv a b → add_fn a = add_fn b := by
--       intro ⟨a1, a2, ha⟩ ⟨b1, b2, hb⟩ h
--       funext Sc
--       let c := Sc.sys_of_repr
--       apply EquivalentClass.sound
--       unfold eqv add_fn_fn_fn at *
--       simp only [mul_add,add_mul]
--       ac_nf
--       simp only [←mul_assoc]
--       congr

--     def add : ℚ → ℚ → ℚ :=
--       EquivalentClass.lift (β := ℚ → ℚ) eqv.eqv add_fn add_respect

--     @[default_instance] instance : Add ℚ := ⟨add⟩

--     theorem add_def {a b : ℚ} : a + b = a.add b := rfl

--     private theorem _add_zero : ∀(n : ℚ), n + zero = n := by
--       intro n
--       let np := n.sys_of_repr
--       repeat rw [add_def]
--       unfold add add_fn
--       rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
--       rw [EquivalentClass.lift_spec _ zero_repr zero_is_member_zero]
--       unfold add_fn_fn add_fn_fn_fn zero_repr
--       simp only [mul_zero, mul_one, add_zero]
--       exact (EquivalentClass.from_sys_of_repr _).symm

--     private theorem _add_comm : ∀(n m : ℚ), n + m = m + n := by
--       intro n m
--       let np := n.sys_of_repr
--       let mp := m.sys_of_repr
--       repeat rw [add_def]
--       unfold add add_fn
--       simp only [
--         EC.lift_spec n np n.sys_of_repr_spec,
--         EC.lift_spec m mp m.sys_of_repr_spec]
--       unfold add_fn_fn add_fn_fn_fn
--       ac_nf


--     private theorem _add_assoc : ∀ (a b c : ℚ), (a + b) + c = a + (b + c) := by
--       intro a b c
--       repeat rw [add_def]
--       unfold add add_fn add_fn_fn
--       let ap := a.sys_of_repr
--       let bp := b.sys_of_repr
--       let cp := c.sys_of_repr
--       let abp := (add_fn_fn_fn ap bp)
--       let bcp := (add_fn_fn_fn bp cp)
--       let ab := mk' abp
--       let bc := mk' bcp
--       repeat first
--       | rw [EC.lift_spec _ ap a.sys_of_repr_spec]
--       | rw [EC.lift_spec _ bp b.sys_of_repr_spec]
--       | rw [EC.lift_spec _ cp c.sys_of_repr_spec]
--       | rw [EC.lift_spec _ abp (EquivalentClass.is_member_of_from_elm abp _)]
--       | rw [EC.lift_spec _ bcp (EquivalentClass.is_member_of_from_elm bcp _)]
--       unfold abp bcp add_fn_fn_fn
--       simp [add_mul, mul_add]
--       ac_nf

--     @[default_instance] instance : CommMonoid ℚ where
--       _add_zero := _add_zero
--       _add_assoc := _add_assoc
--       add_comm := _add_comm

--   end add

--   section neg

--     def neg_fn_fn : ℚ_con → ℚ_con :=
--       fun a => ⟨-a.fst, a.snd, a.h⟩

--     def neg_fn : ℚ_con → ℚ :=
--       fun a => ℚ.mk' (neg_fn_fn a)

--     private theorem neg_respect : ∀(a b : ℚ_con), eqv a b → neg_fn a = neg_fn b := by
--       intro ⟨b1, b2, h⟩ ⟨b1', b2', h'⟩ h''
--       apply EC.sound
--       unfold eqv neg_fn_fn at *
--       simp only [mul_neg_left, mul_neg_right] at *
--       congr

--     def neg : ℚ → ℚ :=
--       EC.lift eqv.eqv neg_fn neg_respect

--     @[default_instance] instance : Neg ℚ where
--       neg := neg

--     theorem neg_def {a : ℚ} : -a = a.neg := rfl

--     private theorem _add_neg : ∀(a : ℚ), a + -a = zero := by
--       intro a
--       repeat first | rw [add_def] | rw [neg_def]
--       unfold add add_fn add_fn_fn neg neg_fn
--       repeat first
--       | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
--       | rw [EC.lift_spec _ _ (EC.is_member_of_from_elm _ eqv.eqv)]
--       apply EC.sound
--       unfold add_fn_fn_fn neg_fn_fn zero_repr eqv
--       simp only [mul_zero, mul_one, mul_comm _ (-_ : ℤ), mul_neg_left, add_neg]


--     @[default_instance] instance : CommGroup ℚ where
--       add_neg := _add_neg

--   end neg

--   section mul

--     def mul_fn_fn_fn : ℚ_con → ℚ_con → ℚ_con :=
--       fun a b => ⟨a.fst * b.fst, a.snd * b.snd, mul_pos a.h b.h⟩

--     def mul_fn_fn : ℚ_con → ℚ_con → ℚ :=
--       fun a b => ℚ.mk' (mul_fn_fn_fn a b)

--     private theorem mul_fn_respect (a : ℚ_con) : ∀ (b c : ℚ_con), eqv b c → mul_fn_fn a b = mul_fn_fn a c := by
--       intro a b h''
--       apply EC.sound
--       unfold eqv mul_fn_fn_fn at *
--       simp only [mul_assoc] at *
--       rw [mul_left_comm a.fst, h'']
--       ac_nf at *

--     def mul_fn : ℚ_con → ℚ → ℚ :=
--       fun a => EquivalentClass.lift (β := ℚ) eqv.eqv (mul_fn_fn a) (mul_fn_respect a)

--     private theorem mul_respect : ∀ (a b : ℚ_con), eqv a b → mul_fn a = mul_fn b := by
--       intro ⟨a1, a2, ha⟩ ⟨b1, b2, hb⟩ h
--       funext Sc
--       let c := Sc.sys_of_repr
--       apply EC.sound
--       unfold eqv mul_fn_fn_fn at *
--       simp only [] at *
--       rw [mul_right_comm, ←mul_assoc, h]
--       ac_nf

--     def mul : ℚ → ℚ → ℚ :=
--       EquivalentClass.lift (β := ℚ → ℚ) eqv.eqv mul_fn mul_respect


--     @[default_instance] instance : Mul ℚ where
--       mul := mul

--     theorem mul_def {a b : ℚ} : a * b = a.mul b := rfl

--     private theorem _mul_one : ∀ (a : ℚ), a * one = a := by
--       intro a
--       repeat first | rw [mul_def]
--       unfold mul mul_fn mul_fn_fn
--       repeat first
--       | rw [EC.lift_spec (one : ℚ) _ (EC.is_member_of_from_elm _ eqv.eqv)]
--       | rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)]
--       apply EC.sound' eqv.eqv (EC.is_member_of_from_elm _ eqv.eqv) a.sys_of_repr_spec _
--       unfold mul_fn_fn_fn one_repr eqv
--       simp only
--       ac_nf

--     private theorem _mul_assoc : ∀ (a b c : ℚ), a * b * c = a * (b * c) := by
--       intro a b c
--       repeat first | rw [mul_def]
--       unfold mul mul_fn mul_fn_fn
--       let ap := a.sys_of_repr
--       let bp := b.sys_of_repr
--       let cp := c.sys_of_repr
--       repeat first
--       | rw [EC.lift_spec a _ (EC.sys_of_repr_spec _)]
--       | rw [EC.lift_spec b _ (EC.sys_of_repr_spec _)]
--       | rw [EC.lift_spec c _ (EC.sys_of_repr_spec _)]
--       | rw [EC.lift_spec _ (mul_fn_fn_fn ap bp) (EC.is_member_of_from_elm _ eqv.eqv)]
--       | rw [EC.lift_spec _ (mul_fn_fn_fn bp cp)  (EC.is_member_of_from_elm _ eqv.eqv)]
--       apply EC.sound
--       unfold ap bp cp mul_fn_fn_fn eqv
--       simp only
--       ac_nf

--     private theorem _add_mul : ∀ (a b c : ℚ), (a + b) * c = a * c + b * c := by
--       intro a b c
--       repeat first | rw [mul_def] | rw [add_def]
--       unfold mul mul_fn mul_fn_fn add add_fn add_fn_fn
--       let ap := a.sys_of_repr
--       let bp := b.sys_of_repr
--       let cp := c.sys_of_repr
--       repeat first
--       | rw [EC.lift_spec a _ (EC.sys_of_repr_spec _)]
--       | rw [EC.lift_spec b _ (EC.sys_of_repr_spec _)]
--       | rw [EC.lift_spec c _ (EC.sys_of_repr_spec _)]
--       | rw [EC.lift_spec _ (add_fn_fn_fn ap bp) (EC.is_member_of_from_elm _ eqv.eqv)]
--       | rw [EC.lift_spec _ (mul_fn_fn_fn ap cp) (EC.is_member_of_from_elm _ eqv.eqv)]
--       | rw [EC.lift_spec _ (mul_fn_fn_fn bp cp)  (EC.is_member_of_from_elm _ eqv.eqv)]
--       apply EC.sound
--       unfold ap bp cp mul_fn_fn_fn add_fn_fn_fn eqv
--       simp only [add_mul, mul_add]
--       ac_nf

--     private theorem _zero_ne_one : zero ≠ one := by
--       intro h
--       replace h := EC.sound_inv' zero_is_member_zero one_is_member_one h
--       unfold eqv zero_repr one_repr at h
--       simp [mul_one] at h
--       exact zero_ne_one h

--     private theorem _mul_comm : ∀ (a b : ℚ), a * b = b * a := by
--       intro a b
--       apply EC.sound
--       unfold eqv mul_fn_fn_fn
--       ac_nf

--     @[default_instance] instance : CommRing ℚ where
--       _mul_one := _mul_one
--       _mul_assoc := _mul_assoc
--       _add_mul := _add_mul
--       _zero_ne_one := _zero_ne_one
--       _mul_comm := _mul_comm


--   end mul

--   section inv

--     -- def inv_fn_fn : (Σ'(a : ℚ_con), a.fst ≠ zero) → ℚ_con :=
--     --   fun ah => ((eq_or_lt_or_gt ah.fst.fst zero).resolve_left ah.snd).elim'
--     --     (⟨ah.fst.snd, -ah.fst.fst, neg_neg_is_pos ·⟩)
--     --     (⟨ah.fst.snd, ah.fst.fst, ·⟩)
--     --   --⟨-a.fst, a.snd, a.h⟩

--     -- def inv_fn : (Σ'(a : ℚ_con), a.fst ≠ zero) → ℚ :=
--     --   fun a => ℚ.mk' (inv_fn_fn a)


--     -- def inv_fn_fn : (a : ℚ_con) → a.fst ≠ zero → ℚ_con :=
--     --   fun a h => ((eq_or_lt_or_gt a.fst zero).resolve_left h).elim'
--     --     (⟨a.snd, -a.fst, neg_neg_is_pos ·⟩) (⟨a.snd, a.fst, ·⟩)

--     -- def inv_fn : (a : ℚ_con) → a.fst ≠ zero → ℚ :=
--     --   fun a h => ℚ.mk' (inv_fn_fn a h)

--     -- private theorem inv_respect : ∀(a b : ℚ_con), eqv a b → inv_fn a ≍ inv_fn b := by
--     --   -- intro ⟨b1, b2, h⟩ ⟨b1', b2', h'⟩ h''
--     --   -- apply EC.sound
--     --   -- unfold eqv inv_fn_fn at *
--     --   -- simp only [mul_inv_left, mul_inv_right] at *
--     --   -- congr
--     --   sorry

--     -- -- def inv : ℚ → ℚ :=
--     -- def inv :=
--     --   EC.hlift (f := inv_fn) eqv.eqv inv_fn inv_respect

--     def inv_fn_fn : (a : ℚ_con) → a.fst ≠ zero → ℚ_con :=
--       fun a h => ((eq_or_lt_or_gt a.fst zero).resolve_left h).elim'
--         (⟨-a.snd, -a.fst, neg_neg_is_pos ·⟩)
--         (⟨a.snd, a.fst, ·⟩)
--       --⟨-a.fst, a.snd, a.h⟩

--     def inv_fn : (a : ℚ_con) → a.fst ≠ zero → ℚ :=
--       fun a h => ℚ.mk' (inv_fn_fn a h)

--     -- def inv : (Σ'(a : ℚ), a ≠ zero) → ℚ :=
--     --   fun ah => inv_fn ⟨ah.fst.sys_of_repr, (fun h => ah.snd (num_eq_zero' ah.fst.sys_of_repr_spec h))⟩
--     def inv' : (a : ℚ) → a ≠ zero → ℚ :=
--       fun a h => inv_fn a.sys_of_repr (fun h' => h (num_eq_zero' a.sys_of_repr_spec h'))

--     theorem inv_spec_eqv {S : ℚ} (a : ℚ_con) (h : S.is_member a) : (S ≠ zero) = (a.fst ≠ zero) :=
--       congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h, num_eq_zero' h⟩)

--     theorem inv_spec {S : ℚ} {h : S ≠ zero} {a : ℚ_con} (hm : S.is_member a) : inv' S h = inv_fn a ((inv_spec_eqv a hm).mp h) := by
--       apply EC.sound
--       unfold eqv inv_fn_fn
--       let s := S.sys_of_repr
--       have hs := fun h0 => h (num_eq_zero' S.sys_of_repr_spec h0)
--       have ha := (inv_spec_eqv a hm).mp h
--       have hos := (eq_or_lt_or_gt s.fst zero).resolve_left hs
--       have hoa := (eq_or_lt_or_gt a.fst zero).resolve_left ha
--       let elm1 := (hos.elim' (c := ℚ_con)
--         (fun x => ⟨ -s.snd, -s.fst, neg_neg_is_pos x ⟩)
--         (fun x => ⟨ s.snd, s.fst, x ⟩))
--       let elm2 := (hoa.elim' (c := ℚ_con)
--           (fun x => ⟨ -a.snd, -a.fst, neg_neg_is_pos x ⟩)
--           (fun x => ⟨ a.snd, a.fst, x ⟩))
--       have heqv := S.member_related a s ⟨hm, S.sys_of_repr_spec⟩
--       unfold eqv at heqv; ac_nf at heqv
--       show elm1.fst * elm2.snd = elm1.snd * elm2.fst
--       apply Or.elim'_spec (c := ℚ_con) (p := (fun m => m.fst * elm2.snd = m.snd * elm2.fst))
--       <;>intro cs<;>simp only
--       <;>apply Or.elim'_spec (c := ℚ_con) (p := (fun m => _ * m.snd = _ * m.fst))
--       <;>intro ca<;>simp only [mul_neg_left, mul_neg_right]
--       <;>ac_nf<;>rw[heqv]

--     theorem inv_spec2 {S : ℚ} {a : ℚ_con} {h : a.fst ≠ zero} (hm : S.is_member a) : inv' S ((inv_spec_eqv a hm).mpr h) = inv_fn a h := inv_spec hm

--       -- show (hos.elim' (c := ℚ_con)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩) ).fst *
--       --   (hoa.elim' (c := ℚ_con)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).snd =
--       --   (hos.elim' (c := ℚ_con)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩)).snd *
--       --   (hoa.elim' (c := ℚ_con)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).fst
--       -- #check Or.elim'_spec


--       -- show (hos.elim' (c := ℚ_con)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩) ).fst *
--       --   (hoa.elim' (c := ℚ_con)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).snd =
--       --   (hos.elim' (c := ℚ_con)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩)).snd *
--       --   (hoa.elim' (c := ℚ_con)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).fst


--     -- theorem inv_spec' (S : ℚ) {h : S ≠ zero} : ∀(a : ℚ_con), S.is_member a → inv' S ≍ inv_fn a := sorry

--       -- -- theorem inv_spec' {h : ∀ (a b : α), R a b → f a = f b} (S : EquivalentClass R) : ∀(a : α), is_member a S → inv' S = f a :=
--       -- set_option pp.proofs true in
--       -- theorem inv_spec' (S : ℚ) {h : S ≠ zero} : ∀(a : ℚ_con), S.is_member a → inv' S ≍ inv_fn a := by
--       --   intro a h'
--       --   have feq : (S ≠ zero) = (a.fst ≠ zero) := congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
--       --   -- have feq (S : ℚ) (a : ℚ_con) (h' : S.is_member a) : (S ≠ zero) = (a.fst ≠ zero) := congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
--       --   apply heq_of_eqRec_eq
--       --   case h₁ =>
--       --     -- congr 1
--       --     refine' implies_congr feq rfl
--       --     -- refine' implies_congr (feq S a h') rfl
--       --   case h₂ =>
--       --     funext h''
--       --     apply EC.sound' eqv.eqv _ (EC.is_member_of_from_elm _ eqv.eqv) _
--       --     -- unfold inv_fn
--       --     exact inv_fn_fn S.sys_of_repr (fun h0 => h (num_eq_zero' S.sys_of_repr_spec h0))
--       --     -- apply EC.is_member_of_from_elm
--       --     -- guard_expr (implies_congr feq rfl ▸ S.inv') =~ S.inv'
--       --     -- guard_expr ((implies_congr feq rfl) ▸ S.inv') =~ rfl ▸ (fun x => S.inv' (feq ▸ x))
--       --     -- simp?
--       --     unfold implies_congr rfl
--       --     guard_target =~ EquivalentClass.is_member (inv_fn_fn (EquivalentClass.sys_of_repr S) fun h0 => h (num_eq_zero' (EquivalentClass.sys_of_repr_spec S) h0))
--       --       -- ((fun he => S.inv' (feq.mpr he)) h'')
--       --       ((((sorry):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')

--       --     have h4 : (((feq ▸ Eq.refl (S ≠ zero → ℚ)) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') = S.inv' := by
--       --       -- simp only []
--       --       unfold Eq.symm
--       --       generalize ((((feq ▸ Eq.refl (S ≠ zero → ℚ)): (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ rfl) : (a.fst ≠ zero → ℚ) = (S ≠ zero → ℚ)) = x
--       --       generalize ((x ▸ rfl) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) = y
--       --       have h1 : y ▸ S.inv' ≍ S.inv' := cast_heq _ _
--       --       have h2 : x ▸ y ▸ S.inv' ≍ y ▸ S.inv' := cast_heq _ _
--       --       have h3 : x ▸ y ▸ S.inv' ≍ S.inv' := HEq.trans h2 h1
--       --       exact eq_of_heq h3
--       --     -- have h4 : (((feq ▸ Eq.refl (S ≠ zero → ℚ)) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') = S.inv' := by
--       --     --   -- simp only []
--       --     --   unfold Eq.symm
--       --     --   generalize ((((feq ▸ Eq.refl (S ≠ zero → ℚ)): (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ rfl) : (a.fst ≠ zero → ℚ) = (S ≠ zero → ℚ)) = x
--       --     --   generalize ((x ▸ rfl) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) = y
--       --     --   have h1 : y ▸ S.inv' ≍ S.inv' := cast_heq _ _
--       --     --   have h2 : x ▸ y ▸ S.inv' ≍ y ▸ S.inv' := cast_heq _ _
--       --     --   have h3 : x ▸ y ▸ S.inv' ≍ S.inv' := HEq.trans h2 h1
--       --     --   exact eq_of_heq h3


--       --       -- ((((sorry):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')
--       --       -- ((((feq ▸ Eq.refl (S ≠ zero → ℚ)):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')
--       --       -- ((((feq ▸ Eq.refl (S ≠ zero → ℚ)):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')
--       --     -- guard_expr (feq ▸ Eq.refl ℚ ▸ Eq.refl (S ≠ zero → ℚ)) =~ (feq ▸ Eq.refl ℚ ▸ Eq.refl (S ≠ zero → ℚ))
--       --     -- exact inv_fn S.sys_of_repr (feq.mpr h'')
--       --     -- exact inv_fn S.sys_of_repr (fun h' => h'' (num_eq_zero' S.sys_of_repr_spec h'))
--       --     simp?

--       --   -- intro a h'
--       --   -- apply heq_of_eqRec_eq
--       --   -- have feq : (S ≠ zero) = (a.fst ≠ zero) := sorry
--       --   -- case h₁ =>
--       --   --   -- congr 1
--       --   --   refine' implies_congr _ rfl
--       --   --   apply congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
--       --   -- case h₂ =>
--       --   --   funext h''
--       --   --   apply EC.sound' eqv.eqv _ (EC.is_member_of_from_elm _ eqv.eqv) _
--       --   --   -- unfold inv_fn
--       --   --   exact inv_fn S.sys_of_repr h''
--       --   --   -- exact inv_fn S.sys_of_repr (fun h' => h'' (num_eq_zero' S.sys_of_repr_spec h'))
--       --   --   simp?


--       --   -- refine @heq_of_eq _


--     def inv : (Σ'(a : ℚ), a ≠ zero) → ℚ :=
--       fun a => a.fst.inv' a.snd
--       -- fun ah => inv_fn ⟨ah.fst.sys_of_repr, (by
--       --   intro h
--       --   let a := ah.fst.sys_of_repr
--       --   have h' := num_eq_zero' ah.fst.sys_of_repr_spec h
--       --   have := ah.snd h'
--       --   -- have h' := EC.sound' (a := a) eqv.eqv (EC.sys_of_repr_spec _) zero_is_member_zero
--       --   -- unfold eqv zero_repr at h'
--       --   -- simp only [mul_one, mul_zero] at h'
--       --   -- replace h' := h' h
--       --   -- have := num_eq_zero_of_eq_zero' ah.fst.sys_of_repr_spec h'
--       --   -- have := num_eq_zero' ah.fst.sys_of_repr_spec h'
--       --   -- have := EC.sound_inv eqv.eqv h
--       --   sorry
--       -- )⟩

--     @[default_instance] instance : Inv ℚ where
--       inv := inv

--     theorem inv_def {a : ℚ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = inv ⟨a, h⟩ := rfl

--     -- the more useful one :
--     theorem inv_def' {a : ℚ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = a.inv' h := rfl

--     private theorem _mul_inv_cancel : ∀ (a : ℚ) (h0 : a ≠ zero), a * ⟨a, h0⟩⁻¹ = one := by
--       intro a h0
--       rw [mul_def, inv_def', inv_spec a.sys_of_repr_spec]
--       unfold mul mul_fn mul_fn_fn inv_fn
--       rw [EC.lift_spec a _ a.sys_of_repr_spec,
--         EC.lift_spec _ _ (EC.is_member_of_from_elm _ _)]
--       apply EC.sound
--       unfold mul_fn_fn_fn inv_fn_fn one_repr eqv
--       simp only [mul_one]
--       let ap := a.sys_of_repr
--       apply Or.elim'_spec (c := ℚ_con) (p := (fun x => (ap.fst * x.fst = ap.snd * x.snd))) _ _
--       <;>simp only [mul_neg_right]<;>intro<;>ac_nf

--     @[default_instance] instance : Field ℚ where
--       mul_inv_cancel := _mul_inv_cancel

--   end inv

--   section comp


--     def le_fn_fn : ℚ_con → ℚ_con → Prop :=
--       fun a b => a.fst * b.snd ≤ a.snd * b.fst

--     private theorem le_fn_respect (a : ℚ_con) : ∀ (b c : ℚ_con), eqv b c → le_fn_fn a b = le_fn_fn a c := by
--       intro b c h
--       have h' {a b c : ℚ_con} : eqv b c → le_fn_fn a b → le_fn_fn a c := by
--         unfold eqv le_fn_fn
--         intro h h'
--         rw [←mul_le_mul_pos_right_iff c.h, mul_assoc a.snd, h] at h'
--         rw [←mul_le_mul_pos_right_iff b.h]
--         ac_nf at *
--       exact propext ⟨h' h, h' h.symm⟩

--     def le_fn : ℚ_con → ℚ → Prop :=
--       fun a => EquivalentClass.lift eqv.eqv (le_fn_fn a) (le_fn_respect a)

--     private theorem le_respect : ∀ (a b : ℚ_con), eqv a b → le_fn a = le_fn b := by
--       intro a b h
--       funext c
--       have h' {a b : ℚ_con} {c : ℚ} : eqv a b → le_fn a c → le_fn b c := by
--         intro h h'
--         unfold eqv le_fn at *
--         repeat rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)] at *
--         unfold le_fn_fn at *
--         rw [←mul_le_mul_pos_left_iff a.h, ←mul_assoc, ← h]
--         rw [←mul_le_mul_pos_left_iff b.h] at h'
--         ac_nf at |- h'
--       exact propext ⟨h' h, h' h.symm⟩

--     def le : ℚ → ℚ → Prop :=
--       EquivalentClass.lift (β := ℚ → Prop) eqv.eqv le_fn le_respect

--     private theorem _le_refl : ∀ (a : ℚ), a.le a := by
--       intro a
--       unfold le le_fn le_fn_fn EC.lift
--       simp only [mul_comm]
--       exact le_refl _

--     private theorem _le_trans : ∀ (a b c : ℚ), a.le b → b.le c → a.le c := by
--       intro a b c
--       unfold le le_fn le_fn_fn EC.lift
--       simp only
--       generalize a.sys_of_repr = a
--       generalize b.sys_of_repr = b
--       generalize c.sys_of_repr = c
--       intro h h'
--       rw [←mul_le_mul_pos_right_iff b.h]
--       rw [←mul_le_mul_pos_right_iff c.h] at h
--       rw [←mul_le_mul_pos_right_iff a.h] at h'
--       ac_nf at *
--       exact le_trans _ _ _ h h'

--     private theorem _le_antisymm : ∀ (a b : ℚ), a.le b → b.le a → a = b := by
--       intro a b
--       unfold le le_fn le_fn_fn EC.lift
--       intro h h'
--       apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
--       simp only [eqv] at *
--       ac_nf at *
--       exact le_antisymm _ _ h h'

--     private theorem _le_total : ∀ (a b : ℚ), a.le b ∨ b.le a := by
--       intro a b
--       unfold le le_fn le_fn_fn EC.lift
--       simp only
--       generalize a.sys_of_repr = a
--       generalize b.sys_of_repr = b
--       ac_nf
--       exact le_total _ _

--     @[default_instance] instance : Comp ℚ where
--       le := le
--       le_refl := _le_refl
--       le_trans := _le_trans
--       le_antisymm := _le_antisymm
--       le_total := _le_total

--     theorem le_def {a b : ℚ} : (a ≤ b) = a.le b := rfl

--     private theorem _add_le_add_left {a b : ℚ} : ∀(c : ℚ), a ≤ b → c + a ≤ c + b := by
--       intro c
--       simp only [le_def, add_def]
--       let ap := a.sys_of_repr
--       let bp := b.sys_of_repr
--       let cp := c.sys_of_repr
--       unfold le le_fn le_fn_fn add add_fn add_fn_fn
--       intro h
--       replace h : ap.fst * bp.snd ≤ ap.snd * bp.fst := h
--       repeat first
--       | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
--       | rw [EC.lift_spec _ _ b.sys_of_repr_spec]
--       | rw [EC.lift_spec _ _ c.sys_of_repr_spec]
--       | rw [EC.lift_spec _ (add_fn_fn_fn cp ap) (EC.is_member_of_from_elm _ eqv.eqv)]
--       | rw [EC.lift_spec _ (add_fn_fn_fn cp bp) (EC.is_member_of_from_elm _ eqv.eqv)]
--       unfold add_fn_fn_fn
--       simp only [mul_add, add_mul]
--       ac_nf
--       simp only [add_le_add_right_iff, ←mul_assoc, mul_le_mul_pos_right_iff cp.h]
--       ac_nf at h |-

--     @[default_instance] instance : OrderedCommMonoid ℚ where
--       _add_le_add_left := _add_le_add_left

--     @[default_instance] instance : OrderedCommGroup ℚ where

--     private theorem _mul_nonneg {a b : ℚ} : zero ≤ a → zero ≤ b → zero ≤ a * b := by
--       simp [le_def, mul_def]
--       let ap := a.sys_of_repr
--       let bp := b.sys_of_repr
--       unfold le le_fn mul mul_fn mul_fn_fn
--       repeat first
--       | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
--       | rw [EC.lift_spec _ _ b.sys_of_repr_spec]
--       | rw [EC.lift_spec _ _ zero_is_member_zero]
--       | rw [EC.lift_spec _ (mul_fn_fn_fn ap bp) (EC.is_member_of_from_elm _ eqv.eqv)]
--       unfold le_fn_fn mul_fn_fn_fn zero_repr
--       simp only [zero_mul, one_mul]
--       exact mul_nonneg

--     private theorem _zero_le_one : zero ≤ one := by
--       rw [le_def]
--       unfold le le_fn le_fn_fn
--       rw [EC.lift_spec _ _ zero_is_member_zero]
--       rw [EC.lift_spec _ _ one_is_member_one]
--       unfold zero_repr one_repr
--       simp only [mul_one]
--       exact zero_le_one


--     @[default_instance] instance : OrderedCommRing ℚ where
--       _mul_nonneg := _mul_nonneg
--       _zero_le_one := _zero_le_one

--     -- private theorem _mul_eq_zero {a b : ℚ} : a * b = zero → a = zero ∨ b = zero := by
--     --   rw [mul_def]
--     --   unfold mul mul_fn mul_fn_fn EC.lift mul_fn_fn_fn
--     --   intro h
--     --   replace h := EC.sound_inv eqv.eqv h
--     --   unfold eqv zero_repr at h
--     --   simp only [mul_zero, mul_one] at h
--     --   exact (mul_eq_zero h).elim
--     --     (fun h' => Or.inl (num_eq_zero' a.sys_of_repr_spec h'))
--     --     (fun h' => Or.inr (num_eq_zero' b.sys_of_repr_spec h'))

--     -- @[default_instance] instance : OrderedCommRing' ℚ where
--     --   mul_eq_zero := _mul_eq_zero

--     @[default_instance] instance : OrderedField ℚ where

--   end comp


-- end ℚ

end my
