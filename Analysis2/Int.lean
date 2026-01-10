import Analysis2.Operator
import Analysis2.Structure
import Analysis2.Comp
import Analysis2.EquivalentClass
import Analysis2.Nat

noncomputable section
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing
open Comp
open Zero One



structure ℕ_pair where
  fst : ℕ
  snd : ℕ

def ℤ.eqv : ℕ_pair → ℕ_pair → Prop :=
  fun ⟨a1, a2⟩ ⟨b1, b2⟩ => a1 + b2 = a2 + b1

namespace ℤ.eqv

  theorem refl : ∀ (a : ℕ_pair), ℤ.eqv a a :=
    fun ⟨a1, a2⟩ => add_comm a1 a2

  theorem symm : ∀ {a b : ℕ_pair}, ℤ.eqv a b → ℤ.eqv b a := by
    unfold eqv
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp only [a1.add_comm, a2.add_comm] at *
    exact h.symm

  theorem trans : ∀ {a b c : ℕ_pair}, ℤ.eqv a b → ℤ.eqv b c → ℤ.eqv a c := by
    unfold eqv
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩ h1 h2
    simp only [] at *
    replace h1 := (ℕ.add_left_inj (b2 + c1)).mpr h1
    rw (occs := .pos [1]) [←h2] at h1
    rw [
      ←add_assoc, ←add_assoc,
      add_assoc a1, add_assoc a2,
      add_right_comm a1, add_right_comm a2,
      add_comm b1, ℕ.add_left_inj
    ] at h1
    trivial

  def eqv : Equivalence ℤ.eqv where
    refl := refl
    symm := symm
    trans := trans

end ℤ.eqv

def ℤ := EquivalentClass ℤ.eqv


namespace ℤ
  open my renaming EquivalentClass → EC

  abbrev mk' (a : ℕ_pair) := EquivalentClass.from_elm eqv.eqv a


  section nums

    def zero_repr : ℕ_pair := ⟨zero, zero⟩
    def _zero : ℤ := ℤ.mk' zero_repr
    @[default_instance] instance : Zero ℤ := ⟨_zero⟩
    theorem zero_is_member_zero : zero.is_member zero_repr := EquivalentClass.is_member_of_from_elm zero_repr eqv.eqv

    def one_repr : ℕ_pair := ⟨one, zero⟩
    def _one : ℤ := ℤ.mk' one_repr
    @[default_instance] instance : One ℤ := ⟨_one⟩
    theorem one_is_member_one : one.is_member one_repr := EquivalentClass.is_member_of_from_elm one_repr eqv.eqv
    def two_repr : ℕ_pair := ⟨ℕ.two, zero⟩
    def two : ℤ := ℤ.mk' two_repr
    theorem two_is_member_two : two.is_member two_repr := EquivalentClass.is_member_of_from_elm two_repr eqv.eqv
    def three_repr : ℕ_pair := ⟨ℕ.three, zero⟩
    def three : ℤ := ℤ.mk' three_repr
    theorem three_is_member_three : three.is_member three_repr := EquivalentClass.is_member_of_from_elm three_repr eqv.eqv
    def four_repr : ℕ_pair := ⟨ℕ.four, zero⟩
    def four : ℤ := ℤ.mk' four_repr
    theorem four_is_member_four : four.is_member four_repr := EquivalentClass.is_member_of_from_elm four_repr eqv.eqv
    def five_repr : ℕ_pair := ⟨ℕ.five, zero⟩
    def five : ℤ := ℤ.mk' five_repr
    theorem five_is_member_five : five.is_member five_repr := EquivalentClass.is_member_of_from_elm five_repr eqv.eqv
    def six_repr : ℕ_pair := ⟨ℕ.six, zero⟩
    def six : ℤ := ℤ.mk' six_repr
    theorem six_is_member_six : six.is_member six_repr := EquivalentClass.is_member_of_from_elm six_repr eqv.eqv
    def seven_repr : ℕ_pair := ⟨ℕ.seven, zero⟩
    def seven : ℤ := ℤ.mk' seven_repr
    theorem seven_is_member_seven : seven.is_member seven_repr := EquivalentClass.is_member_of_from_elm seven_repr eqv.eqv

    def neg_one_repr : ℕ_pair := ⟨zero, one⟩
    def neg_one : ℤ := ℤ.mk' neg_one_repr
    theorem neg_one_is_member_neg_one : neg_one.is_member neg_one_repr := EquivalentClass.is_member_of_from_elm neg_one_repr eqv.eqv
    def neg_two_repr : ℕ_pair := ⟨zero, ℕ.two⟩
    def neg_two : ℤ := ℤ.mk' neg_two_repr
    theorem neg_two_is_member_neg_two : neg_two.is_member neg_two_repr := EquivalentClass.is_member_of_from_elm neg_two_repr eqv.eqv
    def neg_three_repr : ℕ_pair := ⟨zero, ℕ.three⟩
    def neg_three : ℤ := ℤ.mk' neg_three_repr
    theorem neg_three_is_member_neg_three : neg_three.is_member neg_three_repr := EquivalentClass.is_member_of_from_elm neg_three_repr eqv.eqv
    def neg_four_repr : ℕ_pair := ⟨zero, ℕ.four⟩
    def neg_four : ℤ := ℤ.mk' neg_four_repr
    theorem neg_four_is_member_neg_four : neg_four.is_member neg_four_repr := EquivalentClass.is_member_of_from_elm neg_four_repr eqv.eqv
    def neg_five_repr : ℕ_pair := ⟨zero, ℕ.five⟩
    def neg_five : ℤ := ℤ.mk' neg_five_repr
    theorem neg_five_is_member_neg_five : neg_five.is_member neg_five_repr := EquivalentClass.is_member_of_from_elm neg_five_repr eqv.eqv
    def neg_six_repr : ℕ_pair := ⟨zero, ℕ.six⟩
    def neg_six : ℤ := ℤ.mk' neg_six_repr
    theorem neg_six_is_member_neg_six : neg_six.is_member neg_six_repr := EquivalentClass.is_member_of_from_elm neg_six_repr eqv.eqv
    def neg_seven_repr : ℕ_pair := ⟨zero, ℕ.seven⟩
    def neg_seven : ℤ := ℤ.mk' neg_seven_repr
    theorem neg_seven_is_member_neg_seven : neg_seven.is_member neg_seven_repr := EquivalentClass.is_member_of_from_elm neg_seven_repr eqv.eqv



    theorem zero_ne_one : zero ≠ one := by
      intro h
      replace h := EC.sound_inv eqv.eqv h
      unfold eqv zero_repr one_repr at h
      simp only [ℕ.zero_add] at h
      exact ℕ.zero_ne_one h


  end nums

  section add

    def add_fn_fn_fn : ℕ_pair → ℕ_pair → ℕ_pair :=
      fun a b => ⟨a.fst + b.fst, a.snd + b.snd⟩

    def add_fn_fn : ℕ_pair → ℕ_pair → ℤ :=
      fun a b => ℤ.mk' (add_fn_fn_fn a b)

    private theorem add_fn_respect (a : ℕ_pair) : ∀ (b c : ℕ_pair), eqv b c → add_fn_fn a b = add_fn_fn a c := by
      intro ⟨b1, b2⟩ ⟨b1', b2'⟩ h'
      apply EquivalentClass.sound
      unfold eqv add_fn_fn_fn at *
      simp only [] at *
      rw [
        ←add_assoc, ←add_assoc,
        add_right_comm a.fst, add_right_comm a.snd,
        add_comm a.fst,
        add_assoc _ b1, add_assoc _ b2
      ]
      exact (ℕ.add_right_inj _).mpr h'

    def add_fn : ℕ_pair → ℤ → ℤ :=
      fun a => EquivalentClass.lift (β := ℤ) eqv.eqv (add_fn_fn a) (add_fn_respect a)

    private theorem add_respect : ∀ (a b : ℕ_pair), eqv a b → add_fn a = add_fn b := by
      intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
      funext Sc
      let c := Sc.sys_of_repr
      apply EquivalentClass.sound
      unfold eqv add_fn_fn_fn at *
      simp only [] at *
      rw [
        ← add_assoc, ← add_assoc,
        add_right_comm a1, add_right_comm a2,
        add_right_comm, h
      ]

    def add : ℤ → ℤ → ℤ :=
      EquivalentClass.lift (β := ℤ → ℤ) eqv.eqv add_fn add_respect

    instance : Add ℤ := {add}

    theorem add_def {a b : ℤ} : a + b = a.add b := rfl

    theorem _add_zero : ∀(n : ℤ), n + zero = n := by
      intro n
      let np := n.sys_of_repr
      rw [add_def]
      unfold add add_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ zero_repr zero_is_member_zero]
      unfold add_fn_fn add_fn_fn_fn zero_repr
      simp only [ℕ.add_zero]
      exact (EquivalentClass.from_sys_of_repr _).symm

    theorem _add_comm : ∀(n m : ℤ), n + m = m + n := by
      intro n m
      let np := n.sys_of_repr
      let mp := m.sys_of_repr
      repeat rw [add_def]
      unfold add add_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      unfold add_fn_fn add_fn_fn_fn
      rw [np.fst.add_comm, np.snd.add_comm]

    theorem _zero_add : ∀(n : ℤ), zero + n = n :=
      fun n => Eq.substr (_add_comm zero n) n._add_zero

    theorem _add_assoc : ∀ (a b c : ℤ), (a + b) + c = a + (b + c) := by
      intro a b c
      repeat rw [add_def]
      unfold add add_fn add_fn_fn
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      let abp := (add_fn_fn_fn ap bp)
      let bcp := (add_fn_fn_fn bp cp)
      let ab := mk' abp
      let bc := mk' bcp
      rw [EquivalentClass.lift_spec _ ap a.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ bp b.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ bp b.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ cp c.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ abp (EquivalentClass.is_member_of_from_elm abp _)]
      rw [EquivalentClass.lift_spec _ cp c.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ bcp (EquivalentClass.is_member_of_from_elm bcp _)]
      unfold abp bcp add_fn_fn_fn
      rw [add_assoc, add_assoc]

    @[default_instance] instance ℤ_Monoid : Monoid ℤ where
      add_zero := _add_zero
      zero_add := _zero_add
      add_assoc := _add_assoc

    -- theorem zero_def : Monoid.zero = zero := rfl

    @[default_instance] instance ℤ_CommMonoid : CommMonoid ℤ where
      add_comm := _add_comm


    -- instance : Std.Associative (α := ℤ) add := ⟨add_assoc⟩
    -- instance : Std.Commutative (α := ℤ) add := ⟨add_comm⟩

    -- theorem add_right_comm : ∀ (a b c : ℤ), (a + b) + c = (a + c) + b := by
    --   intros _ b _
    --   repeat rw [add_assoc]
    --   rw [add_comm b]

    -- theorem add_left_comm : ∀ (a b c : ℤ), a + (b + c) = b + (a + c) := by
    --   intros
    --   ac_nf

    theorem add_left_inj {a b : ℤ} : ∀ (c : ℤ), a + c = b + c ↔ a = b := by
      intro c
      apply Iff.intro
      case mp =>
        intro h
        apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
        replace h := EC.sound_inv eqv.eqv h
        unfold eqv add_fn_fn_fn at *
        simp only [] at *
        rw (occs := .pos [1]) [add_right_comm] at h
        rw (occs := .pos [2]) [add_right_comm] at h
        simp only [←add_assoc] at h
        rw (occs := .pos [3]) [add_right_comm] at h
        simp only [ℕ.add_left_inj] at h
        assumption
      case mpr =>
        intro h;simp only [h]

    theorem add_right_inj {a b : ℤ} : ∀ (c : ℤ), c + a = c + b ↔ a = b := by
      intro c
      simp only [add_comm]
      exact add_left_inj c


  end add

  section neg

    def neg_fn_fn : ℕ_pair → ℕ_pair :=
      fun a => ⟨a.snd, a.fst⟩

    def neg_fn : ℕ_pair → ℤ :=
      fun a => mk' (neg_fn_fn a)

    private theorem neg_respect : ∀ (a b : ℕ_pair), eqv a b → neg_fn a = neg_fn b :=
      fun _ _ h => EC.sound eqv.eqv (Eq.symm (id h))

    def neg : ℤ → ℤ :=
      EC.lift eqv.eqv neg_fn neg_respect

    @[default_instance] instance : Neg ℤ := {neg}

    theorem neg_def {a : ℤ} : -a = a.neg:= rfl

    theorem _add_neg : ∀(a : ℤ), a + (-a) = zero := by
      intro a
      rw [neg_def, add_def]
      let ap := a.sys_of_repr
      let nap := neg_fn_fn ap
      unfold add add_fn add_fn_fn neg neg_fn
      repeat first
      | rw [EC.lift_spec _ ap a.sys_of_repr_spec]
      | rw [EC.lift_spec _ nap (EC.is_member_of_from_elm nap _)]
      apply EC.sound
      unfold nap neg_fn_fn add_fn_fn_fn eqv zero_repr
      simp only
      ac_nf

    @[default_instance] instance : CommGroup ℤ where
      add_neg := _add_neg

  end neg

  section sub

  end sub

  section mul

    def mul_fn_fn_fn : ℕ_pair → ℕ_pair → ℕ_pair :=
      fun a b => ⟨(a.fst * b.fst) + (a.snd * b.snd), (a.fst * b.snd) + (a.snd * b.fst)⟩

    def mul_fn_fn : ℕ_pair → ℕ_pair → ℤ :=
      fun a b => ℤ.mk' (mul_fn_fn_fn a b)

    private theorem mul_fn_respect (a : ℕ_pair) : ∀ (b c : ℕ_pair), eqv b c → mul_fn_fn a b = mul_fn_fn a c := by
      intro ⟨b1, b2⟩ ⟨b1', b2'⟩ h'
      apply EquivalentClass.sound
      unfold eqv mul_fn_fn_fn at *
      simp only [] at *
      rw [
        ←add_assoc, ←add_assoc,
        add_right_comm (a.fst * b1), add_right_comm (a.fst * b2),
        ← mul_add, ← mul_add,
        add_assoc, add_assoc,
        ← mul_add, ← mul_add, h'
      ]

    def mul_fn : ℕ_pair → ℤ → ℤ :=
      fun a => EquivalentClass.lift (β := ℤ) eqv.eqv (mul_fn_fn a) (mul_fn_respect a)

    private theorem mul_respect : ∀ (a b : ℕ_pair), eqv a b → mul_fn a = mul_fn b := by
      intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
      funext Sc
      let (eq:=eqc) c := Sc.sys_of_repr
      apply EquivalentClass.sound
      unfold eqv mul_fn_fn_fn at *
      simp only [] at *
      rw [
        ← eqc,
        ← add_assoc, ← add_assoc,
        add_right_comm _ _ (b2 * c.fst),
        add_right_comm _ _ (b2 * c.fst),
        ← add_mul, add_assoc, ← add_mul,
        add_comm (a1 * _),
        add_right_comm _ (a1 * _),
        ← add_mul, add_assoc, ← add_mul,
        h,
      ]

    def mul : ℤ → ℤ → ℤ :=
      EquivalentClass.lift (β := ℤ → ℤ) eqv.eqv mul_fn mul_respect

    instance : Mul ℤ := {mul}

    theorem mul_def {a b : ℤ} : a * b = a.mul b := rfl

    theorem _mul_zero : ∀(n : ℤ), n * zero = zero := by
      intro n
      let np := n.sys_of_repr
      repeat rw [mul_def]
      unfold mul mul_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ zero_repr zero_is_member_zero]
      unfold mul_fn_fn mul_fn_fn_fn zero_repr
      simp only [ℕ.mul_zero, ℕ.add_zero]
      rfl

    theorem _mul_one : ∀(n : ℤ), n * one = n := by
      intro n
      let np := n.sys_of_repr
      repeat rw [mul_def]
      unfold mul mul_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ one_repr one_is_member_one]
      unfold mul_fn_fn mul_fn_fn_fn one_repr
      simp only [ℕ.mul_zero, ℕ.add_zero, ℕ.mul_one, ℕ.zero_add]
      exact (EquivalentClass.from_sys_of_repr _).symm

    theorem _mul_comm : ∀(n m : ℤ), n * m = m * n := by
      intro n m
      let np := n.sys_of_repr
      let mp := m.sys_of_repr
      repeat rw [mul_def]
      unfold mul mul_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      unfold mul_fn_fn mul_fn_fn_fn
      rw [
        np.fst.mul_comm, np.fst.mul_comm,
        np.snd.mul_comm, np.snd.mul_comm,
        (mp.snd * np.fst).add_comm
      ]

    theorem _zero_mul : ∀(n : ℤ), zero * n = zero :=
      fun n => Eq.substr (_mul_comm zero n) n._mul_zero

    theorem _one_mul : ∀(n : ℤ), one * n = n :=
      fun n => Eq.substr (_mul_comm one n) n._mul_one

    theorem _mul_assoc : ∀ (a b c : ℤ), (a * b) * c = a * (b * c) := by
      intro a b c
      repeat rw [mul_def]
      unfold mul mul_fn mul_fn_fn
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      let abp := (mul_fn_fn_fn ap bp)
      let bcp := (mul_fn_fn_fn bp cp)
      let ab := mk' abp
      let bc := mk' bcp
      rw [EC.lift_spec _ ap a.sys_of_repr_spec]
      rw [EC.lift_spec _ bp b.sys_of_repr_spec]
      rw [EC.lift_spec _ bp b.sys_of_repr_spec]
      rw [EC.lift_spec _ cp c.sys_of_repr_spec]
      rw [EC.lift_spec _ abp (EC.is_member_of_from_elm abp _)]
      rw [EC.lift_spec _ cp c.sys_of_repr_spec]
      rw [EC.lift_spec _ bcp (EC.is_member_of_from_elm bcp _)]
      apply EC.sound
      unfold abp bcp mul_fn_fn_fn eqv
      simp only [add_mul, mul_add]
      ac_nf

    theorem _mul_add : ∀ (a b c : ℤ), a * (b + c) = a * b + a * c := by
      intro a b c
      repeat rw [mul_def]
      repeat rw [add_def]
      unfold mul mul_fn mul_fn_fn add add_fn add_fn_fn
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      let abp := (mul_fn_fn_fn ap bp)
      let acp := (mul_fn_fn_fn ap cp)
      let bcp := (add_fn_fn_fn bp cp)
      let bc := mk' bcp
      rw [EC.lift_spec _ ap a.sys_of_repr_spec]
      rw [EC.lift_spec _ bp b.sys_of_repr_spec]
      rw [EC.lift_spec _ cp c.sys_of_repr_spec]
      rw [EC.lift_spec _ bcp (EC.is_member_of_from_elm bcp _)]
      rw [EC.lift_spec _ bp b.sys_of_repr_spec]
      rw [EC.lift_spec _ cp c.sys_of_repr_spec]
      rw [EC.lift_spec _ abp (EC.is_member_of_from_elm abp _)]
      rw [EC.lift_spec _ acp (EC.is_member_of_from_elm acp _)]
      unfold abp acp bcp add_fn_fn_fn mul_fn_fn_fn
      simp only [mul_add]
      ac_nf

    theorem _add_mul : ∀ (a b c : ℤ), (a + b) * c = a * c + b * c := by
      intro a b c
      simp only [_mul_comm _ c, _mul_add]

    @[default_instance] instance t : SemiRing ℤ where
      mul_one := _mul_one
      one_mul := _one_mul
      mul_assoc := _mul_assoc
      mul_zero := _mul_zero
      zero_mul := _zero_mul
      mul_add := _mul_add
      add_mul := _add_mul


    @[default_instance] instance : CommSemiRing ℤ where
      mul_comm := _mul_comm

    @[default_instance] instance : CommRing ℤ where

    theorem mul_right_comm : ∀ (a b c : ℤ), (a * b) * c = (a * c) * b := by
      intros
      ac_nf

    theorem mul_left_comm : ∀ (a b c : ℤ), a * (b * c) = b * (a * c) := by
      intros
      ac_nf

    theorem mul_left_inj {a b c : ℤ} (ha : c ≠ zero) : a * c = b * c ↔ a = b := by
      apply Iff.intro
      case mpr => intro h;rw [h]
      case mp =>
        let ap := a.sys_of_repr
        let bp := b.sys_of_repr
        let cp := c.sys_of_repr
        repeat rw [mul_def]
        unfold mul mul_fn mul_fn_fn mul_fn_fn_fn
        rw [EquivalentClass.lift_spec a ap a.sys_of_repr_spec]
        rw [EquivalentClass.lift_spec b bp b.sys_of_repr_spec]
        rw [EquivalentClass.lift_spec c cp c.sys_of_repr_spec]
        rw [EquivalentClass.lift_spec c cp c.sys_of_repr_spec]
        intro h
        replace h := EC.sound_inv eqv.eqv h
        simp only [eqv] at h
        replace h : ((ap.fst + bp.snd) * cp.fst) + ((ap.snd + bp.fst) * cp.snd) = ((ap.fst + bp.snd) * cp.snd) + ((ap.snd + bp.fst) * cp.fst) := by
          simp only [add_mul] at |- h
          ac_nf at |- h
        have hc_neq : cp.fst ≠ cp.snd := by
          intro heq
          apply ha
          refine' EC.sound' eqv.eqv c.sys_of_repr_spec zero_is_member_zero _
          unfold eqv zero_repr
          show cp.fst + zero = cp.snd + zero
          rw [ℕ.add_zero, ℕ.add_zero, heq]
        apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
        show ap.fst + bp.snd = ap.snd + bp.fst

        have l1 (a1 a2 b1 b2 c1 c2 : ℕ) (h : c1 < c2)
          (h' : ((a1 + b2) * c1) + ((a2 + b1) * c2) = ((a1 + b2) * c2) + ((a2 + b1) * c1))
          : a1 + b2 = a2 + b1 := by
            have ⟨x, hx⟩ := le_of_lt h
            rw [hx] at h'
            simp only [add_mul, mul_add] at h'
            ac_nf at h'
            rw [add_comm (b1 * x) _] at h'
            repeat rw [add_left_comm (_ * x) _ _] at h'
            simp only [ℕ.add_right_inj, ← add_mul] at h'
            have hx0 : x ≠ zero := fun h' => by rw [h', ℕ.add_zero] at hx;exact (ne_of_lt h) hx.symm
            replace h' := (ℕ.mul_left_inj hx0).mp h'
            ac_nf at h' |-;symm;assumption

        rcases lt_or_eq_or_gt cp.fst cp.snd with hl | hc_eq | hl
        case _ => exact l1 _ _ _ _ _ _ hl h
        case _ => exact (hc_neq hc_eq).elim
        case _ => exact l1 _ _ _ _ _ _ hl h.symm

    theorem mul_right_inj {a b c : ℤ} (hc : c ≠ zero) : c * a = c * b ↔ a = b := by
      simp only [mul_comm]
      exact mul_left_inj hc

    theorem mul_eq_zero {a b : ℤ} : a * b = zero → a = zero ∨ b = zero := by
      intro h
      by_cases ha0 : a = zero
      case pos => exact Or.inl ha0
      case neg =>
        -- replace h : a * b = Monoid.zero := h
        -- guard_hyp h : a * b = Monoid.zero
        -- guard_hyp h :~ a * b = Monoid.zero
        -- guard_hyp h :ₛ a * b = Monoid.zero
        -- guard_hyp h :ₐ a * b = Monoid.zero
        -- with_unfolding_all guard_expr zero =ₛ Monoid.zero
        with_unfolding_all guard_expr a+b =~ a.add b
        rw [← mul_zero a, mul_right_inj ha0] at h
        exact Or.inr h


  end mul

  section comp

    def le_fn_fn : ℕ_pair → ℕ_pair → Prop :=
      fun a b => (a.fst + b.snd) ≤ (a.snd + b.fst)

    private theorem le_fn_respect (a : ℕ_pair) : ∀ (b b' : ℕ_pair), eqv b b' → le_fn_fn a b = le_fn_fn a b' := by
      intro ⟨b1, b2⟩ ⟨b1', b2'⟩ h'
      unfold eqv le_fn_fn at *
      simp only [] at *
      apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro ⟨x, h⟩
        refine ⟨x, ?_⟩
        replace h := (ℕ.add_left_inj b1').mpr h
        apply (ℕ.add_left_inj b1).mp
        rw [
          add_right_comm, h,
          add_right_comm _ _ b1,
          add_right_comm _ _ b1,
          add_assoc _ b1, h',
          add_right_comm, ←add_assoc
        ]
      case mpr =>
        intro ⟨x, h⟩
        refine ⟨x, ?_⟩
        replace h := (ℕ.add_left_inj b1).mpr h
        apply (ℕ.add_left_inj b1').mp
        rw [
          add_right_comm, h,
          add_right_comm _ _ b1,
          add_right_comm _ _ b1,
          add_assoc _ b1, h',
          add_right_comm _ x, ←add_assoc
        ]

    def le_fn : ℕ_pair → ℤ → Prop :=
      fun a => EC.lift eqv.eqv (le_fn_fn a) (le_fn_respect a)

    private theorem le_respect : ∀ (a a' : ℕ_pair), eqv a a' → le_fn a = le_fn a' := by
      intro ⟨a1, a2⟩ ⟨a1', a2'⟩ h
      funext Sc
      let (eq:=eqc) c := Sc.sys_of_repr
      unfold eqv le_fn le_fn_fn at *
      simp only [] at *
      conv =>
        lhs
        pattern fun b => _
        intro b
        rw [
          ← ℕ.add_le_add_iff_right (c := a2'),
          add_right_comm, h,
          add_right_comm _ b.fst,
        ]
      conv =>
        rhs
        pattern fun b => _
        intro b
        rw [
          ← ℕ.add_le_add_iff_right (c := a2),
          add_comm _ a2, add_comm _ a2,
          ← add_assoc, ← add_assoc,
        ]

    def le : ℤ → ℤ → Prop :=
      EC.lift eqv.eqv le_fn le_respect

    theorem le_refl : ∀ (a : ℤ), a.le a := by
      intro
      unfold le le_fn le_fn_fn eqv
      simp [EC.lift_spec _ _ (EC.sys_of_repr_spec _)] at *
      rw [add_comm]
      exact le_self _

    theorem le_trans : ∀(a b c : ℤ), a.le b → b.le c → a.le c := by
      intro a b c
      let bp := b.sys_of_repr
      unfold le le_fn le_fn_fn eqv
      simp [
        EC.lift_spec a _ a.sys_of_repr_spec,
        EC.lift_spec b bp b.sys_of_repr_spec,
        EC.lift_spec c _ c.sys_of_repr_spec] at *
      intro h1 h2
      have h3 := ℕ.add_le_le_le h1 h2
      repeat rw [add_assoc] at h3
      repeat rw [add_left_comm _ bp.fst] at h3
      repeat rw [add_left_comm _ bp.snd] at h3
      exact ℕ.add_le_add_iff_left.mp (ℕ.add_le_add_iff_left.mp h3)

    theorem le_antisymm : ∀(a b : ℤ), a.le b → b.le a → a = b := by
      intro a b hx hx'
      apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
      unfold le EC.lift le_fn EC.lift le_fn_fn eqv at *
      simp only
      ac_nf at *
      exact Comp.le_antisymm _ _ hx hx'

    theorem le_total : ∀(a b : ℤ), a.le b ∨ b.le a := by
      intro a b
      unfold le EC.lift le_fn EC.lift le_fn_fn eqv at *
      ac_nf
      exact Comp.le_total _ _

    @[default_instance] instance : Comp ℤ :=
      {le, le_refl, le_trans, le_antisymm, le_total}

    theorem le_def {a b : ℤ} : (a ≤ b) = a.le b := rfl

    @[reducible] def pos (n : ℤ) : Prop := zero < n

    @[reducible] def nonneg (n : ℤ) : Prop := zero ≤ n

    theorem zero_le_one : zero ≤ one := by
      repeat rw [le_def]
      unfold le le_fn le_fn_fn eqv
      simp only [
        EC.lift_spec _ zero_repr zero_is_member_zero,
        EC.lift_spec _ one_repr one_is_member_one,
        zero_repr, one_repr, ℕ.zero_add, ℕ.zero_le_one]

    theorem zero_lt_one : zero < one := by
      -- simp only [EC.lift_spec zero zero_repr zero_is_member_zero]
      refine' lt_of_le_ne zero_le_one zero_ne_one


      -- unfold le

    theorem le_total' : ∀(a b : ℤ), a ≤ b ∨ b ≤ a := by
      intro a b
      repeat rw [le_def]
      unfold le EC.lift le_fn EC.lift le_fn_fn eqv at *
      ac_nf
      exact Comp.le_total _ _

    -- theorem le_iff_add_nonneg

    theorem mul_nonneg {a b : ℤ} : a.nonneg → b.nonneg → (a * b).nonneg := by
      simp only [le_def]
      repeat rw [mul_def]
      unfold le le_fn le_fn_fn mul mul_fn mul_fn_fn
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let abp := mul_fn_fn_fn ap bp
      let ab := mk' abp
      simp [
        EC.lift_spec _ zero_repr zero_is_member_zero,
        EC.lift_spec a ap a.sys_of_repr_spec,
        EC.lift_spec b bp b.sys_of_repr_spec,
        -- EC.lift_spec _ abp (EC.is_member_of_from_elm abp _)
      ]
      rw [EC.lift_spec _ abp (EC.is_member_of_from_elm abp _)]
      unfold zero_repr abp mul_fn_fn_fn
      simp only [ℕ.zero_add] at *
      intro ⟨x, hx⟩ ⟨x', hx'⟩
      simp only [hx, hx', add_mul, mul_add]
      exists x * x'
      ac_nf

    theorem mul_le_mul_of_nonneg_left {a b c : ℤ} : a ≤ b → c.nonneg → c * a ≤ c * b := by
      sorry

    section nums

    end nums

  end comp


end ℤ
end my
