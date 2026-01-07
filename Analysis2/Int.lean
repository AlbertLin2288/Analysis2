import Analysis2.Logic
import Analysis2.EquivalentClass
import Analysis2.Nat

noncomputable section
namespace my
open Classical



structure ℕ_pair where
  fst : ℕ
  snd : ℕ

def ℤ.eqv : ℕ_pair → ℕ_pair → Prop :=
  fun ⟨a1, a2⟩ ⟨b1, b2⟩ => a1.add b2 = a2.add b1

namespace ℤ.eqv

  theorem refl : ∀ (a : ℕ_pair), ℤ.eqv a a :=
    fun ⟨a1, a2⟩ => ℕ.add_comm a1 a2

  theorem symm : ∀ {a b : ℕ_pair}, ℤ.eqv a b → ℤ.eqv b a := by
    unfold eqv
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp only [a1.add_comm, a2.add_comm] at *
    exact h.symm

  theorem trans : ∀ {a b c : ℕ_pair}, ℤ.eqv a b → ℤ.eqv b c → ℤ.eqv a c := by
    unfold eqv
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩ h1 h2
    simp only [] at *
    replace h1 := (ℕ.add_left_inj (b2.add c1)).mpr h1
    rw (occs := .pos [1]) [←h2] at h1
    rw [
      ←ℕ.add_assoc, ←ℕ.add_assoc,
      ℕ.add_assoc a1, ℕ.add_assoc a2,
      ℕ.add_right_comm a1, ℕ.add_right_comm a2,
      ℕ.add_comm b1, ℕ.add_left_inj
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

    def zero_repr : ℕ_pair := ⟨ℕ.zero, ℕ.zero⟩
    def zero : ℤ := ℤ.mk' zero_repr
    theorem zero_is_member_zero : zero.is_member zero_repr := EquivalentClass.is_member_of_from_elm zero_repr eqv.eqv

    def one_repr : ℕ_pair := ⟨ℕ.one, ℕ.zero⟩
    def one : ℤ := ℤ.mk' one_repr
    theorem one_is_member_one : one.is_member one_repr := EquivalentClass.is_member_of_from_elm one_repr eqv.eqv
    def two_repr : ℕ_pair := ⟨ℕ.two, ℕ.zero⟩
    def two : ℤ := ℤ.mk' two_repr
    theorem two_is_member_two : two.is_member two_repr := EquivalentClass.is_member_of_from_elm two_repr eqv.eqv
    def three_repr : ℕ_pair := ⟨ℕ.three, ℕ.zero⟩
    def three : ℤ := ℤ.mk' three_repr
    theorem three_is_member_three : three.is_member three_repr := EquivalentClass.is_member_of_from_elm three_repr eqv.eqv
    def four_repr : ℕ_pair := ⟨ℕ.four, ℕ.zero⟩
    def four : ℤ := ℤ.mk' four_repr
    theorem four_is_member_four : four.is_member four_repr := EquivalentClass.is_member_of_from_elm four_repr eqv.eqv
    def five_repr : ℕ_pair := ⟨ℕ.five, ℕ.zero⟩
    def five : ℤ := ℤ.mk' five_repr
    theorem five_is_member_five : five.is_member five_repr := EquivalentClass.is_member_of_from_elm five_repr eqv.eqv
    def six_repr : ℕ_pair := ⟨ℕ.six, ℕ.zero⟩
    def six : ℤ := ℤ.mk' six_repr
    theorem six_is_member_six : six.is_member six_repr := EquivalentClass.is_member_of_from_elm six_repr eqv.eqv
    def seven_repr : ℕ_pair := ⟨ℕ.seven, ℕ.zero⟩
    def seven : ℤ := ℤ.mk' seven_repr
    theorem seven_is_member_seven : seven.is_member seven_repr := EquivalentClass.is_member_of_from_elm seven_repr eqv.eqv

    def neg_one_repr : ℕ_pair := ⟨ℕ.zero, ℕ.one⟩
    def neg_one : ℤ := ℤ.mk' neg_one_repr
    theorem neg_one_is_member_neg_one : neg_one.is_member neg_one_repr := EquivalentClass.is_member_of_from_elm neg_one_repr eqv.eqv
    def neg_two_repr : ℕ_pair := ⟨ℕ.zero, ℕ.two⟩
    def neg_two : ℤ := ℤ.mk' neg_two_repr
    theorem neg_two_is_member_neg_two : neg_two.is_member neg_two_repr := EquivalentClass.is_member_of_from_elm neg_two_repr eqv.eqv
    def neg_three_repr : ℕ_pair := ⟨ℕ.zero, ℕ.three⟩
    def neg_three : ℤ := ℤ.mk' neg_three_repr
    theorem neg_three_is_member_neg_three : neg_three.is_member neg_three_repr := EquivalentClass.is_member_of_from_elm neg_three_repr eqv.eqv
    def neg_four_repr : ℕ_pair := ⟨ℕ.zero, ℕ.four⟩
    def neg_four : ℤ := ℤ.mk' neg_four_repr
    theorem neg_four_is_member_neg_four : neg_four.is_member neg_four_repr := EquivalentClass.is_member_of_from_elm neg_four_repr eqv.eqv
    def neg_five_repr : ℕ_pair := ⟨ℕ.zero, ℕ.five⟩
    def neg_five : ℤ := ℤ.mk' neg_five_repr
    theorem neg_five_is_member_neg_five : neg_five.is_member neg_five_repr := EquivalentClass.is_member_of_from_elm neg_five_repr eqv.eqv
    def neg_six_repr : ℕ_pair := ⟨ℕ.zero, ℕ.six⟩
    def neg_six : ℤ := ℤ.mk' neg_six_repr
    theorem neg_six_is_member_neg_six : neg_six.is_member neg_six_repr := EquivalentClass.is_member_of_from_elm neg_six_repr eqv.eqv
    def neg_seven_repr : ℕ_pair := ⟨ℕ.zero, ℕ.seven⟩
    def neg_seven : ℤ := ℤ.mk' neg_seven_repr
    theorem neg_seven_is_member_neg_seven : neg_seven.is_member neg_seven_repr := EquivalentClass.is_member_of_from_elm neg_seven_repr eqv.eqv

  end nums

  section add

    def add_fn_fn_fn : ℕ_pair → ℕ_pair → ℕ_pair :=
      fun a b => ⟨a.fst.add b.fst, a.snd.add b.snd⟩

    def add_fn_fn : ℕ_pair → ℕ_pair → ℤ :=
      fun a b => ℤ.mk' (add_fn_fn_fn a b)

    private theorem add_fn_respect (a : ℕ_pair) : ∀ (b c : ℕ_pair), eqv b c → add_fn_fn a b = add_fn_fn a c := by
      intro ⟨b1, b2⟩ ⟨b1', b2'⟩ h'
      apply EquivalentClass.sound
      unfold eqv add_fn_fn_fn at *
      simp only [] at *
      rw [
        ←ℕ.add_assoc, ←ℕ.add_assoc,
        ℕ.add_right_comm a.fst, ℕ.add_right_comm a.snd,
        ℕ.add_comm a.fst,
        ℕ.add_assoc _ b1, ℕ.add_assoc _ b2
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
        ← ℕ.add_assoc, ← ℕ.add_assoc,
        ℕ.add_right_comm a1, ℕ.add_right_comm a2,
        ℕ.add_right_comm, h
      ]

    def add : ℤ → ℤ → ℤ :=
      EquivalentClass.lift (β := ℤ → ℤ) eqv.eqv add_fn add_respect

    theorem add_zero : ∀(n : ℤ), n.add zero = n := by
      intro n
      let np := n.sys_of_repr
      unfold add add_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec zero zero_repr zero_is_member_zero]
      unfold add_fn_fn add_fn_fn_fn zero_repr
      simp only [ℕ.add_zero]
      exact (EquivalentClass.from_sys_of_repr _).symm

    theorem add_comm : ∀(n m : ℤ), n.add m = m.add n := by
      intro n m
      let np := n.sys_of_repr
      let mp := m.sys_of_repr
      unfold add add_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      unfold add_fn_fn add_fn_fn_fn
      rw [np.fst.add_comm, np.snd.add_comm]

    theorem zero_add : ∀(n : ℤ), zero.add n = n :=
      fun n => Eq.substr (zero.add_comm n) n.add_zero

    theorem add_assoc : ∀ (a b c : ℤ), (a.add b).add c = a.add (b.add c) := by
      intro a b c
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
      rw [ℕ.add_assoc, ℕ.add_assoc]


    instance : Std.Associative (α := ℤ) add := ⟨add_assoc⟩
    instance : Std.Commutative (α := ℤ) add := ⟨add_comm⟩

    theorem add_right_comm : ∀ (a b c : ℤ), (a.add b).add c = (a.add c).add b := by
      intros _ b _
      repeat rw [add_assoc]
      rw [add_comm b]

    theorem add_left_comm : ∀ (a b c : ℤ), a.add (b.add c) = b.add (a.add c) := by
      intros
      ac_nf

    theorem add_left_inj {a b : ℤ} : ∀ (c : ℤ), a.add c = b.add c ↔ a = b := by
      intro c
      apply Iff.intro
      case mp =>
        intro h
        apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
        replace h := EC.sound_inv eqv.eqv h
        unfold eqv add_fn_fn_fn at *
        simp only [] at *
        rw (occs := .pos [1]) [ℕ.add_right_comm] at h
        rw (occs := .pos [2]) [ℕ.add_right_comm] at h
        simp only [←ℕ.add_assoc] at h
        rw (occs := .pos [3]) [ℕ.add_right_comm] at h
        simp only [ℕ.add_left_inj] at h
        assumption
      case mpr =>
        intro h;simp only [h]

    theorem add_right_inj {a b : ℤ} : ∀ (c : ℤ), c.add a = c.add b ↔ a = b := by
      intro c
      simp only [c.add_comm]
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

  end neg

  section sub

  end sub

  section mul

    def mul_fn_fn_fn : ℕ_pair → ℕ_pair → ℕ_pair :=
      fun a b => ⟨(a.fst.mul b.fst).add (a.snd.mul b.snd), (a.fst.mul b.snd).add (a.snd.mul b.fst)⟩

    def mul_fn_fn : ℕ_pair → ℕ_pair → ℤ :=
      fun a b => ℤ.mk' (mul_fn_fn_fn a b)

    private theorem mul_fn_respect (a : ℕ_pair) : ∀ (b c : ℕ_pair), eqv b c → mul_fn_fn a b = mul_fn_fn a c := by
      intro ⟨b1, b2⟩ ⟨b1', b2'⟩ h'
      apply EquivalentClass.sound
      unfold eqv mul_fn_fn_fn at *
      simp only [] at *
      rw [
        ←ℕ.add_assoc, ←ℕ.add_assoc,
        ℕ.add_right_comm (a.fst.mul b1), ℕ.add_right_comm (a.fst.mul b2),
        ← ℕ.mul_add, ← ℕ.mul_add,
        ℕ.add_assoc, ℕ.add_assoc,
        ← ℕ.mul_add, ← ℕ.mul_add, h'
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
        ← ℕ.add_assoc, ← ℕ.add_assoc,
        ℕ.add_right_comm _ _ (b2.mul c.fst),
        ℕ.add_right_comm _ _ (b2.mul c.fst),
        ← ℕ.add_mul, ℕ.add_assoc, ← ℕ.add_mul,
        ℕ.add_comm (a1.mul _),
        ℕ.add_right_comm _ (a1.mul _),
        ← ℕ.add_mul, ℕ.add_assoc, ← ℕ.add_mul,
        h,
      ]

    def mul : ℤ → ℤ → ℤ :=
      EquivalentClass.lift (β := ℤ → ℤ) eqv.eqv mul_fn mul_respect

    theorem mul_zero : ∀(n : ℤ), n.mul zero = zero := by
      intro n
      let np := n.sys_of_repr
      unfold mul mul_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec zero zero_repr zero_is_member_zero]
      unfold mul_fn_fn mul_fn_fn_fn zero_repr
      simp only [ℕ.mul_zero, ℕ.add_zero]
      rfl

    theorem mul_one : ∀(n : ℤ), n.mul one = n := by
      intro n
      let np := n.sys_of_repr
      unfold mul mul_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec one one_repr one_is_member_one]
      unfold mul_fn_fn mul_fn_fn_fn one_repr
      simp only [ℕ.mul_zero, ℕ.add_zero, ℕ.mul_one, ℕ.zero_add]
      exact (EquivalentClass.from_sys_of_repr _).symm

    theorem mul_comm : ∀(n m : ℤ), n.mul m = m.mul n := by
      intro n m
      let np := n.sys_of_repr
      let mp := m.sys_of_repr
      unfold mul mul_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec m mp m.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      unfold mul_fn_fn mul_fn_fn_fn
      rw [
        np.fst.mul_comm, np.fst.mul_comm,
        np.snd.mul_comm, np.snd.mul_comm,
        (mp.snd.mul np.fst).add_comm
      ]

    theorem zero_mul : ∀(n : ℤ), zero.mul n = zero :=
      fun n => Eq.substr (zero.mul_comm n) n.mul_zero

    theorem one_mul : ∀(n : ℤ), one.mul n = n :=
      fun n => Eq.substr (one.mul_comm n) n.mul_one

    theorem mul_assoc : ∀ (a b c : ℤ), (a.mul b).mul c = a.mul (b.mul c) := by
      intro a b c
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
      simp only [ℕ.add_mul, ℕ.mul_add]
      ac_nf

    instance : Std.Associative (α := ℤ) mul := ⟨mul_assoc⟩
    instance : Std.Commutative (α := ℤ) mul := ⟨mul_comm⟩

    theorem mul_right_comm : ∀ (a b c : ℤ), (a.mul b).mul c = (a.mul c).mul b := by
      intros
      ac_nf

    theorem mul_left_comm : ∀ (a b c : ℤ), a.mul (b.mul c) = b.mul (a.mul c) := by
      intros
      ac_nf

    theorem mul_left_inj {a b c : ℤ} (ha : c ≠ zero) : a.mul c = b.mul c ↔ a = b := by
      apply Iff.intro
      case mpr => intro h;rw [h]
      case mp =>
        let ap := a.sys_of_repr
        let bp := b.sys_of_repr
        let cp := c.sys_of_repr
        unfold mul mul_fn mul_fn_fn mul_fn_fn_fn
        rw [EquivalentClass.lift_spec a ap a.sys_of_repr_spec]
        rw [EquivalentClass.lift_spec b bp b.sys_of_repr_spec]
        rw [EquivalentClass.lift_spec c cp c.sys_of_repr_spec]
        rw [EquivalentClass.lift_spec c cp c.sys_of_repr_spec]
        intro h
        replace h := EC.sound_inv eqv.eqv h
        simp only [eqv] at h
        replace h : ((ap.fst.add bp.snd).mul cp.fst).add ((ap.snd.add bp.fst).mul cp.snd) = ((ap.fst.add bp.snd).mul cp.snd).add ((ap.snd.add bp.fst).mul cp.fst) := by
          simp only [ℕ.add_mul] at |- h
          ac_nf at |- h
        have hc_neq : cp.fst ≠ cp.snd := by
          intro heq
          apply ha
          refine' EC.sound' eqv.eqv c.sys_of_repr_spec zero_is_member_zero _
          unfold eqv zero_repr
          show cp.fst.add ℕ.zero = cp.snd.add ℕ.zero
          rw [ℕ.add_zero, ℕ.add_zero, heq]
        apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
        show ap.fst.add bp.snd = ap.snd.add bp.fst

        have l1 (a1 a2 b1 b2 c1 c2 : ℕ) (h : c1.lt c2)
          (h' : ((a1.add b2).mul c1).add ((a2.add b1).mul c2) = ((a1.add b2).mul c2).add ((a2.add b1).mul c1))
          : a1.add b2 = a2.add b1 := by
            have ⟨x, hx⟩ := h.left
            rw [hx] at h'
            simp only [ℕ.add_mul, ℕ.mul_add] at h'
            ac_nf at h'
            rw [ℕ.add_comm (ℕ.mul b1 x) _] at h'
            repeat rw [ℕ.add_left_comm (ℕ.mul _ x) _ _] at h'
            simp only [ℕ.add_right_inj, ← ℕ.add_mul] at h'
            have hx0 : x ≠ ℕ.zero := fun h' => by rw [h', ℕ.add_zero] at hx;exact h.right hx.symm
            replace h' := (ℕ.mul_left_inj hx0).mp h'
            ac_nf at h' |-;symm;assumption

        rcases ℕ.lt_or_eq_or_gt cp.fst cp.snd with hl | hc_eq | hl
        case _ => exact l1 _ _ _ _ _ _ hl h
        case _ => exact (hc_neq hc_eq).elim
        case _ => exact l1 _ _ _ _ _ _ hl h.symm

    theorem mul_right_inj {a b c : ℤ} (hc : c ≠ zero) : c.mul a = c.mul b ↔ a = b := by
      simp only [c.mul_comm]
      exact mul_left_inj hc

    theorem mul_eq_zero {a b : ℤ} : a.mul b = zero → a = zero ∨ b = zero := by
      intro h
      by_cases ha0 : a = zero
      case pos => exact Or.inl ha0
      case neg =>
        rw [← a.mul_zero, mul_right_inj ha0] at h
        exact Or.inr h


  end mul

  section comp

    def le_fn_fn : ℕ_pair → ℕ_pair → Prop :=
      fun a b => (a.fst.add b.snd).le (a.snd.add b.fst)

    private theorem le_fn_respect (a : ℕ_pair) : ∀ (b b' : ℕ_pair), eqv b b' → le_fn_fn a b = le_fn_fn a b' := by
      intro ⟨b1, b2⟩ ⟨b1', b2'⟩ h'
      unfold eqv le_fn_fn ℕ.le at *
      simp only [] at *
      apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro ⟨x, h⟩
        refine ⟨x, ?_⟩
        replace h := (ℕ.add_left_inj b1').mpr h
        apply (ℕ.add_left_inj b1).mp
        rw [
          ℕ.add_right_comm, h,
          ℕ.add_right_comm _ _ b1,
          ℕ.add_right_comm _ _ b1,
          ℕ.add_assoc _ b1, h',
          ℕ.add_right_comm, ←ℕ.add_assoc
        ]
      case mpr =>
        intro ⟨x, h⟩
        refine ⟨x, ?_⟩
        replace h := (ℕ.add_left_inj b1).mpr h
        apply (ℕ.add_left_inj b1').mp
        rw [
          ℕ.add_right_comm, h,
          ℕ.add_right_comm _ _ b1,
          ℕ.add_right_comm _ _ b1,
          ℕ.add_assoc _ b1, h',
          ℕ.add_right_comm _ x, ←ℕ.add_assoc
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
          ℕ.add_right_comm, h,
          ℕ.add_right_comm _ b.fst,
        ]
      conv =>
        rhs
        pattern fun b => _
        intro b
        rw [
          ← ℕ.add_le_add_iff_right (c := a2),
          ℕ.add_comm _ a2, ℕ.add_comm _ a2,
          ← ℕ.add_assoc, ← ℕ.add_assoc,
        ]

    def le : ℤ → ℤ → Prop :=
      EC.lift eqv.eqv le_fn le_respect

    @[reducible] def ge (n m : ℤ) : Prop := le m n

    def lt : ℤ → ℤ → Prop :=
      fun n m => ¬ m.le n

    @[reducible] def gt (n m : ℤ) : Prop := lt m n

    @[reducible] def pos (n : ℤ) : Prop := lt zero n

    theorem le_of_lt {n m : ℤ} : n.lt m → n.le m := by
      intro h
      unfold lt le le_fn le_fn_fn at *
      let np := n.sys_of_repr
      let mp := m.sys_of_repr
      simp [EC.lift_spec n np n.sys_of_repr_spec, EC.lift_spec m mp m.sys_of_repr_spec] at *
      ac_nf at *
      exact ℕ.le_of_not_le h

    theorem ne_of_lt {n m : ℤ} : n.lt m → n ≠ m := by
      intro h hne
      replace hne := EC.sound_inv' n.sys_of_repr_spec m.sys_of_repr_spec hne
      unfold lt le le_fn le_fn_fn eqv at *
      simp [EC.lift_spec n _ n.sys_of_repr_spec, EC.lift_spec m _ m.sys_of_repr_spec] at *
      ac_nf at *
      exact h (ℕ.le_of_eq hne.symm)


  end comp


end ℤ
end my
