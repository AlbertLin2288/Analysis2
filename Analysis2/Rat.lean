import Analysis2.Operator
import Analysis2.Comp
import Analysis2.Structure
import Analysis2.CompStructure
import Analysis2.EquivalentClass
import Analysis2.Nat
import Analysis2.Int

noncomputable section
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommGroup
open Comp
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommGroup
open Zero One

open my renaming EquivalentClass → EC


structure ℤ_pair where
  fst : ℤ
  snd : ℤ

structure ℚ_con where
  fst : ℤ
  snd : ℤ
  h : snd > zero


def ℚ.eqv : ℚ_con → ℚ_con → Prop :=
  fun a b => a.fst * b.snd = a.snd * b.fst

namespace ℚ.eqv

  theorem refl : ∀ (a : ℚ_con), ℚ.eqv a a :=
    fun ⟨a1, a2, _⟩ => mul_comm a1 a2

  theorem symm : ∀ {a b : ℚ_con}, ℚ.eqv a b → ℚ.eqv b a := by
    unfold eqv
    intro ⟨a1, a2, _⟩ ⟨b1, b2, _⟩ h
    simp only [mul_comm a1, mul_comm a2] at *
    exact h.symm

  theorem trans : ∀ {a b c : ℚ_con}, ℚ.eqv a b → ℚ.eqv b c → ℚ.eqv a c := by
    unfold eqv
    intro ⟨a1, a2, _⟩ ⟨b1, b2, hb⟩ ⟨c1, c2, hc⟩ h1 h2
    simp only [] at *
    by_cases hb0 : b1 = zero
    case pos =>
      simp only [hb0, mul_zero, zero_mul] at h1 h2
      have ha0 : a1 = zero := (ℤ.mul_eq_zero h1).resolve_right (ne_of_lt hb).symm
      have hc0 : c1 = zero := (ℤ.mul_eq_zero h2.symm).resolve_left (ne_of_lt hb).symm
      rw [ha0, hc0, mul_zero, zero_mul]
    case neg =>
      replace h1 := congrArg (· * c1) h1--(ℤ.mul_left_inj (b2.mul c1)).mpr h1
      simp only [mul_assoc, ←h2] at h1
      replace h1 := congrArg (· * c2) h1--(ℤ.mul_left_inj (b2.mul c1)).mpr h1
      simp only [ℤ.mul_left_inj (ne_of_lt hc).symm] at h1
      simp only [mul_left_comm _ b1, ℤ.mul_right_inj hb0] at h1
      exact h1

  def eqv : Equivalence ℚ.eqv where
    refl := refl
    symm := symm
    trans := trans

end ℚ.eqv

def ℚ := EquivalentClass ℚ.eqv

namespace ℚ

  abbrev mk' (a : ℚ_con) := EquivalentClass.from_elm eqv.eqv a

  section nums

    def zero_repr : ℚ_con := ⟨zero, one, zero_lt_one⟩
    def _zero : ℚ := mk' zero_repr
    @[default_instance] instance : Zero ℚ := ⟨_zero⟩
    theorem zero_is_member_zero : zero.is_member zero_repr := EC.is_member_of_from_elm _ eqv.eqv


    def one_repr : ℚ_con := ⟨one, one, zero_lt_one⟩
    def _one : ℚ := mk' one_repr
    @[default_instance] instance : One ℚ := ⟨_one⟩
    theorem one_is_member_one : one.is_member one_repr := EC.is_member_of_from_elm _ eqv.eqv
    def two_repr : ℚ_con := ⟨ℤ.two, one, zero_lt_one⟩
    def two : ℚ := mk' two_repr
    theorem two_is_member_two : two.is_member two_repr := EC.is_member_of_from_elm _ eqv.eqv
    def three_repr : ℚ_con := ⟨ℤ.three, one, zero_lt_one⟩
    def three : ℚ := mk' three_repr
    theorem three_is_member_three : three.is_member three_repr := EC.is_member_of_from_elm _ eqv.eqv

    def neg_one_repr : ℚ_con := ⟨ℤ.neg_one, one, zero_lt_one⟩
    def neg_one : ℚ := mk' neg_one_repr
    theorem neg_one_is_member_neg_one : neg_one.is_member neg_one_repr := EC.is_member_of_from_elm _ eqv.eqv
    def neg_two_repr : ℚ_con := ⟨ℤ.neg_two, one, zero_lt_one⟩
    def neg_two : ℚ := mk' neg_two_repr
    theorem neg_two_is_member_neg_two : neg_two.is_member neg_two_repr := EC.is_member_of_from_elm _ eqv.eqv
    def neg_three_repr : ℚ_con := ⟨ℤ.neg_three, one, zero_lt_one⟩
    def neg_three : ℚ := mk' neg_three_repr
    theorem neg_three_is_member_neg_three : neg_three.is_member neg_three_repr := EC.is_member_of_from_elm _ eqv.eqv

  end nums


  section add

    def add_fn_fn_fn : ℚ_con → ℚ_con → ℚ_con :=
      fun a b => ⟨(a.fst * b.snd) + (a.snd * b.fst), a.snd * b.snd, (by
        sorry
        )⟩

    def add_fn_fn : ℚ_con → ℚ_con → ℚ :=
      fun a b => ℚ.mk' (add_fn_fn_fn a b)

    private theorem add_fn_respect (a : ℚ_con) : ∀ (b c : ℚ_con), eqv b c → add_fn_fn a b = add_fn_fn a c := by
      intro ⟨b1, b2, h⟩ ⟨b1', b2', h'⟩ h''
      apply EquivalentClass.sound
      unfold eqv add_fn_fn_fn at *
      simp only [mul_add,add_mul]
      ac_nf
      simp [←mul_assoc]
      congr 3

    def add_fn : ℚ_con → ℚ → ℚ :=
      fun a => EquivalentClass.lift (β := ℚ) eqv.eqv (add_fn_fn a) (add_fn_respect a)

    private theorem add_respect : ∀ (a b : ℚ_con), eqv a b → add_fn a = add_fn b := by
      intro ⟨a1, a2, ha⟩ ⟨b1, b2, hb⟩ h
      funext Sc
      let c := Sc.sys_of_repr
      apply EquivalentClass.sound
      unfold eqv add_fn_fn_fn at *
      simp only [mul_add,add_mul]
      ac_nf
      simp only [←mul_assoc]
      congr

    def add : ℚ → ℚ → ℚ :=
      EquivalentClass.lift (β := ℚ → ℚ) eqv.eqv add_fn add_respect

    @[default_instance] instance : Add ℚ := ⟨add⟩

    theorem add_def {a b : ℚ} : a + b = a.add b := rfl

    theorem _add_zero : ∀(n : ℚ), n + zero = n := by
      intro n
      let np := n.sys_of_repr
      repeat rw [add_def]
      unfold add add_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ zero_repr zero_is_member_zero]
      unfold add_fn_fn add_fn_fn_fn zero_repr
      simp only [mul_zero, mul_one, add_zero]
      exact (EquivalentClass.from_sys_of_repr _).symm

    theorem _add_comm : ∀(n m : ℚ), n + m = m + n := by
      intro n m
      let np := n.sys_of_repr
      let mp := m.sys_of_repr
      repeat rw [add_def]
      unfold add add_fn
      simp only [
        EC.lift_spec n np n.sys_of_repr_spec,
        EC.lift_spec m mp m.sys_of_repr_spec]
      unfold add_fn_fn add_fn_fn_fn
      ac_nf


    theorem _add_assoc : ∀ (a b c : ℚ), (a + b) + c = a + (b + c) := by
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
      repeat first
      | rw [EC.lift_spec _ ap a.sys_of_repr_spec]
      | rw [EC.lift_spec _ bp b.sys_of_repr_spec]
      | rw [EC.lift_spec _ cp c.sys_of_repr_spec]
      | rw [EC.lift_spec _ abp (EquivalentClass.is_member_of_from_elm abp _)]
      | rw [EC.lift_spec _ bcp (EquivalentClass.is_member_of_from_elm bcp _)]
      unfold abp bcp add_fn_fn_fn
      simp [add_mul, mul_add]
      ac_nf

    @[default_instance] instance : CommMonoid ℚ where
      _add_zero := _add_zero
      _add_assoc := _add_assoc
      add_comm := _add_comm

  end add

  section neg

  end neg


end ℚ

end my
