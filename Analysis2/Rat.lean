import Analysis2.Int
import Analysis2.CompStructure.OrderedField

noncomputable section
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing' Field
open Comp
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing OrderedCommRing' OrderedField
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
      have ha0 : a1 = zero := (mul_eq_zero h1).resolve_right (ne_of_lt hb).symm
      have hc0 : c1 = zero := (mul_eq_zero h2.symm).resolve_left (ne_of_lt hb).symm
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
    -- def two_repr : ℚ_con := ⟨ℤ.two, one, zero_lt_one⟩
    -- def two : ℚ := mk' two_repr
    -- theorem two_is_member_two : two.is_member two_repr := EC.is_member_of_from_elm _ eqv.eqv
    -- def three_repr : ℚ_con := ⟨ℤ.three, one, zero_lt_one⟩
    -- def three : ℚ := mk' three_repr
    -- theorem three_is_member_three : three.is_member three_repr := EC.is_member_of_from_elm _ eqv.eqv

    -- def neg_one_repr : ℚ_con := ⟨ℤ.neg_one, one, zero_lt_one⟩
    -- def neg_one : ℚ := mk' neg_one_repr
    -- theorem neg_one_is_member_neg_one : neg_one.is_member neg_one_repr := EC.is_member_of_from_elm _ eqv.eqv
    -- def neg_two_repr : ℚ_con := ⟨ℤ.neg_two, one, zero_lt_one⟩
    -- def neg_two : ℚ := mk' neg_two_repr
    -- theorem neg_two_is_member_neg_two : neg_two.is_member neg_two_repr := EC.is_member_of_from_elm _ eqv.eqv
    -- def neg_three_repr : ℚ_con := ⟨ℤ.neg_three, one, zero_lt_one⟩
    -- def neg_three : ℚ := mk' neg_three_repr
    -- theorem neg_three_is_member_neg_three : neg_three.is_member neg_three_repr := EC.is_member_of_from_elm _ eqv.eqv

  end nums

  section basic

    theorem num_eq_zero {a : ℤ} {h : zero < a} : EC.from_elm eqv.eqv ⟨zero, a, h⟩ = (zero : ℚ) := by
      apply EC.sound eqv.eqv _
      unfold eqv zero_repr
      simp only [zero_mul, mul_zero]

    theorem num_eq_zero' {a : ℚ_con} {S : ℚ} (h : S.is_member a) : a.fst = zero → S = zero := by
      intro h'
      apply EC.sound' eqv.eqv h zero_is_member_zero _
      unfold eqv zero_repr
      simp only [h', zero_mul, mul_zero]

    theorem num_eq_zero_of_eq_zero {a b : ℤ} {h : zero < b} : EC.from_elm eqv.eqv ⟨a, b, h⟩ = (zero : ℚ) → a = zero := by
      intro h'
      replace h' := EC.sound_inv eqv.eqv h'
      simp only [eqv, zero_repr, mul_one, mul_zero] at h'
      exact h'

    theorem num_eq_zero_of_eq_zero' {a : ℚ_con} {S : ℚ} (h : S.is_member a) : S = zero → a.fst = zero := by
      intro h'
      replace h' := EC.sound_inv' h zero_is_member_zero h'
      simp only [eqv, zero_repr, mul_one, mul_zero] at h'
      exact h'

  end basic

  section add

    def add_fn_fn_fn : ℚ_con → ℚ_con → ℚ_con :=
      fun a b => ⟨(a.fst * b.snd) + (a.snd * b.fst), a.snd * b.snd, mul_pos a.h b.h⟩

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

    private theorem _add_zero : ∀(n : ℚ), n + zero = n := by
      intro n
      let np := n.sys_of_repr
      repeat rw [add_def]
      unfold add add_fn
      rw [EquivalentClass.lift_spec n np n.sys_of_repr_spec]
      rw [EquivalentClass.lift_spec _ zero_repr zero_is_member_zero]
      unfold add_fn_fn add_fn_fn_fn zero_repr
      simp only [mul_zero, mul_one, add_zero]
      exact (EquivalentClass.from_sys_of_repr _).symm

    private theorem _add_comm : ∀(n m : ℚ), n + m = m + n := by
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


    private theorem _add_assoc : ∀ (a b c : ℚ), (a + b) + c = a + (b + c) := by
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

    def neg_fn_fn : ℚ_con → ℚ_con :=
      fun a => ⟨-a.fst, a.snd, a.h⟩

    def neg_fn : ℚ_con → ℚ :=
      fun a => ℚ.mk' (neg_fn_fn a)

    private theorem neg_respect : ∀(a b : ℚ_con), eqv a b → neg_fn a = neg_fn b := by
      intro ⟨b1, b2, h⟩ ⟨b1', b2', h'⟩ h''
      apply EC.sound
      unfold eqv neg_fn_fn at *
      simp only [mul_neg_left, mul_neg_right] at *
      congr

    def neg : ℚ → ℚ :=
      EC.lift eqv.eqv neg_fn neg_respect

    @[default_instance] instance : Neg ℚ where
      neg := neg

    theorem neg_def {a : ℚ} : -a = a.neg := rfl

    private theorem _add_neg : ∀(a : ℚ), a + -a = zero := by
      intro a
      repeat first | rw [add_def] | rw [neg_def]
      unfold add add_fn add_fn_fn neg neg_fn
      repeat first
      | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ (EC.is_member_of_from_elm _ eqv.eqv)]
      apply EC.sound
      unfold add_fn_fn_fn neg_fn_fn zero_repr eqv
      simp only [mul_zero, mul_one, mul_comm _ (-_ : ℤ), mul_neg_left, add_neg]


    @[default_instance] instance : CommGroup ℚ where
      add_neg := _add_neg

  end neg

  section mul

    def mul_fn_fn_fn : ℚ_con → ℚ_con → ℚ_con :=
      fun a b => ⟨a.fst * b.fst, a.snd * b.snd, mul_pos a.h b.h⟩

    def mul_fn_fn : ℚ_con → ℚ_con → ℚ :=
      fun a b => ℚ.mk' (mul_fn_fn_fn a b)

    private theorem mul_fn_respect (a : ℚ_con) : ∀ (b c : ℚ_con), eqv b c → mul_fn_fn a b = mul_fn_fn a c := by
      intro a b h''
      apply EC.sound
      unfold eqv mul_fn_fn_fn at *
      simp only [mul_assoc] at *
      rw [mul_left_comm a.fst, h'']
      ac_nf at *

    def mul_fn : ℚ_con → ℚ → ℚ :=
      fun a => EquivalentClass.lift (β := ℚ) eqv.eqv (mul_fn_fn a) (mul_fn_respect a)

    private theorem mul_respect : ∀ (a b : ℚ_con), eqv a b → mul_fn a = mul_fn b := by
      intro ⟨a1, a2, ha⟩ ⟨b1, b2, hb⟩ h
      funext Sc
      let c := Sc.sys_of_repr
      apply EC.sound
      unfold eqv mul_fn_fn_fn at *
      simp only [] at *
      rw [mul_right_comm, ←mul_assoc, h]
      ac_nf

    def mul : ℚ → ℚ → ℚ :=
      EquivalentClass.lift (β := ℚ → ℚ) eqv.eqv mul_fn mul_respect


    @[default_instance] instance : Mul ℚ where
      mul := mul

    theorem mul_def {a b : ℚ} : a * b = a.mul b := rfl

    private theorem _mul_one : ∀ (a : ℚ), a * one = a := by
      intro a
      repeat first | rw [mul_def]
      unfold mul mul_fn mul_fn_fn
      repeat first
      | rw [EC.lift_spec (one : ℚ) _ (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)]
      apply EC.sound' eqv.eqv (EC.is_member_of_from_elm _ eqv.eqv) a.sys_of_repr_spec _
      unfold mul_fn_fn_fn one_repr eqv
      simp only
      ac_nf

    private theorem _mul_assoc : ∀ (a b c : ℚ), a * b * c = a * (b * c) := by
      intro a b c
      repeat first | rw [mul_def]
      unfold mul mul_fn mul_fn_fn
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      repeat first
      | rw [EC.lift_spec a _ (EC.sys_of_repr_spec _)]
      | rw [EC.lift_spec b _ (EC.sys_of_repr_spec _)]
      | rw [EC.lift_spec c _ (EC.sys_of_repr_spec _)]
      | rw [EC.lift_spec _ (mul_fn_fn_fn ap bp) (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ (mul_fn_fn_fn bp cp)  (EC.is_member_of_from_elm _ eqv.eqv)]
      apply EC.sound
      unfold ap bp cp mul_fn_fn_fn eqv
      simp only
      ac_nf

    private theorem _add_mul : ∀ (a b c : ℚ), (a + b) * c = a * c + b * c := by
      intro a b c
      repeat first | rw [mul_def] | rw [add_def]
      unfold mul mul_fn mul_fn_fn add add_fn add_fn_fn
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      repeat first
      | rw [EC.lift_spec a _ (EC.sys_of_repr_spec _)]
      | rw [EC.lift_spec b _ (EC.sys_of_repr_spec _)]
      | rw [EC.lift_spec c _ (EC.sys_of_repr_spec _)]
      | rw [EC.lift_spec _ (add_fn_fn_fn ap bp) (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ (mul_fn_fn_fn ap cp) (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ (mul_fn_fn_fn bp cp)  (EC.is_member_of_from_elm _ eqv.eqv)]
      apply EC.sound
      unfold ap bp cp mul_fn_fn_fn add_fn_fn_fn eqv
      simp only [add_mul, mul_add]
      ac_nf

    private theorem _zero_ne_one : zero ≠ one := by
      intro h
      replace h := EC.sound_inv' zero_is_member_zero one_is_member_one h
      unfold eqv zero_repr one_repr at h
      simp [mul_one] at h
      exact zero_ne_one h

    private theorem _mul_comm : ∀ (a b : ℚ), a * b = b * a := by
      intro a b
      apply EC.sound
      unfold eqv mul_fn_fn_fn
      ac_nf

    @[default_instance] instance : CommRing ℚ where
      _mul_one := _mul_one
      _mul_assoc := _mul_assoc
      _add_mul := _add_mul
      _zero_ne_one := _zero_ne_one
      _mul_comm := _mul_comm


  end mul

  section inv

    def inv_fn_fn : (a : ℚ_con) → a.fst ≠ zero → ℚ_con :=
      fun a h => ((eq_or_lt_or_gt a.fst zero).resolve_left h).elim'
        (⟨-a.snd, -a.fst, neg_neg_is_pos ·⟩)
        (⟨a.snd, a.fst, ·⟩)
      --⟨-a.fst, a.snd, a.h⟩

    def inv_fn : (a : ℚ_con) → a.fst ≠ zero → ℚ :=
      fun a h => ℚ.mk' (inv_fn_fn a h)

    -- def inv : (Σ'(a : ℚ), a ≠ zero) → ℚ :=
    --   fun ah => inv_fn ⟨ah.fst.sys_of_repr, (fun h => ah.snd (num_eq_zero' ah.fst.sys_of_repr_spec h))⟩
    def inv' : (a : ℚ) → a ≠ zero → ℚ :=
      fun a h => inv_fn a.sys_of_repr (fun h' => h (num_eq_zero' a.sys_of_repr_spec h'))

    theorem inv_spec_eqv {S : ℚ} (a : ℚ_con) (h : S.is_member a) : (S ≠ zero) = (a.fst ≠ zero) :=
      congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h, num_eq_zero' h⟩)

    theorem inv_spec {S : ℚ} {h : S ≠ zero} {a : ℚ_con} (hm : S.is_member a) : inv' S h = inv_fn a ((inv_spec_eqv a hm).mp h) := by
      apply EC.sound
      unfold eqv inv_fn_fn
      let s := S.sys_of_repr
      have hs := fun h0 => h (num_eq_zero' S.sys_of_repr_spec h0)
      have ha := (inv_spec_eqv a hm).mp h
      have hos := (eq_or_lt_or_gt s.fst zero).resolve_left hs
      have hoa := (eq_or_lt_or_gt a.fst zero).resolve_left ha
      let elm1 := (hos.elim' (c := ℚ_con)
        (fun x => ⟨ -s.snd, -s.fst, neg_neg_is_pos x ⟩)
        (fun x => ⟨ s.snd, s.fst, x ⟩))
      let elm2 := (hoa.elim' (c := ℚ_con)
          (fun x => ⟨ -a.snd, -a.fst, neg_neg_is_pos x ⟩)
          (fun x => ⟨ a.snd, a.fst, x ⟩))
      have heqv := S.member_related a s ⟨hm, S.sys_of_repr_spec⟩
      unfold eqv at heqv; ac_nf at heqv
      show elm1.fst * elm2.snd = elm1.snd * elm2.fst
      apply Or.elim'_spec (c := ℚ_con) (p := (fun m => m.fst * elm2.snd = m.snd * elm2.fst))
      <;>intro cs<;>simp only
      <;>apply Or.elim'_spec (c := ℚ_con) (p := (fun m => _ * m.snd = _ * m.fst))
      <;>intro ca<;>simp only [mul_neg_left, mul_neg_right]
      <;>ac_nf<;>rw[heqv]

    theorem inv_spec2 {S : ℚ} {a : ℚ_con} {h : a.fst ≠ zero} (hm : S.is_member a) : inv' S ((inv_spec_eqv a hm).mpr h) = inv_fn a h := inv_spec hm

      -- show (hos.elim' (c := ℚ_con)
      --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ (s).snd, (s).fst, x ⟩) ).fst *
      --   (hoa.elim' (c := ℚ_con)
      --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ a.snd, a.fst, x ⟩)).snd =
      --   (hos.elim' (c := ℚ_con)
      --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ (s).snd, (s).fst, x ⟩)).snd *
      --   (hoa.elim' (c := ℚ_con)
      --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ a.snd, a.fst, x ⟩)).fst
      -- #check Or.elim'_spec


      -- show (hos.elim' (c := ℚ_con)
      --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ (s).snd, (s).fst, x ⟩) ).fst *
      --   (hoa.elim' (c := ℚ_con)
      --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ a.snd, a.fst, x ⟩)).snd =
      --   (hos.elim' (c := ℚ_con)
      --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ (s).snd, (s).fst, x ⟩)).snd *
      --   (hoa.elim' (c := ℚ_con)
      --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
      --     (fun x => ⟨ a.snd, a.fst, x ⟩)).fst


    -- theorem inv_spec' (S : ℚ) {h : S ≠ zero} : ∀(a : ℚ_con), S.is_member a → inv' S ≍ inv_fn a := sorry

      -- -- theorem inv_spec' {h : ∀ (a b : α), R a b → f a = f b} (S : EquivalentClass R) : ∀(a : α), is_member a S → inv' S = f a :=
      -- set_option pp.proofs true in
      -- theorem inv_spec' (S : ℚ) {h : S ≠ zero} : ∀(a : ℚ_con), S.is_member a → inv' S ≍ inv_fn a := by
      --   intro a h'
      --   have feq : (S ≠ zero) = (a.fst ≠ zero) := congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
      --   -- have feq (S : ℚ) (a : ℚ_con) (h' : S.is_member a) : (S ≠ zero) = (a.fst ≠ zero) := congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
      --   apply heq_of_eqRec_eq
      --   case h₁ =>
      --     -- congr 1
      --     refine' implies_congr feq rfl
      --     -- refine' implies_congr (feq S a h') rfl
      --   case h₂ =>
      --     funext h''
      --     apply EC.sound' eqv.eqv _ (EC.is_member_of_from_elm _ eqv.eqv) _
      --     -- unfold inv_fn
      --     exact inv_fn_fn S.sys_of_repr (fun h0 => h (num_eq_zero' S.sys_of_repr_spec h0))
      --     -- apply EC.is_member_of_from_elm
      --     -- guard_expr (implies_congr feq rfl ▸ S.inv') =~ S.inv'
      --     -- guard_expr ((implies_congr feq rfl) ▸ S.inv') =~ rfl ▸ (fun x => S.inv' (feq ▸ x))
      --     -- simp?
      --     unfold implies_congr rfl
      --     guard_target =~ EquivalentClass.is_member (inv_fn_fn (EquivalentClass.sys_of_repr S) fun h0 => h (num_eq_zero' (EquivalentClass.sys_of_repr_spec S) h0))
      --       -- ((fun he => S.inv' (feq.mpr he)) h'')
      --       ((((sorry):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')

      --     have h4 : (((feq ▸ Eq.refl (S ≠ zero → ℚ)) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') = S.inv' := by
      --       -- simp only []
      --       unfold Eq.symm
      --       generalize ((((feq ▸ Eq.refl (S ≠ zero → ℚ)): (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ rfl) : (a.fst ≠ zero → ℚ) = (S ≠ zero → ℚ)) = x
      --       generalize ((x ▸ rfl) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) = y
      --       have h1 : y ▸ S.inv' ≍ S.inv' := cast_heq _ _
      --       have h2 : x ▸ y ▸ S.inv' ≍ y ▸ S.inv' := cast_heq _ _
      --       have h3 : x ▸ y ▸ S.inv' ≍ S.inv' := HEq.trans h2 h1
      --       exact eq_of_heq h3
      --     -- have h4 : (((feq ▸ Eq.refl (S ≠ zero → ℚ)) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') = S.inv' := by
      --     --   -- simp only []
      --     --   unfold Eq.symm
      --     --   generalize ((((feq ▸ Eq.refl (S ≠ zero → ℚ)): (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ rfl) : (a.fst ≠ zero → ℚ) = (S ≠ zero → ℚ)) = x
      --     --   generalize ((x ▸ rfl) : (S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) = y
      --     --   have h1 : y ▸ S.inv' ≍ S.inv' := cast_heq _ _
      --     --   have h2 : x ▸ y ▸ S.inv' ≍ y ▸ S.inv' := cast_heq _ _
      --     --   have h3 : x ▸ y ▸ S.inv' ≍ S.inv' := HEq.trans h2 h1
      --     --   exact eq_of_heq h3


      --       -- ((((sorry):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')
      --       -- ((((feq ▸ Eq.refl (S ≠ zero → ℚ)):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')
      --       -- ((((feq ▸ Eq.refl (S ≠ zero → ℚ)):(S ≠ zero → ℚ) = (a.fst ≠ zero → ℚ)) ▸ S.inv') h'')
      --     -- guard_expr (feq ▸ Eq.refl ℚ ▸ Eq.refl (S ≠ zero → ℚ)) =~ (feq ▸ Eq.refl ℚ ▸ Eq.refl (S ≠ zero → ℚ))
      --     -- exact inv_fn S.sys_of_repr (feq.mpr h'')
      --     -- exact inv_fn S.sys_of_repr (fun h' => h'' (num_eq_zero' S.sys_of_repr_spec h'))
      --     simp?

      --   -- intro a h'
      --   -- apply heq_of_eqRec_eq
      --   -- have feq : (S ≠ zero) = (a.fst ≠ zero) := sorry
      --   -- case h₁ =>
      --   --   -- congr 1
      --   --   refine' implies_congr _ rfl
      --   --   apply congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
      --   -- case h₂ =>
      --   --   funext h''
      --   --   apply EC.sound' eqv.eqv _ (EC.is_member_of_from_elm _ eqv.eqv) _
      --   --   -- unfold inv_fn
      --   --   exact inv_fn S.sys_of_repr h''
      --   --   -- exact inv_fn S.sys_of_repr (fun h' => h'' (num_eq_zero' S.sys_of_repr_spec h'))
      --   --   simp?


      --   -- refine @heq_of_eq _


    def inv : (Σ'(a : ℚ), a ≠ zero) → ℚ :=
      fun a => a.fst.inv' a.snd
      -- fun ah => inv_fn ⟨ah.fst.sys_of_repr, (by
      --   intro h
      --   let a := ah.fst.sys_of_repr
      --   have h' := num_eq_zero' ah.fst.sys_of_repr_spec h
      --   have := ah.snd h'
      --   -- have h' := EC.sound' (a := a) eqv.eqv (EC.sys_of_repr_spec _) zero_is_member_zero
      --   -- unfold eqv zero_repr at h'
      --   -- simp only [mul_one, mul_zero] at h'
      --   -- replace h' := h' h
      --   -- have := num_eq_zero_of_eq_zero' ah.fst.sys_of_repr_spec h'
      --   -- have := num_eq_zero' ah.fst.sys_of_repr_spec h'
      --   -- have := EC.sound_inv eqv.eqv h
      --   sorry
      -- )⟩

    @[default_instance] instance : Inv ℚ where
      inv := inv

    theorem inv_def {a : ℚ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = inv ⟨a, h⟩ := rfl

    -- the more useful one :
    theorem inv_def' {a : ℚ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = a.inv' h := rfl

    private theorem _mul_inv_cancel : ∀ (a : ℚ) (h0 : a ≠ zero), a * ⟨a, h0⟩⁻¹ = one := by
      intro a h0
      rw [mul_def, inv_def', inv_spec a.sys_of_repr_spec]
      unfold mul mul_fn mul_fn_fn inv_fn
      rw [EC.lift_spec a _ a.sys_of_repr_spec,
        EC.lift_spec _ _ (EC.is_member_of_from_elm _ _)]
      apply EC.sound
      unfold mul_fn_fn_fn inv_fn_fn one_repr eqv
      simp only [mul_one]
      let ap := a.sys_of_repr
      apply Or.elim'_spec (c := ℚ_con) (p := (fun x => (ap.fst * x.fst = ap.snd * x.snd))) _ _
      <;>simp only [mul_neg_right]<;>intro<;>ac_nf

    @[default_instance] instance : Field ℚ where
      mul_inv_cancel := _mul_inv_cancel

  end inv

  section comp


    def le_fn_fn : ℚ_con → ℚ_con → Prop :=
      fun a b => a.fst * b.snd ≤ a.snd * b.fst

    private theorem le_fn_respect (a : ℚ_con) : ∀ (b c : ℚ_con), eqv b c → le_fn_fn a b = le_fn_fn a c := by
      intro b c h
      have h' {a b c : ℚ_con} : eqv b c → le_fn_fn a b → le_fn_fn a c := by
        unfold eqv le_fn_fn
        intro h h'
        rw [←mul_le_mul_pos_right_iff c.h, mul_assoc a.snd, h] at h'
        rw [←mul_le_mul_pos_right_iff b.h]
        ac_nf at *
      exact propext ⟨h' h, h' h.symm⟩

    def le_fn : ℚ_con → ℚ → Prop :=
      fun a => EquivalentClass.lift eqv.eqv (le_fn_fn a) (le_fn_respect a)

    private theorem le_respect : ∀ (a b : ℚ_con), eqv a b → le_fn a = le_fn b := by
      intro a b h
      funext c
      have h' {a b : ℚ_con} {c : ℚ} : eqv a b → le_fn a c → le_fn b c := by
        intro h h'
        unfold eqv le_fn at *
        repeat rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)] at *
        unfold le_fn_fn at *
        rw [←mul_le_mul_pos_left_iff a.h, ←mul_assoc, ← h]
        rw [←mul_le_mul_pos_left_iff b.h] at h'
        ac_nf at |- h'
      exact propext ⟨h' h, h' h.symm⟩

    def le : ℚ → ℚ → Prop :=
      EquivalentClass.lift (β := ℚ → Prop) eqv.eqv le_fn le_respect

    private theorem _le_refl : ∀ (a : ℚ), a.le a := by
      intro a
      unfold le le_fn le_fn_fn EC.lift
      simp only [mul_comm]
      exact le_refl _

    private theorem _le_trans : ∀ (a b c : ℚ), a.le b → b.le c → a.le c := by
      intro a b c
      unfold le le_fn le_fn_fn EC.lift
      simp only
      generalize a.sys_of_repr = a
      generalize b.sys_of_repr = b
      generalize c.sys_of_repr = c
      intro h h'
      rw [←mul_le_mul_pos_right_iff b.h]
      rw [←mul_le_mul_pos_right_iff c.h] at h
      rw [←mul_le_mul_pos_right_iff a.h] at h'
      ac_nf at *
      exact le_trans _ _ _ h h'

    private theorem _le_antisymm : ∀ (a b : ℚ), a.le b → b.le a → a = b := by
      intro a b
      unfold le le_fn le_fn_fn EC.lift
      intro h h'
      apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
      simp only [eqv] at *
      ac_nf at *
      exact le_antisymm _ _ h h'

    private theorem _le_total : ∀ (a b : ℚ), a.le b ∨ b.le a := by
      intro a b
      unfold le le_fn le_fn_fn EC.lift
      simp only
      generalize a.sys_of_repr = a
      generalize b.sys_of_repr = b
      ac_nf
      exact le_total _ _

    @[default_instance] instance : Comp ℚ where
      le := le
      le_refl := _le_refl
      le_trans := _le_trans
      le_antisymm := _le_antisymm
      le_total := _le_total

    theorem le_def {a b : ℚ} : (a ≤ b) = a.le b := rfl

    private theorem _add_le_add_left {a b : ℚ} : ∀(c : ℚ), a ≤ b → c + a ≤ c + b := by
      intro c
      simp only [le_def, add_def]
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      unfold le le_fn le_fn_fn add add_fn add_fn_fn
      intro h
      replace h : ap.fst * bp.snd ≤ ap.snd * bp.fst := h
      repeat first
      | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ b.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ c.sys_of_repr_spec]
      | rw [EC.lift_spec _ (add_fn_fn_fn cp ap) (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ (add_fn_fn_fn cp bp) (EC.is_member_of_from_elm _ eqv.eqv)]
      unfold add_fn_fn_fn
      simp only [mul_add, add_mul]
      ac_nf
      simp only [add_le_add_right_iff, ←mul_assoc, mul_le_mul_pos_right_iff cp.h]
      ac_nf at h |-

    @[default_instance] instance : OrderedCommMonoid ℚ where
      _add_le_add_left := _add_le_add_left

    @[default_instance] instance : OrderedCommGroup ℚ where

    private theorem _mul_nonneg {a b : ℚ} : zero ≤ a → zero ≤ b → zero ≤ a * b := by
      simp [le_def, mul_def]
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      unfold le le_fn mul mul_fn mul_fn_fn
      repeat first
      | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ b.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ zero_is_member_zero]
      | rw [EC.lift_spec _ (mul_fn_fn_fn ap bp) (EC.is_member_of_from_elm _ eqv.eqv)]
      unfold le_fn_fn mul_fn_fn_fn zero_repr
      simp only [zero_mul, one_mul]
      exact mul_nonneg

    private theorem _zero_le_one : zero ≤ one := by
      rw [le_def]
      unfold le le_fn le_fn_fn
      rw [EC.lift_spec _ _ zero_is_member_zero]
      rw [EC.lift_spec _ _ one_is_member_one]
      unfold zero_repr one_repr
      simp only [mul_one]
      exact zero_le_one


    @[default_instance] instance : OrderedCommRing ℚ where
      _mul_nonneg := _mul_nonneg
      _zero_le_one := _zero_le_one

    -- private theorem _mul_eq_zero {a b : ℚ} : a * b = zero → a = zero ∨ b = zero := by
    --   rw [mul_def]
    --   unfold mul mul_fn mul_fn_fn EC.lift mul_fn_fn_fn
    --   intro h
    --   replace h := EC.sound_inv eqv.eqv h
    --   unfold eqv zero_repr at h
    --   simp only [mul_zero, mul_one] at h
    --   exact (mul_eq_zero h).elim
    --     (fun h' => Or.inl (num_eq_zero' a.sys_of_repr_spec h'))
    --     (fun h' => Or.inr (num_eq_zero' b.sys_of_repr_spec h'))

    -- @[default_instance] instance : OrderedCommRing' ℚ where
    --   mul_eq_zero := _mul_eq_zero

    @[default_instance] instance : OrderedField ℚ where

  end comp

  section num
    namespace num

      def two := one + one
      theorem two_pos : zero < two := pos_add_pos_is_pos zero_lt_one zero_lt_one
      theorem two_nonzero : two ≠ zero := ne_of_gt two_pos

      theorem mul_two (a : ℚ) : a * two = a + a := by
        unfold two;simp only [mul_add,mul_one]

      def one_half := ⟨two, two_nonzero⟩⁻¹
      theorem one_half_pos : zero < one_half := inv_pos_is_pos two_pos
      theorem one_half_nonzero : one_half ≠ zero := ne_of_gt one_half_pos
      theorem add_half : one_half + one_half = one := by
        rw [←mul_two];unfold one_half;rw[inv_mul_cancel];

    end num

  end num

end ℚ

end my
