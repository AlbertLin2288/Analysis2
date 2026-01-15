import Analysis2.Rat
import Analysis2.Seq

noncomputable section
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing' Field
open Comp
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing OrderedCommRing'
open Zero One
open Seq

open my renaming EquivalentClass → EC


structure ℚ_cauchy where
  s : Seq ℚ
  h : is_cauchy s


def ℝ.eqv : ℚ_cauchy → ℚ_cauchy → Prop :=
  fun a b => conv_to (a.s - b.s) zero

namespace ℝ.eqv

  theorem refl : ∀ (a : ℚ_cauchy), ℝ.eqv a a :=
    fun a => (add_neg a.s).substr (p:=(conv_to · zero)) (conv_to_of_const zero)

  theorem symm : ∀ {a b : ℚ_cauchy}, ℝ.eqv a b → ℝ.eqv b a := by
    unfold eqv
    intro a b h
    rw [←neg_neg b.s, ←neg_sum, ←neg_zero, add_comm]
    exact conv_to_neg_of_neg h

  theorem trans : ∀ {a b c : ℚ_cauchy}, ℝ.eqv a b → ℝ.eqv b c → ℝ.eqv a c := by
    intro a b c h h'
    unfold eqv
    replace h := (conv_to_sum_of_sum h h')
    rw [←add_assoc, sub_add_cancel, add_zero] at h
    exact h

  def eqv : Equivalence ℝ.eqv where
    refl := refl
    symm := symm
    trans := trans

end ℝ.eqv

def ℝ := EquivalentClass ℝ.eqv

namespace ℝ

  abbrev mk' (a : ℚ_cauchy) := EquivalentClass.from_elm eqv.eqv a

  section nums

    def zero_repr : ℚ_cauchy := ⟨zero, is_cauchy_of_const zero⟩
    def _zero : ℝ := mk' zero_repr
    @[default_instance] instance : Zero ℝ := ⟨_zero⟩
    theorem zero_is_member_zero : zero.is_member zero_repr := EC.is_member_of_from_elm _ eqv.eqv


    def one_repr : ℚ_cauchy := ⟨one, is_cauchy_of_const one⟩
    def _one : ℝ := mk' one_repr
    @[default_instance] instance : One ℝ := ⟨_one⟩
    theorem one_is_member_one : one.is_member one_repr := EC.is_member_of_from_elm _ eqv.eqv

    -- def two : ℝ := one + one

    -- def two_repr : ℚ_cauchy := ⟨const_seq ℚ.two, cauchy_of_const _⟩
    -- def two : ℝ := mk' two_repr
    -- theorem two_is_member_two : two.is_member two_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def three_repr : ℚ_cauchy := ⟨const_seq ℚ.three, cauchy_of_const _⟩
--     def three : ℝ := mk' three_repr
--     theorem three_is_member_three : three.is_member three_repr := EC.is_member_of_from_elm _ eqv.eqv

--     def neg_one_repr : ℚ_cauchy := ⟨ℤ.neg_one, one, zero_lt_one⟩
--     def neg_one : ℝ := mk' neg_one_repr
--     theorem neg_one_is_member_neg_one : neg_one.is_member neg_one_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def neg_two_repr : ℚ_cauchy := ⟨ℤ.neg_two, one, zero_lt_one⟩
--     def neg_two : ℝ := mk' neg_two_repr
--     theorem neg_two_is_member_neg_two : neg_two.is_member neg_two_repr := EC.is_member_of_from_elm _ eqv.eqv
--     def neg_three_repr : ℚ_cauchy := ⟨ℤ.neg_three, one, zero_lt_one⟩
--     def neg_three : ℝ := mk' neg_three_repr
--     theorem neg_three_is_member_neg_three : neg_three.is_member neg_three_repr := EC.is_member_of_from_elm _ eqv.eqv

  end nums

  section basic

  end basic

  section add

    def add_fn_fn_fn : ℚ_cauchy → ℚ_cauchy → ℚ_cauchy :=
      fun a b => ⟨a.s + b.s, is_cauchy_of_sum a.h b.h⟩

    def add_fn_fn : ℚ_cauchy → ℚ_cauchy → ℝ :=
      fun a b => ℝ.mk' (add_fn_fn_fn a b)

    private theorem add_fn_respect (a : ℚ_cauchy) : ∀ (b c : ℚ_cauchy), eqv b c → add_fn_fn a b = add_fn_fn a c := by
      intros
      apply EquivalentClass.sound
      unfold eqv add_fn_fn_fn
      simpa only [neg_sum,←add_assoc,add_right_comm _ _ (-a.s),add_neg,zero_add,]

    def add_fn : ℚ_cauchy → ℝ → ℝ :=
      fun a => EquivalentClass.lift (β := ℝ) eqv.eqv (add_fn_fn a) (add_fn_respect a)

    private theorem add_respect : ∀ (a b : ℚ_cauchy), eqv a b → add_fn a = add_fn b := by
      intro _ ⟨b, _⟩ h
      funext
      apply EC.sound
      unfold eqv add_fn_fn_fn at *
      simp at *
      rwa [neg_sum, add_assoc, add_left_comm _ (-b),add_neg,add_zero]

    def add : ℝ → ℝ → ℝ :=
      EquivalentClass.lift (β := ℝ → ℝ) eqv.eqv add_fn add_respect

    @[default_instance] instance : Add ℝ := ⟨add⟩

    theorem add_def {a b : ℝ} : a + b = a.add b := rfl

    private theorem _add_zero : ∀(n : ℝ), n + zero = n := by
      intro n
      let np := n.sys_of_repr
      repeat rw [add_def]
      unfold add add_fn
      rw [EC.lift_spec n np n.sys_of_repr_spec]
      rw [EC.lift_spec _ zero_repr zero_is_member_zero]
      unfold add_fn_fn add_fn_fn_fn zero_repr
      simp only [add_zero]
      exact (n.from_sys_of_repr).symm

    private theorem _add_comm : ∀(n m : ℝ), n + m = m + n := by
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

    private theorem _add_assoc : ∀ (a b c : ℝ), (a + b) + c = a + (b + c) := by
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
      simp only
      ac_nf

    @[default_instance] instance : CommMonoid ℝ where
      _add_zero := _add_zero
      _add_assoc := _add_assoc
      add_comm := _add_comm

  end add

  section neg

    def neg_fn_fn : ℚ_cauchy → ℚ_cauchy :=
      fun a => ⟨-a.s, is_cauchy_of_neg a.h⟩

    def neg_fn : ℚ_cauchy → ℝ :=
      fun a => ℝ.mk' (neg_fn_fn a)

    private theorem neg_respect : ∀(a b : ℚ_cauchy), eqv a b → neg_fn a = neg_fn b :=
      fun ⟨b, _⟩ ⟨b', _⟩ h => EC.sound eqv.eqv (@id (conv_to (-b + - -b') zero) (neg_sum b (-b') ▸ neg_zero (α := ℚ) ▸ conv_to_neg_of_neg h))

    def neg : ℝ → ℝ :=
      EC.lift eqv.eqv neg_fn neg_respect

    @[default_instance] instance : Neg ℝ where
      neg := neg

    theorem neg_def {a : ℝ} : -a = a.neg := rfl

    private theorem _add_neg : ∀(a : ℝ), a + -a = zero := by
      intro a
      repeat first | rw [add_def] | rw [neg_def]
      unfold add add_fn add_fn_fn neg neg_fn
      repeat first
      | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ (EC.is_member_of_from_elm _ eqv.eqv)]
      apply EC.sound
      unfold add_fn_fn_fn eqv neg_fn_fn zero_repr
      simp only [add_neg]
      exact conv_to_of_const zero

    @[default_instance] instance : CommGroup ℝ where
      add_neg := _add_neg

  end neg

  section mul

    -- def mul_fn_fn_fn : ℚ_cauchy → ℚ_cauchy → ℚ_cauchy :=
    --   fun a b => ⟨a.s * b.s, is_cauchy_of_mul a.h b.h⟩

    -- def mul_fn_fn : ℚ_cauchy → ℚ_cauchy → ℝ :=
    --   fun a b => ℝ.mk' (mul_fn_fn_fn a b)

    -- private theorem mul_fn_respect (a : ℚ_cauchy) : ∀ (b c : ℚ_cauchy), eqv b c → mul_fn_fn a b = mul_fn_fn a c := by
    --   intro a b h''
    --   apply EC.sound
    --   unfold eqv mul_fn_fn_fn at *
    --   simp only [mul_assoc] at *
    --   rw [mul_left_comm a.fst, h'']
    --   ac_nf at *

--     def mul_fn : ℚ_cauchy → ℝ → ℝ :=
--       fun a => EquivalentClass.lift (β := ℝ) eqv.eqv (mul_fn_fn a) (mul_fn_respect a)

--     private theorem mul_respect : ∀ (a b : ℚ_cauchy), eqv a b → mul_fn a = mul_fn b := by
--       intro ⟨a1, a2, ha⟩ ⟨b1, b2, hb⟩ h
--       funext Sc
--       let c := Sc.sys_of_repr
--       apply EC.sound
--       unfold eqv mul_fn_fn_fn at *
--       simp only [] at *
--       rw [mul_right_comm, ←mul_assoc, h]
--       ac_nf

--     def mul : ℝ → ℝ → ℝ :=
--       EquivalentClass.lift (β := ℝ → ℝ) eqv.eqv mul_fn mul_respect


--     @[default_instance] instance : Mul ℝ where
--       mul := mul

--     theorem mul_def {a b : ℝ} : a * b = a.mul b := rfl

--     private theorem _mul_one : ∀ (a : ℝ), a * one = a := by
--       intro a
--       repeat first | rw [mul_def]
--       unfold mul mul_fn mul_fn_fn
--       repeat first
--       | rw [EC.lift_spec (one : ℝ) _ (EC.is_member_of_from_elm _ eqv.eqv)]
--       | rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)]
--       apply EC.sound' eqv.eqv (EC.is_member_of_from_elm _ eqv.eqv) a.sys_of_repr_spec _
--       unfold mul_fn_fn_fn one_repr eqv
--       simp only
--       ac_nf

--     private theorem _mul_assoc : ∀ (a b c : ℝ), a * b * c = a * (b * c) := by
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

--     private theorem _add_mul : ∀ (a b c : ℝ), (a + b) * c = a * c + b * c := by
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

--     private theorem _mul_comm : ∀ (a b : ℝ), a * b = b * a := by
--       intro a b
--       apply EC.sound
--       unfold eqv mul_fn_fn_fn
--       ac_nf

--     @[default_instance] instance : CommRing ℝ where
--       _mul_one := _mul_one
--       _mul_assoc := _mul_assoc
--       _add_mul := _add_mul
--       _zero_ne_one := _zero_ne_one
--       _mul_comm := _mul_comm


  end mul

--   section inv

--     -- def inv_fn_fn : (Σ'(a : ℚ_cauchy), a.fst ≠ zero) → ℚ_cauchy :=
--     --   fun ah => ((eq_or_lt_or_gt ah.fst.fst zero).resolve_left ah.snd).elim'
--     --     (⟨ah.fst.snd, -ah.fst.fst, neg_neg_is_pos ·⟩)
--     --     (⟨ah.fst.snd, ah.fst.fst, ·⟩)
--     --   --⟨-a.fst, a.snd, a.h⟩

--     -- def inv_fn : (Σ'(a : ℚ_cauchy), a.fst ≠ zero) → ℝ :=
--     --   fun a => ℝ.mk' (inv_fn_fn a)


--     -- def inv_fn_fn : (a : ℚ_cauchy) → a.fst ≠ zero → ℚ_cauchy :=
--     --   fun a h => ((eq_or_lt_or_gt a.fst zero).resolve_left h).elim'
--     --     (⟨a.snd, -a.fst, neg_neg_is_pos ·⟩) (⟨a.snd, a.fst, ·⟩)

--     -- def inv_fn : (a : ℚ_cauchy) → a.fst ≠ zero → ℝ :=
--     --   fun a h => ℝ.mk' (inv_fn_fn a h)

--     -- private theorem inv_respect : ∀(a b : ℚ_cauchy), eqv a b → inv_fn a ≍ inv_fn b := by
--     --   -- intro ⟨b1, b2, h⟩ ⟨b1', b2', h'⟩ h''
--     --   -- apply EC.sound
--     --   -- unfold eqv inv_fn_fn at *
--     --   -- simp only [mul_inv_left, mul_inv_right] at *
--     --   -- congr
--     --   sorry

--     -- -- def inv : ℝ → ℝ :=
--     -- def inv :=
--     --   EC.hlift (f := inv_fn) eqv.eqv inv_fn inv_respect

--     def inv_fn_fn : (a : ℚ_cauchy) → a.fst ≠ zero → ℚ_cauchy :=
--       fun a h => ((eq_or_lt_or_gt a.fst zero).resolve_left h).elim'
--         (⟨-a.snd, -a.fst, neg_neg_is_pos ·⟩)
--         (⟨a.snd, a.fst, ·⟩)
--       --⟨-a.fst, a.snd, a.h⟩

--     def inv_fn : (a : ℚ_cauchy) → a.fst ≠ zero → ℝ :=
--       fun a h => ℝ.mk' (inv_fn_fn a h)

--     -- def inv : (Σ'(a : ℝ), a ≠ zero) → ℝ :=
--     --   fun ah => inv_fn ⟨ah.fst.sys_of_repr, (fun h => ah.snd (num_eq_zero' ah.fst.sys_of_repr_spec h))⟩
--     def inv' : (a : ℝ) → a ≠ zero → ℝ :=
--       fun a h => inv_fn a.sys_of_repr (fun h' => h (num_eq_zero' a.sys_of_repr_spec h'))

--     theorem inv_spec_eqv {S : ℝ} (a : ℚ_cauchy) (h : S.is_member a) : (S ≠ zero) = (a.fst ≠ zero) :=
--       congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h, num_eq_zero' h⟩)

--     theorem inv_spec {S : ℝ} {h : S ≠ zero} {a : ℚ_cauchy} (hm : S.is_member a) : inv' S h = inv_fn a ((inv_spec_eqv a hm).mp h) := by
--       apply EC.sound
--       unfold eqv inv_fn_fn
--       let s := S.sys_of_repr
--       have hs := fun h0 => h (num_eq_zero' S.sys_of_repr_spec h0)
--       have ha := (inv_spec_eqv a hm).mp h
--       have hos := (eq_or_lt_or_gt s.fst zero).resolve_left hs
--       have hoa := (eq_or_lt_or_gt a.fst zero).resolve_left ha
--       let elm1 := (hos.elim' (c := ℚ_cauchy)
--         (fun x => ⟨ -s.snd, -s.fst, neg_neg_is_pos x ⟩)
--         (fun x => ⟨ s.snd, s.fst, x ⟩))
--       let elm2 := (hoa.elim' (c := ℚ_cauchy)
--           (fun x => ⟨ -a.snd, -a.fst, neg_neg_is_pos x ⟩)
--           (fun x => ⟨ a.snd, a.fst, x ⟩))
--       have heqv := S.member_related a s ⟨hm, S.sys_of_repr_spec⟩
--       unfold eqv at heqv; ac_nf at heqv
--       show elm1.fst * elm2.snd = elm1.snd * elm2.fst
--       apply Or.elim'_spec (c := ℚ_cauchy) (p := (fun m => m.fst * elm2.snd = m.snd * elm2.fst))
--       <;>intro cs<;>simp only
--       <;>apply Or.elim'_spec (c := ℚ_cauchy) (p := (fun m => _ * m.snd = _ * m.fst))
--       <;>intro ca<;>simp only [mul_neg_left, mul_neg_right]
--       <;>ac_nf<;>rw[heqv]

--     theorem inv_spec2 {S : ℝ} {a : ℚ_cauchy} {h : a.fst ≠ zero} (hm : S.is_member a) : inv' S ((inv_spec_eqv a hm).mpr h) = inv_fn a h := inv_spec hm

--       -- show (hos.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩) ).fst *
--       --   (hoa.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).snd =
--       --   (hos.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩)).snd *
--       --   (hoa.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).fst
--       -- #check Or.elim'_spec


--       -- show (hos.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩) ).fst *
--       --   (hoa.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).snd =
--       --   (hos.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ (s).snd, -(s).fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ (s).snd, (s).fst, x ⟩)).snd *
--       --   (hoa.elim' (c := ℚ_cauchy)
--       --     (fun x => ⟨ a.snd, -a.fst, neg_neg_is_pos x ⟩)
--       --     (fun x => ⟨ a.snd, a.fst, x ⟩)).fst


--     -- theorem inv_spec' (S : ℝ) {h : S ≠ zero} : ∀(a : ℚ_cauchy), S.is_member a → inv' S ≍ inv_fn a := sorry

--       -- -- theorem inv_spec' {h : ∀ (a b : α), R a b → f a = f b} (S : EquivalentClass R) : ∀(a : α), is_member a S → inv' S = f a :=
--       -- set_option pp.proofs true in
--       -- theorem inv_spec' (S : ℝ) {h : S ≠ zero} : ∀(a : ℚ_cauchy), S.is_member a → inv' S ≍ inv_fn a := by
--       --   intro a h'
--       --   have feq : (S ≠ zero) = (a.fst ≠ zero) := congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
--       --   -- have feq (S : ℝ) (a : ℚ_cauchy) (h' : S.is_member a) : (S ≠ zero) = (a.fst ≠ zero) := congrArg (¬·) (propext ⟨num_eq_zero_of_eq_zero' h', num_eq_zero' h'⟩)
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
--       --       ((((sorry):(S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ S.inv') h'')

--       --     have h4 : (((feq ▸ Eq.refl (S ≠ zero → ℝ)) : (S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ S.inv') = S.inv' := by
--       --       -- simp only []
--       --       unfold Eq.symm
--       --       generalize ((((feq ▸ Eq.refl (S ≠ zero → ℝ)): (S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ rfl) : (a.fst ≠ zero → ℝ) = (S ≠ zero → ℝ)) = x
--       --       generalize ((x ▸ rfl) : (S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) = y
--       --       have h1 : y ▸ S.inv' ≍ S.inv' := cast_heq _ _
--       --       have h2 : x ▸ y ▸ S.inv' ≍ y ▸ S.inv' := cast_heq _ _
--       --       have h3 : x ▸ y ▸ S.inv' ≍ S.inv' := HEq.trans h2 h1
--       --       exact eq_of_heq h3
--       --     -- have h4 : (((feq ▸ Eq.refl (S ≠ zero → ℝ)) : (S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ S.inv') = S.inv' := by
--       --     --   -- simp only []
--       --     --   unfold Eq.symm
--       --     --   generalize ((((feq ▸ Eq.refl (S ≠ zero → ℝ)): (S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ rfl) : (a.fst ≠ zero → ℝ) = (S ≠ zero → ℝ)) = x
--       --     --   generalize ((x ▸ rfl) : (S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) = y
--       --     --   have h1 : y ▸ S.inv' ≍ S.inv' := cast_heq _ _
--       --     --   have h2 : x ▸ y ▸ S.inv' ≍ y ▸ S.inv' := cast_heq _ _
--       --     --   have h3 : x ▸ y ▸ S.inv' ≍ S.inv' := HEq.trans h2 h1
--       --     --   exact eq_of_heq h3


--       --       -- ((((sorry):(S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ S.inv') h'')
--       --       -- ((((feq ▸ Eq.refl (S ≠ zero → ℝ)):(S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ S.inv') h'')
--       --       -- ((((feq ▸ Eq.refl (S ≠ zero → ℝ)):(S ≠ zero → ℝ) = (a.fst ≠ zero → ℝ)) ▸ S.inv') h'')
--       --     -- guard_expr (feq ▸ Eq.refl ℝ ▸ Eq.refl (S ≠ zero → ℝ)) =~ (feq ▸ Eq.refl ℝ ▸ Eq.refl (S ≠ zero → ℝ))
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


--     def inv : (Σ'(a : ℝ), a ≠ zero) → ℝ :=
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

--     @[default_instance] instance : Inv ℝ where
--       inv := inv

--     theorem inv_def {a : ℝ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = inv ⟨a, h⟩ := rfl

--     -- the more useful one :
--     theorem inv_def' {a : ℝ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = a.inv' h := rfl

--     private theorem _mul_inv_cancel : ∀ (a : ℝ) (h0 : a ≠ zero), a * ⟨a, h0⟩⁻¹ = one := by
--       intro a h0
--       rw [mul_def, inv_def', inv_spec a.sys_of_repr_spec]
--       unfold mul mul_fn mul_fn_fn inv_fn
--       rw [EC.lift_spec a _ a.sys_of_repr_spec,
--         EC.lift_spec _ _ (EC.is_member_of_from_elm _ _)]
--       apply EC.sound
--       unfold mul_fn_fn_fn inv_fn_fn one_repr eqv
--       simp only [mul_one]
--       let ap := a.sys_of_repr
--       apply Or.elim'_spec (c := ℚ_cauchy) (p := (fun x => (ap.fst * x.fst = ap.snd * x.snd))) _ _
--       <;>simp only [mul_neg_right]<;>intro<;>ac_nf

--     @[default_instance] instance : Field ℝ where
--       mul_inv_cancel := _mul_inv_cancel

--   end inv

--   section comp


--     def le_fn_fn : ℚ_cauchy → ℚ_cauchy → Prop :=
--       fun a b => a.fst * b.snd ≤ a.snd * b.fst

--     private theorem le_fn_respect (a : ℚ_cauchy) : ∀ (b c : ℚ_cauchy), eqv b c → le_fn_fn a b = le_fn_fn a c := by
--       intro b c h
--       have h' {a b c : ℚ_cauchy} : eqv b c → le_fn_fn a b → le_fn_fn a c := by
--         unfold eqv le_fn_fn
--         intro h h'
--         rw [←mul_le_mul_pos_right_iff c.h, mul_assoc a.snd, h] at h'
--         rw [←mul_le_mul_pos_right_iff b.h]
--         ac_nf at *
--       exact propext ⟨h' h, h' h.symm⟩

--     def le_fn : ℚ_cauchy → ℝ → Prop :=
--       fun a => EquivalentClass.lift eqv.eqv (le_fn_fn a) (le_fn_respect a)

--     private theorem le_respect : ∀ (a b : ℚ_cauchy), eqv a b → le_fn a = le_fn b := by
--       intro a b h
--       funext c
--       have h' {a b : ℚ_cauchy} {c : ℝ} : eqv a b → le_fn a c → le_fn b c := by
--         intro h h'
--         unfold eqv le_fn at *
--         repeat rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)] at *
--         unfold le_fn_fn at *
--         rw [←mul_le_mul_pos_left_iff a.h, ←mul_assoc, ← h]
--         rw [←mul_le_mul_pos_left_iff b.h] at h'
--         ac_nf at |- h'
--       exact propext ⟨h' h, h' h.symm⟩

--     def le : ℝ → ℝ → Prop :=
--       EquivalentClass.lift (β := ℝ → Prop) eqv.eqv le_fn le_respect

--     private theorem _le_refl : ∀ (a : ℝ), a.le a := by
--       intro a
--       unfold le le_fn le_fn_fn EC.lift
--       simp only [mul_comm]
--       exact le_refl _

--     private theorem _le_trans : ∀ (a b c : ℝ), a.le b → b.le c → a.le c := by
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

--     private theorem _le_antisymm : ∀ (a b : ℝ), a.le b → b.le a → a = b := by
--       intro a b
--       unfold le le_fn le_fn_fn EC.lift
--       intro h h'
--       apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
--       simp only [eqv] at *
--       ac_nf at *
--       exact le_antisymm _ _ h h'

--     private theorem _le_total : ∀ (a b : ℝ), a.le b ∨ b.le a := by
--       intro a b
--       unfold le le_fn le_fn_fn EC.lift
--       simp only
--       generalize a.sys_of_repr = a
--       generalize b.sys_of_repr = b
--       ac_nf
--       exact le_total _ _

--     @[default_instance] instance : Comp ℝ where
--       le := le
--       le_refl := _le_refl
--       le_trans := _le_trans
--       le_antisymm := _le_antisymm
--       le_total := _le_total

--     theorem le_def {a b : ℝ} : (a ≤ b) = a.le b := rfl

--     private theorem _add_le_add_left {a b : ℝ} : ∀(c : ℝ), a ≤ b → c + a ≤ c + b := by
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

--     @[default_instance] instance : OrderedCommMonoid ℝ where
--       _add_le_add_left := _add_le_add_left

--     @[default_instance] instance : OrderedCommGroup ℝ where

--     private theorem _mul_nonneg {a b : ℝ} : zero ≤ a → zero ≤ b → zero ≤ a * b := by
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


--     @[default_instance] instance : OrderedCommRing ℝ where
--       _mul_nonneg := _mul_nonneg
--       _zero_le_one := _zero_le_one

--     -- private theorem _mul_eq_zero {a b : ℝ} : a * b = zero → a = zero ∨ b = zero := by
--     --   rw [mul_def]
--     --   unfold mul mul_fn mul_fn_fn EC.lift mul_fn_fn_fn
--     --   intro h
--     --   replace h := EC.sound_inv eqv.eqv h
--     --   unfold eqv zero_repr at h
--     --   simp only [mul_zero, mul_one] at h
--     --   exact (mul_eq_zero h).elim
--     --     (fun h' => Or.inl (num_eq_zero' a.sys_of_repr_spec h'))
--     --     (fun h' => Or.inr (num_eq_zero' b.sys_of_repr_spec h'))

--     -- @[default_instance] instance : OrderedCommRing' ℝ where
--     --   mul_eq_zero := _mul_eq_zero

--     @[default_instance] instance : OrderedField ℝ where

--   end comp


end ℝ

end my
