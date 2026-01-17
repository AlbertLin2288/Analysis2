import Analysis2.Rat
import Analysis2.Seq

noncomputable section
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing' Field
open Comp
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing OrderedCommRing' OrderedField
open Zero One
open Abs OfNat
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

    theorem conv_zero_of_eq_zero {a : ℚ_cauchy} : eqv a ⟨(zero : Seq ℚ), is_cauchy_of_const zero⟩ → conv_to a.s zero := by
      unfold eqv;simp only [neg_zero, add_zero];exact id

    theorem eq_zero_of_conv_zero {a : ℚ_cauchy} : conv_to a.s zero → eqv a ⟨(zero : Seq ℚ), is_cauchy_of_const zero⟩ := by
      unfold eqv;simp only [neg_zero, add_zero];exact id

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

    def mul_fn_fn_fn : ℚ_cauchy → ℚ_cauchy → ℚ_cauchy :=
      fun a b => ⟨a.s * b.s, is_cauchy_of_mul a.h b.h⟩

    def mul_fn_fn : ℚ_cauchy → ℚ_cauchy → ℝ :=
      fun a b => ℝ.mk' (mul_fn_fn_fn a b)

    private theorem mul_aux {s1 s2 : Seq ℚ} (h1 : is_cauchy s1) (h2 : conv_to s2 zero) : conv_to (s1 * s2) zero := by
      intro ε hε
      replace ⟨N1, h1⟩ := h1 one zero_lt_one
      let a := abs (s1 N1) + one
      have ha := nonneg_add_pos_is_pos (abs_nonneg (s1 N1)) zero_lt_one
      let ε2 := ε * ⟨a, ne_of_gt ha⟩⁻¹
      have hε2 := mul_pos hε (inv_pos_is_pos ha)
      replace ⟨N2, h2⟩ := h2 ε2 hε2
      let N := max N1 N2
      exists N
      intro n hn
      replace h1 := abs_neg_eq_abs (s1 N1) ▸ lt_add_of_sub_left_lt (lt_of_le_lt (triangle_add_ge_sub _ _) (h1 n N1 (le_of_le_le max_ge_fst hn) (le_self N1)))
      replace h2 := lt_of_le_lt (triangle_add_ge_sub _ _) (h2 n (le_of_le_le max_ge_snd hn))
      simp only [neg_zero, abs_of_zero, add_zero] at h2
      rw [neg_zero, add_zero, Seq.mul_def, abs_of_mul_eq_mul_abs]
      exact mul_mul_inv_cancel_left2 (ne_of_gt ha) (b:=ε) ▸ (lt_of_mul_nonneg_nonneg_lt_lt (abs_nonneg _) (abs_nonneg _) h1 h2)

    private theorem mul_fn_respect (a : ℚ_cauchy) : ∀ (b c : ℚ_cauchy), eqv b c → mul_fn_fn a b = mul_fn_fn a c := by
      intro b c h
      apply EC.sound
      unfold eqv mul_fn_fn_fn at *
      simp only [←mul_neg_right, ←mul_add] at *
      exact mul_aux a.h h

    def mul_fn : ℚ_cauchy → ℝ → ℝ :=
      fun a => EquivalentClass.lift (β := ℝ) eqv.eqv (mul_fn_fn a) (mul_fn_respect a)

    private theorem mul_respect : ∀ (a b : ℚ_cauchy), eqv a b → mul_fn a = mul_fn b := by
      intro a b h
      funext Sc
      let c := Sc.sys_of_repr
      apply EC.sound
      unfold eqv mul_fn_fn_fn at *
      rw [←mul_neg_left, ←add_mul, mul_comm _ c.s]
      exact mul_aux c.h h

    def mul : ℝ → ℝ → ℝ :=
      EquivalentClass.lift (β := ℝ → ℝ) eqv.eqv mul_fn mul_respect


    @[default_instance] instance : Mul ℝ where
      mul := mul

    theorem mul_def {a b : ℝ} : a * b = a.mul b := rfl

    private theorem _mul_one : ∀ (a : ℝ), a * one = a := by
      intro a
      repeat first | rw [mul_def]
      unfold mul mul_fn mul_fn_fn
      repeat first
      | rw [EC.lift_spec (one : ℝ) _ (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)]
      apply EC.sound' eqv.eqv (EC.is_member_of_from_elm _ eqv.eqv) a.sys_of_repr_spec _
      unfold mul_fn_fn_fn one_repr eqv
      simp only [mul_one, add_neg]
      exact conv_to_of_const zero

    private theorem _mul_assoc : ∀ (a b c : ℝ), a * b * c = a * (b * c) := by
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
      simp only [mul_assoc, add_neg]
      exact conv_to_of_const zero


    private theorem _add_mul : ∀ (a b c : ℝ), (a + b) * c = a * c + b * c := by
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
      simp only [add_mul, add_neg]
      exact conv_to_of_const zero

    private theorem _zero_ne_one : zero ≠ one := by
      intro h
      replace h := EC.sound_inv' one_is_member_one zero_is_member_zero h.symm
      unfold eqv zero_repr one_repr one at h
      simp [neg_zero, add_zero] at h
      replace ⟨N, h⟩ := h one zero_lt_one
      replace h := h N (le_self N)
      rw [neg_zero, add_zero, abs_of_nonneg zero_le_one] at h
      exact (not_lt_self one) h

    private theorem _mul_comm : ∀ (a b : ℝ), a * b = b * a := by
      intro a b
      apply EC.sound
      unfold eqv mul_fn_fn_fn
      simp only [mul_comm, add_neg]
      exact conv_to_of_const zero


    @[default_instance] instance : CommRing ℝ where
      _mul_one := _mul_one
      _mul_assoc := _mul_assoc
      _add_mul := _add_mul
      _zero_ne_one := _zero_ne_one
      _mul_comm := _mul_comm


  end mul

  section inv

    theorem inv_aux {s : Seq ℚ} (h : is_cauchy s) (h' : ¬ conv_to s zero) :
      ∃(N : ℕ) (l : ℚ), zero < l ∧ ((∀(n : ℕ), N ≤ n → l ≤ s n) ∨ (∀(n : ℕ), N ≤ n → l ≤ -(s n))) := by
        apply byContradiction
        intro hc
        simp only [not_exists, not_and, not_or, not_forall] at hc
        simp only [not_forall, not_exists, neg_zero, add_zero] at h'
        replace ⟨ε, hε, h'⟩ := h'
        let ε2 := ε * ℚ.num.one_half
        have hε2 := mul_pos hε ℚ.num.one_half_pos
        replace ⟨N1, h⟩ := h ε2 hε2
        replace ⟨N2, hN, h'⟩ := h' N1
        replace h' := le_of_not_lt h'
        replace ⟨⟨n, hn, hc⟩, ⟨n', hn', hc'⟩⟩ := hc N1 ε2 hε2
        have ε22 : ε2 + ε2 = ε := by unfold ε2;simp [←mul_add,ℚ.num.add_half,mul_one]
        have ε21 : ε2 = ε - ε2 := eq_sub_right_of_add_eq ε22
        replace hc := lt_of_not_le hc
        replace hc' := lt_of_not_le hc'
        cases nonpos_or_nonneg (s N2)
        case h.inl h'' =>
          rw [abs_of_nonpos h''] at h'
          replace h' := le_neg_of_le_neg h'
          replace h := h N2 n' hN hn'
          have h'' : s N2 - s n' ≤ -ε2 := by
            rw [ε21, neg_sum, neg_neg]
            exact le_of_add_le_lt h' hc'
          rw [abs_of_neg (lt_of_le_lt h'' (neg_pos_is_neg hε2))] at h
          exact (not_le_of_lt (neg_lt_of_neg_lt h)) h''
        case h.inr h'' =>
          rw [abs_of_nonneg h''] at h'
          replace h := h N2 n hN hn
          have h'' : s N2 - s n ≥ ε2 := ε21 ▸ le_of_add_le_lt h' (neg_lt_neg_of_lt hc)
          rw [abs_of_pos (lt_of_lt_le hε2 h'')] at h
          exact (not_le_of_lt h) h''

    theorem inv_aux' {s : Seq ℚ} (h : is_cauchy s) (h' : ¬ conv_to s zero) :
      ∃(N : ℕ) (l : ℚ), zero < l ∧ ∀(n : ℕ), N ≤ n → l ≤ abs (s n) :=
      ⟨(inv_aux h h').choose, (inv_aux h h').choose_spec.choose, (inv_aux h h').choose_spec.choose_spec.left,
      (inv_aux h h').choose_spec.choose_spec.right.elim
        (fun hl n hn => le_of_le_eq (hl n hn) (abs_of_nonneg (le_of_lt_le ((inv_aux h h').choose_spec.choose_spec.left) (hl n hn))).symm)
        (fun hl n hn => le_of_le_eq (hl n hn) (abs_of_neg (neg_pos_iff_neg.mp (lt_of_lt_le ((inv_aux h h').choose_spec.choose_spec.left) (hl n hn)))).symm)⟩

    def inv_fn_fn (a : ℚ_cauchy) (h : ¬conv_to a.s zero) : ℚ_cauchy :=
      have hv := inv_aux a.h h
      ⟨(
        fun n => (lt_or_ge n hv.choose).elim' (fun _ => zero) (fun hn => ⟨a.s n, (by
          have ⟨l, hl, hnl⟩ := hv.choose_spec
          exact (hnl.elim (fun x => ne_of_gt (lt_of_lt_le hl (x n hn))) (fun x => ne_of_lt (neg_pos_iff_neg.mp (lt_of_lt_le hl (x n hn)))))
        )⟩⁻¹)
      ) , (by
        let N1 := hv.choose
        have ⟨l, ⟨hl, hNl⟩⟩ := hv.choose_spec
        intro ε hε
        let ε2 := ε * (l * l)
        have hε2 := mul_pos hε (mul_pos hl hl)
        have ⟨N2, hN2⟩ := a.h ε2 hε2
        let N := max N1 N2
        exists N
        intro n m hn hm
        replace hN2 := hN2 n m (le_of_le_le max_ge_snd hn) (le_of_le_le max_ge_snd hm)
        refine' Or.elim'_spec (p:=fun x => abs (x - _) < ε) (fun hc => (not_lt_of_le (le_of_le_le max_ge_fst hn) hc).elim) (fun _ => _)
        refine' Or.elim'_spec (p:=fun x => abs (_ - x) < ε) (fun hc => (not_lt_of_le (le_of_le_le max_ge_fst hm) hc).elim) (fun _ => _)
        have thm1 (s : Seq ℚ) (n m : ℕ) (hnl : l ≤ s n) (hml : l ≤ s m)
           (hN2 : abs (s n - s m) < ε2)
          : abs (⟨s n, ne_of_gt (lt_of_lt_le hl hnl)⟩⁻¹ + -⟨s m, ne_of_gt (lt_of_lt_le hl hml)⟩⁻¹) < ε := by
            apply lt_of_mul_lt_mul_pos_right _ (mul_pos (lt_of_lt_le hl hnl) (lt_of_lt_le hl hml))
            have : ε * (s n * s m) ≥ ε2 := by
              refine' mul_le_mul_of_pos_left _ hε
              exact le_of_mul_nonneg_nonneg_le_le (le_of_lt hl) (le_of_lt hl) hnl hml
            refine' lt_of_lt_le _ this
            rw [←abs_of_pos (mul_pos (lt_of_lt_le hl hnl) (lt_of_lt_le hl hml)), ←abs_of_mul_eq_mul_abs]
            rw [mul_comm, mul_add, mul_mul_inv_cancel_left1, mul_neg_right , mul_mul_inv_cancel_right]
            rwa [←abs_neg_eq_abs, neg_sub] at hN2
        cases hNl
        case inl hNl =>
          have hnl := hNl n (le_of_le_le max_ge_fst hn)
          have hml := hNl m (le_of_le_le max_ge_fst hm)
          exact thm1 a.s n m hnl hml hN2
        case inr hNl =>
          have hnl := hNl n (le_of_le_le max_ge_fst hn)
          have hml := hNl m (le_of_le_le max_ge_fst hm)
          have hn0 := ne_of_lt (neg_pos_iff_neg.mp (lt_of_lt_le hl hnl))
          have hm0 := ne_of_lt (neg_pos_iff_neg.mp (lt_of_lt_le hl hml))
          replace hN2 : abs ((-a.s) n + -(-a.s) m) < ε2 := by
            simp only [Seq.neg_def, ← neg_sum, abs_neg_eq_abs]
            exact hN2
          have h := thm1 (-a.s) n m hnl hml hN2
          simp only [Seq.neg_def, inv_neg _ hn0, inv_neg _ hm0, ←neg_sum, abs_neg_eq_abs] at h
          exact h
      )⟩

    def inv_fn : (a : ℚ_cauchy) → ¬ conv_to a.s zero → ℝ :=
      fun a h => ℝ.mk' (inv_fn_fn a h)

    def inv' : (a : ℝ) → a ≠ zero → ℝ :=
      fun a h => inv_fn a.sys_of_repr
        (fun h' => h (EC.sound' eqv.eqv a.sys_of_repr_spec zero_is_member_zero (eq_zero_of_conv_zero h')))

    def inv : (Σ'(a : ℝ), a ≠ zero) → ℝ :=
      fun a => a.fst.inv' a.snd

    @[default_instance] instance : Inv ℝ where
      inv := inv

    theorem inv_def {a : ℝ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = inv ⟨a, h⟩ := rfl

    -- the more useful one :
    theorem inv_def' {a : ℝ} {h : a ≠ zero} : ⟨a, h⟩⁻¹ = a.inv' h := rfl

    set_option pp.proofs true
    private theorem _mul_inv_cancel : ∀ (a : ℝ) (h0 : a ≠ zero), a * ⟨a, h0⟩⁻¹ = one := by
      intro a h0
      let ap := a.sys_of_repr
      let s := ap.s
      have hs0 : ¬conv_to s zero := (fun h => h0 (EC.sound' eqv.eqv a.sys_of_repr_spec zero_is_member_zero (eq_zero_of_conv_zero h)))
      let avp := inv_fn_fn ap hs0
      rw [mul_def, inv_def']
      unfold mul mul_fn mul_fn_fn inv' inv_fn
      rw [EC.lift_spec a _ a.sys_of_repr_spec,
        EC.lift_spec _ avp (EC.is_member_of_from_elm _ eqv.eqv)]
      apply EC.sound
      unfold one_repr mul_fn_fn_fn avp inv_fn_fn eqv
      simp only
      let hv := inv_aux ap.h hs0
      let N1 := hv.choose
      intro ε hε
      exists N1
      intro n hn
      simp only [neg_zero, add_zero, Seq.mul_def, Seq.add_def]
      refine' Or.elim'_spec (p:=fun x =>(abs ((s n * x) + -one) < ε)) (fun hn' => (not_lt_of_le hn hn').elim) _
      intro hn'
      guard_expr hn' = hn
      rw [mul_inv_cancel, add_neg, abs_of_zero]
      exact hε

    @[default_instance] instance : Field ℝ where
      mul_inv_cancel := _mul_inv_cancel

  end inv

  section comp

    -- def _is_nonneg : ℚ_cauchy → Prop :=
    --   fun a => conv_to a.s zero ∨ ∃(N : ℕ), ∀(n : ℕ), N ≤ n → zero ≤ a.s n
    -- Only meaningful if seq is cauchy
    def _is_nonneg : Seq ℚ → Prop :=
      fun s => conv_to s zero ∨ ∃(N : ℕ), ∀(n : ℕ), N ≤ n → zero ≤ s n


    def le_fn_fn : ℚ_cauchy → ℚ_cauchy → Prop :=
      fun a b => _is_nonneg (b.s - a.s)

    private theorem le_aux {s1 s2 : Seq ℚ} (h1 : is_cauchy s1) (h : conv_to (s1 - s2) zero) : _is_nonneg s1 → _is_nonneg s2 := by
      intro h'
      by_cases h'' : conv_to s1 zero
      case pos =>
        replace h := neg_sub s1 _ ▸ conv_to_neg_of_neg h
        replace h := conv_to_sum_of_sum h h''
        rw [add_assoc, neg_add, add_zero, add_zero, neg_zero] at h
        exact Or.inl h
      case neg =>
        -- have c21 := is_cauchy_of_sum h2 (is_cauchy_of_neg h1)
        have ⟨N1, l, hl, hN1⟩ := inv_aux h1 h''
        replace hN1 := hN1.resolve_right (by
          intro hc
          have ⟨N2, hN2⟩ := h'.resolve_left h''
          let N := max N1 N2
          replace hc := hc N max_ge_fst
          replace hN2 := neg_nonneg_is_nonpos (hN2 N max_ge_snd)
          exact not_le_of_lt (lt_of_lt_le hl hc) hN2
        )
        replace ⟨N2, hN2⟩ := h l hl
        let N := max N1 N2
        refine' Or.inr ⟨N, _⟩
        intro n hn
        replace hN1 := hN1 n (le_of_le_le max_ge_fst hn)
        replace hN2 := lt_of_le_lt (self_le_abs_self _) (sub_zero _ (α:=ℚ) ▸ hN2 n (le_of_le_le max_ge_snd hn))
        rw [Seq.add_def, Seq.neg_def] at *
        replace hN1 := (le_of_lt_le hN2 hN1)
        simp only at hN1 |-
        apply le_of_add_le_add_left (c:=(s1 n))
        rw [add_zero]
        exact (le_add_of_sub_right_le hN1)


    private theorem le_fn_respect (a : ℚ_cauchy) : ∀ (b c : ℚ_cauchy), eqv b c → le_fn_fn a b = le_fn_fn a c := by
      intro b c h
      have thm1 {a b c : ℚ_cauchy} (h : eqv b c) : le_fn_fn a b → le_fn_fn a c := by
        unfold eqv le_fn_fn at *
        rw [←add_zero b.s, ←neg_add a.s, ←add_assoc, add_assoc, ←neg_sub c.s] at h
        exact le_aux (is_cauchy_of_sum b.h (is_cauchy_of_neg a.h)) h
      exact propext ⟨thm1 h, thm1 h.symm⟩

    def le_fn : ℚ_cauchy → ℝ → Prop :=
      fun a => EquivalentClass.lift eqv.eqv (le_fn_fn a) (le_fn_respect a)

    private theorem le_respect : ∀ (a b : ℚ_cauchy), eqv a b → le_fn a = le_fn b := by
      intro a b h
      funext c
      have thm1 {a b : ℚ_cauchy} {c : ℝ} : eqv a b → le_fn a c → le_fn b c := by
        intro h h'
        unfold eqv le_fn at *
        repeat rw [EC.lift_spec _ _ (EC.sys_of_repr_spec _)] at *
        unfold le_fn_fn at *
        generalize c.sys_of_repr = c at *
        replace h := conv_to_neg_of_neg h
        rw [neg_sub, neg_zero, ←add_zero b.s, ←neg_add c.s, ←add_assoc, add_assoc] at h
        rw [add_comm, ←neg_sub _ b.s] at h
        exact le_aux (is_cauchy_of_sum c.h (is_cauchy_of_neg a.h)) h h'

      exact propext ⟨thm1 h, thm1 h.symm⟩

    def le : ℝ → ℝ → Prop :=
      EquivalentClass.lift (β := ℝ → Prop) eqv.eqv le_fn le_respect

    private theorem _le_refl : ∀ (a : ℝ), a.le a := by
      intro a
      unfold le le_fn le_fn_fn EC.lift
      simp only [add_neg]
      apply Or.inl
      exact conv_to_of_const zero

    private theorem _le_trans : ∀ (a b c : ℝ), a.le b → b.le c → a.le c := by
      intro a b c
      unfold le le_fn le_fn_fn EC.lift
      simp only
      generalize a.sys_of_repr = a
      generalize b.sys_of_repr = b
      generalize c.sys_of_repr = c
      intro h h'
      by_cases h0 : conv_to (b.s - a.s) zero
      case pos =>
        replace h0 := conv_to_neg_of_neg h0
        rw [neg_sum, neg_zero, neg_neg, ←add_zero (-b.s), ←add_neg c.s, ←add_assoc] at h0
        rw [add_assoc, add_comm (-b.s), add_comm (-c.s), ←neg_sub c.s] at h0
        exact le_aux (is_cauchy_of_sum c.h (is_cauchy_of_neg b.h)) h0 h'
      case neg =>
        by_cases h0' : conv_to (c.s - b.s) zero
        case pos =>
          replace h0' := conv_to_neg_of_neg h0'
          rw [neg_sub, neg_zero, ←add_zero (b.s), ←neg_add a.s, ←add_assoc] at h0'
          rw [add_assoc, ←neg_sub c.s] at h0'
          exact le_aux (is_cauchy_of_sum b.h (is_cauchy_of_neg a.h)) h0' h
        case neg =>
          replace ⟨N1, hN1⟩ := h.resolve_left h0
          replace ⟨N2, hN2⟩ := h'.resolve_left h0'
          let N := max N1 N2
          refine' Or.inr ⟨N, _⟩
          intro n hn
          replace hN1 := hN1 n (le_of_le_le max_ge_fst hn)
          replace hN2 := hN2 n (le_of_le_le max_ge_snd hn)
          have hN := nonneg_add_nonneg_is_nonneg hN2 hN1
          simp only [Seq.add_def, Seq.neg_def, ←add_assoc, sub_add_cancel] at hN
          exact hN

    private theorem _le_antisymm : ∀ (a b : ℝ), a.le b → b.le a → a = b := by
      intro a b
      unfold le le_fn le_fn_fn EC.lift
      intro h' h
      apply EC.sound' eqv.eqv a.sys_of_repr_spec b.sys_of_repr_spec
      simp only [eqv] at *
      generalize a.sys_of_repr = a at *
      generalize b.sys_of_repr = b at *
      refine' (em (conv_to (a.s - b.s) zero)).elim id _
      intro h0
      have h0' : ¬conv_to (b.s - a.s) zero := by
        intro h0';rw [←neg_sub, ←neg_zero] at h0;exact h0 (conv_to_neg_of_neg h0')
      replace ⟨N1, hN1⟩ := h.resolve_left h0
      replace ⟨N2, hN2⟩ := h'.resolve_left h0'
      let N := max N1 N2
      intro ε hε
      exists N
      intro n hn
      replace hN1 := hN1 n (le_of_le_le max_ge_fst hn)
      replace hN2 := neg_sub a.s b.s ▸ hN2 n (le_of_le_le max_ge_snd hn)
      rw [←le_antisymm _ _ hN1 (neg_nonneg_iff_nonpos.mp hN2),sub_zero,abs_of_zero]
      exact hε

    private theorem _le_total : ∀ (a b : ℝ), a.le b ∨ b.le a := by
      intro a b
      unfold le le_fn le_fn_fn EC.lift
      simp only
      generalize a.sys_of_repr = a
      generalize b.sys_of_repr = b
      have thm1 {s : Seq ℚ} (hs : is_cauchy s) : _is_nonneg s ∨ _is_nonneg (-s) := by
        by_cases h0 : conv_to s zero
        case pos => exact Or.inl (Or.inl h0)
        case neg =>
          have ⟨N, l, hl, hnl⟩ := inv_aux hs h0
          have thm2 {s : Seq ℚ} (hs : is_cauchy s) (N : ℕ) (l : ℚ) (hl : zero < l)
            (hnl : ∀ (n : ℕ), N ≤ n → l ≤ s n) : _is_nonneg s := by
              refine' Or.inr ⟨N, _⟩
              intro n hn
              exact le_of_lt_le hl (hnl n hn)
          cases hnl
          case inl hnl =>
            exact Or.inl (thm2 hs N l hl hnl)
          case inr hnl =>
            exact Or.inr (thm2 (is_cauchy_of_neg hs) N l hl hnl)
      exact (thm1 (is_cauchy_of_sum b.h (is_cauchy_of_neg a.h))).elim Or.inl (fun h => Or.inr (neg_sub b.s a.s ▸ h))

    @[default_instance] instance : Comp ℝ where
      le := le
      le_refl := _le_refl
      le_trans := _le_trans
      le_antisymm := _le_antisymm
      le_total := _le_total

    theorem le_def {a b : ℝ} : (a ≤ b) = a.le b := rfl

    private theorem _add_le_add_left {a b : ℝ} : ∀(c : ℝ), a ≤ b → c + a ≤ c + b := by
      intro c
      simp only [le_def, add_def]
      let ap := a.sys_of_repr
      let bp := b.sys_of_repr
      let cp := c.sys_of_repr
      unfold le le_fn le_fn_fn add add_fn add_fn_fn
      intro h
      replace h : _is_nonneg (bp.s + -ap.s) := h
      repeat first
      | rw [EC.lift_spec _ _ a.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ b.sys_of_repr_spec]
      | rw [EC.lift_spec _ _ c.sys_of_repr_spec]
      | rw [EC.lift_spec _ (add_fn_fn_fn cp ap) (EC.is_member_of_from_elm _ eqv.eqv)]
      | rw [EC.lift_spec _ (add_fn_fn_fn cp bp) (EC.is_member_of_from_elm _ eqv.eqv)]
      unfold add_fn_fn_fn
      simp only [neg_sum, ←add_assoc, add_comm _ bp.s, add_sub_cancel]
      exact h

    @[default_instance] instance : OrderedCommMonoid ℝ where
      _add_le_add_left := _add_le_add_left

    @[default_instance] instance : OrderedCommGroup ℝ where

    private theorem _mul_nonneg {a b : ℝ} : zero ≤ a → zero ≤ b → zero ≤ a * b := by
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
      simp only [sub_zero]
      show _is_nonneg ap.s → _is_nonneg bp.s → _is_nonneg (ap.s*bp.s)
      intro h h'
      by_cases h0 : conv_to ap.s zero
      case pos =>
        exact Or.inl (mul_comm bp.s _ ▸ mul_aux bp.h h0)
      case neg =>
        by_cases h0' : conv_to bp.s zero
        case pos =>
          exact Or.inl (mul_aux ap.h h0')
        case neg =>
          have ⟨N1, hN1⟩ := h.resolve_left h0
          have ⟨N2, hN2⟩ := h'.resolve_left h0'
          let N := max N1 N2
          refine' Or.inr ⟨N, _⟩
          intro n hn
          simp only [Seq.mul_def]
          exact mul_nonneg (hN1 n (le_of_le_le max_ge_fst hn)) (hN2 n (le_of_le_le max_ge_snd hn))

    private theorem _zero_le_one : zero ≤ one := by
      rw [le_def]
      unfold le le_fn le_fn_fn
      rw [EC.lift_spec _ _ zero_is_member_zero]
      rw [EC.lift_spec _ _ one_is_member_one]
      unfold zero_repr one_repr
      simp only [sub_zero]
      refine' Or.inr ⟨zero, _⟩
      intros
      exact zero_le_one


    @[default_instance] instance : OrderedCommRing ℝ where
      _mul_nonneg := _mul_nonneg
      _zero_le_one := _zero_le_one

    @[default_instance] instance : OrderedField ℝ where

    theorem ofNat_repr (n : ℕ) : ofNat (α:=ℝ) n = mk' ⟨const_seq (ofNat (α:=ℚ) n), is_cauchy_of_const _⟩ := by
      induction n
      case _zero => rfl
      case succ n h =>
        conv => lhs;change ofNat (α:=ℝ) n + one
        conv => rhs;enter [1,1,1];change ofNat (α:=ℚ) n + one
        rw [h, add_def]
        unfold add add_fn
        rw [EC.lift_spec _ _ (EC.is_member_of_from_elm _ eqv.eqv)]
        rw [EC.lift_spec _ _ one_is_member_one]
        apply EC.sound
        unfold add_fn_fn_fn one_repr eqv const_seq
        simp only [Seq.add_def, Seq.neg_def]
        conv in (fun _ => _) =>
          ext n
          rw [neg_sum, ←add_assoc, add_comm (ofNat _), add_sub_cancel]
          change one - one
          rw [sub_self]
        exact conv_to_of_const zero

    theorem archimedean : ∀x : ℝ, ∃n : ℕ, x ≤ ofNat n := by
      intro x
      let s := x.sys_of_repr.s
      let hs : is_cauchy s := x.sys_of_repr.h
      replace ⟨N, hN⟩ := hs one zero_lt_one
      have ⟨x', hx'⟩ := (ℚ.archimedean (s N + one))
      exists x'
      rw [le_def, ofNat_repr]
      unfold le le_fn
      rw [EC.lift_spec _ _ (x.sys_of_repr_spec)]
      rw [EC.lift_spec _ _ (EC.is_member_of_from_elm _ eqv.eqv)]
      unfold le_fn_fn eqv
      refine' Or.inr ⟨N, _⟩
      intro n hn
      simp only [Seq.neg_def, Seq.add_def]
      show zero ≤ (ofNat x') + -(s n)
      refine' le_of_le_le _ (add_le_add_right (-s n) hx')
      rw [add_comm (s N), add_assoc, ←neg_sub, sub_nonneg_iff]
      exact le_of_le_lt (self_le_abs_self (s n - s N)) (hN n N hn (le_self N))

  end comp


end ℝ

end my
