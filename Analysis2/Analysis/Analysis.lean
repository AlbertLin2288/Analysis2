import Analysis2.Real
noncomputable section
set_option maxHeartbeats 5000
namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing' Field
open Comp
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing OrderedCommRing' OrderedField
open Zero One
open Abs OfNat
open Seq


@[reducible] def Set (α : Type) := α → Prop
instance : Membership α (Set α) where
  mem := fun S a => S a

def con_set {α : Type} (S : Set α) (pred : α → Prop) : Set α :=
  fun a => a ∈ S ∧ pred a

def all_set (α : Type) : Set α := fun _ => True

def nonempty {α : Type} : Set α → Prop :=
  fun S => ∃a ∈ S, True

@[reducible] def ℝSet := Set ℝ
-- @[reducible] def ℝ : ℝSet := all_set Real

def is_maximum {α : Type} [Comp α] (a : α) (S : Set α) : Prop :=
  a ∈ S ∧ ∀x ∈ S, x ≤ a

def is_minimum {α : Type} [Comp α] (a : α) (S : Set α) : Prop :=
  a ∈ S ∧ ∀x ∈ S, a ≤ x

theorem minimum_unique {α : Type} [Comp α] (S : Set α) {a b : α} : is_minimum a S → is_minimum b S → a = b :=
  fun ha hb => le_antisymm _ _ (ha.right b hb.left) (hb.right a ha.left)

theorem maximum_unique {α : Type} [Comp α] (S : Set α) {a b : α} : is_maximum a S → is_maximum b S → a = b :=
  fun ha hb => le_antisymm _ _ (hb.right a ha.left) (ha.right b hb.left)

def is_lowerbound {α : Type} [Comp α] (a : α) (S : Set α) : Prop :=
  ∀x ∈ S, a ≤ x

def is_upperbound {α : Type} [Comp α] (a : α) (S : Set α) : Prop :=
  ∀x ∈ S, x ≤ a

def is_supremum {α : Type} [Comp α] (a : α) (S : Set α) : Prop :=
  is_upperbound a S ∧ ∀x : α, is_upperbound x S → a ≤ x

def is_infimum {α : Type} [Comp α] (a : α) (S : Set α) : Prop :=
  is_lowerbound a S ∧ ∀x : α, is_lowerbound x S → x ≤ a

def is_above_bounded {α : Type} [Comp α] (S : Set α) : Prop :=
  ∃b : α, is_upperbound b S

def is_below_bounded {α : Type} [Comp α] (S : Set α) : Prop :=
  ∃b : α, is_lowerbound b S

def is_bounded {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] (S : Set α) : Prop :=
  ∃b : α, ∀x ∈ S, abs x ≤ b

def limit {α : Type} [Zero α] [Add α] [Neg α] [Comp α] (s : Seq α) (h : is_conv s) : α :=
  h.choose

theorem limit_of_conv_to {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] (s : Seq α) (a : α) (h : conv_to s a) : limit s (is_conv_of_conv_to h) = a :=
  conv_to_unique (is_conv_of_conv_to h).choose_spec h

theorem limit_of_const {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] (a : α) : limit (const_seq a) (conv_of_const a) = a :=
  limit_of_conv_to _ _ (conv_to_of_const _)

theorem conv_to_limit {α : Type} [Zero α] [Add α] [Neg α] [Comp α] (s : Seq α) (h : is_conv s) : conv_to s (limit _ h) :=
  h.choose_spec

def seq_bounded_above {α : Type} [Comp α] (s : Seq α) : Prop :=
  ∃b : α, ∀n : ℕ, b ≥ s n

def seq_bounded_below {α : Type} [Comp α] (s : Seq α) : Prop :=
  ∃b : α, ∀n : ℕ, b ≤ s n

def seq_bounded {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] (s : Seq α) : Prop :=
  ∃b : α, ∀n : ℕ, abs (s n) ≤ b

theorem seq_bounded_above_of_bounded {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] {s : Seq α} : seq_bounded s → seq_bounded_above s :=
  fun ⟨b, hb⟩ => ⟨b, fun n => le_of_le_le (self_le_abs_self _) (hb n)⟩

theorem seq_bounded_below_of_bounded {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] {s : Seq α} : seq_bounded s → seq_bounded_below s :=
  fun ⟨b, hb⟩ => ⟨-b, fun n => le_of_le_le (neg_le_neg_of_le (hb n)) (neg_le_of_neg_le (neg_self_le_abs_self _))⟩

theorem seq_bounded_of_above_below_bounded {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] {s : Seq α} : seq_bounded_below s → seq_bounded_above s → seq_bounded s :=
  fun ⟨b, hb⟩ ⟨b', hb'⟩ => ⟨max (-b) b', fun n => (nonneg_or_nonpos (s n)).elim (fun h => (abs_of_nonneg h).substr (le_of_le_le (hb' n) max_ge_snd)) (fun h => abs_of_nonpos h ▸ le_of_le_le (neg_le_neg_of_le (hb n)) max_ge_fst)⟩

theorem seq_bounded_iff {α : Type} [Zero α] [Add α] [Neg α] [Comp α] [CommMonoid α] [CommGroup α] [OrderedCommMonoid α] [OrderedCommGroup α] {s : Seq α} : seq_bounded s ↔ seq_bounded_below s ∧ seq_bounded_above s :=
  ⟨fun h => ⟨seq_bounded_below_of_bounded h, seq_bounded_above_of_bounded h⟩, fun h => seq_bounded_of_above_below_bounded h.left h.right⟩

def increasing {α : Type} [Comp α] : Seq α → Prop :=
  fun s => ∀n m : ℕ, n ≤ m → s n ≤ s m

def decreasing {α : Type} [Comp α] : Seq α → Prop :=
  fun s => ∀n m : ℕ, n ≤ m → s n ≥ s m

def monotone {α : Type} [Comp α] : Seq α → Prop :=
  fun s => increasing s ∨ decreasing s

theorem is_supremum_alt {a : ℝ} {S : ℝSet} (h : is_upperbound a S) :
  (∀ε, ε > zero → ∃x ∈ S, abs (a-x) < ε) → is_supremum a S := by
    intro h'
    refine' ⟨h, _⟩
    intro x hx
    apply le_of_not_lt
    intro hl
    replace hl := sub_pos_of_lt hl
    replace ⟨x', hx'⟩ := h' (a-x) hl
    replace hx := hx x' hx'.left
    replace hx' := lt_of_neg_lt_neg (lt_of_add_lt_add_left (lt_of_le_lt (self_le_abs_self _) hx'.right) )
    exact not_le_of_lt hx' hx

theorem limit_of_le_le {s : Seq ℝ} (hs : is_conv s) {s' : Seq ℝ} (hs' : is_conv s') (h : ∀n : ℕ, s n ≤ s' n) : limit s hs ≤ limit s' hs' := by
  apply le_of_not_lt
  intro hc
  let d := limit _ hs - limit _ hs'
  have hd : zero < d := sub_pos_of_lt hc
  let d2 := half d
  have hd2 : zero < d2 := half_of_pos_is_pos hd
  replace ⟨N1, hN1⟩ := conv_to_limit _ hs d2 hd2
  replace ⟨N2, hN2⟩ := conv_to_limit _ hs' d2 hd2
  let N := max N1 N2
  replace hN1 := hN1 N max_ge_fst
  replace hN2 := hN2 N max_ge_snd
  replace h := h N
  replace hN1 := lt_of_le_lt (triangle_sub_le_add _ _) (lt_of_add_lt_lt hN2 hN1)
  rw [add_half d, neg_sub, add_assoc, ←add_assoc (-_), add_comm (-_)] at hN1
  replace hN1 : s' N + (d - s N) < d := lt_of_le_lt (self_le_abs_self _) hN1
  replace h := add_le_add_right d (sub_nonneg_of_le h)
  rw [zero_add, add_right_comm, add_assoc] at h
  exact not_lt_of_le h hN1

theorem limit_of_le_le_const {s : Seq ℝ} (hs : is_conv s) (c : ℝ) (h : ∀n : ℕ, s n ≤ c) : limit s hs ≤ c := by
  rw [←limit_of_const c]
  apply limit_of_le_le
  intro n
  exact h n

theorem limit_of_le_const_le {s : Seq ℝ} (hs : is_conv s) (c : ℝ) (h : ∀n : ℕ, c ≤ s n) : c ≤ limit s hs := by
  rw [←limit_of_const c]
  apply limit_of_le_le
  intro n
  exact h n

theorem abs_half_pow_conv_to_zero {s : Seq ℝ} (hsi : ∀n : ℕ, abs (s n.succ) = abs (half (s n))) : conv_to s zero := by
  intro ε hε
  let s0 := abs (s zero)
  let s' : Seq ℕ := ℕ.rec one fun _ x => x + x
  have hs'' : ∀n : ℕ, one ≤ s' n := ℕ.rec (le_self _) fun _ h => ℕ.le_add_right _ h
  have hsp' : ∀n : ℕ, zero < s' n := fun n => lt_of_lt_le ℕ.zero_lt_one (hs'' n)
  have hs' : ∀n : ℕ, n < s' n := ℕ.rec ℕ.zero_lt_one fun n h => ℕ.lt_of_add_lt_le h (hs'' n)
  have he : ∀n : ℕ, abs (s n) = s0 * ⟨ofNat (s' n), nonzero_of_ofNat_of_pos (hsp' n)⟩⁻¹ := by
    intro n
    induction n
    case _zero =>
      change s0 = s0 * ⟨zero + one, _⟩⁻¹
      conv => enter [2,2,1,1];rw[zero_add]
      rw [inv_of_one, mul_one]
    case succ n hn =>
      conv in ofNat _ => rw [ofNat_add, add_eq_mul_two];
      rw [inv_mul (ne_of_gt (ofNat_of_pos (hsp' n))) two_nonzero, hsi n, half, abs_of_mul_eq_mul_abs, hn, mul_assoc, abs_of_pos one_half_pos]
      rfl
  by_cases s0 = zero
  case pos h0 =>
    exists zero;intros;rw [sub_zero,he,h0,zero_mul]
    exact hε
  case neg h0 =>
    let ε2 := ε * ⟨s0, h0⟩⁻¹
    have h0p : zero < s0 := lt_of_le_ne (abs_nonneg _) (Ne.symm h0)
    have hε2 : zero < ε2 := mul_pos hε (inv_pos_is_pos h0p)
    let ⟨⟨N, hNp⟩, hN⟩ := ℝ.archimedean_inv ε2 hε2
    refine' ⟨N, _⟩
    intro n hn
    rw [sub_zero, he]
    replace hN := lt_of_lt_le (inv_gt_of_pos_lt (ofNat_of_pos hNp) (ofNat_lt_of_lt (lt_of_le_lt hn (hs' n)))) hN
    replace hN := mul_lt_mul_of_pos_left hN h0p
    rw [mul_mul_inv_cancel_left2] at hN
    exact hN

theorem half_pow_conv_to_zero {s : Seq ℝ} (hsi : ∀n : ℕ, s n.succ = half (s n)) : conv_to s zero :=
  abs_half_pow_conv_to_zero fun n => congrArg abs (hsi n)

theorem monotone_convergence_inc : ∀s : Seq ℝ, increasing s → seq_bounded_above s → is_conv s := by
  intro s h h'
  let l0 := s zero
  let r0 := h'.choose
  let s' (n : ℕ) : Σ'(lr' : ℝ × ℝ), (∃N : ℕ, ∀n : ℕ, N ≤ n → lr'.fst ≤ s n) ∧ ∀ n : ℕ, s n ≤ lr'.snd := by
    induction n
    case _zero =>
      refine' ⟨⟨l0, r0⟩, ⟨⟨zero, fun n _ => h _ n (ℕ.zero_le n)⟩, h'.choose_spec⟩⟩
    case succ n hn =>
      let l := hn.fst.fst
      let r := hn.fst.snd
      have hl := hn.snd.left
      have hr := hn.snd.right
      let m := half (l + r)
      by_cases h' : ∃n : ℕ, m ≤ s n
      case pos =>
        refine' ⟨⟨m, r⟩, _, hr⟩
        have ⟨N, hN⟩ := h'
        exists N
        intro n hn
        refine' le_of_le_le hN _
        exact h _ _ hn
      case neg =>
        simp only [not_exists] at h'
        refine' ⟨⟨l, m⟩, hl, fun n => le_of_not_le (h' n)⟩
  have hc := half_pow_conv_to_zero (s:=fun n =>(s' n).fst.snd - (s' n).fst.fst) (by
    intro n
    let l := (s' n).fst.fst
    let r := (s' n).fst.snd
    let m := half (l + r)
    simp only [s']
    by_cases h' : ∃n : ℕ, m ≤ s n
    case pos =>
      rw [dite_cond_eq_true (eq_true h')]
      change r - half (l + r) = half (r - l)
      show r - half (l + r) = half (r - l)
      apply mul_right_inj two_nonzero
      rw [add_mul, half_twice_cancel', mul_neg_left, half_twice_cancel', ←add_eq_mul_two]
      rw [neg_sum, add_left_comm, add_sub_cancel, add_comm]
    case neg =>
      rw [dite_cond_eq_false (eq_false h')]
      change half (l + r) - l = half (r - l)
      apply mul_right_inj two_nonzero
      rw [add_mul, half_twice_cancel', half_twice_cancel', ←add_eq_mul_two]
      rw [add_comm, ←add_assoc, sub_add_cancel, add_comm]
  )
  rw [←ℝ.cauchy_criterion]
  intro ε hε
  let ε2 := half ε
  have hε2 := half_of_pos_is_pos hε
  have ⟨N1, hN1⟩ := hc ε2 hε2
  replace hN1 := hN1 N1 (le_self _)
  let sn := s' N1
  let l := sn.fst.fst
  let r := sn.fst.snd
  have hl := sn.snd.left
  have hr := sn.snd.right
  replace ⟨N, hl⟩ := hl
  exists N
  intro n m hn hm
  have hd : ∀{n : ℕ}, N ≤ n → abs (s n - l) < ε2 := by
    intro n hn
    replace hl := hl n hn
    replace hr := add_le_add_right (-l) (hr n)
    rw [←abs_of_nonneg (sub_nonneg_of_le hl)] at hr
    refine' lt_of_le_le_lt hr (self_le_abs_self _) _
    rw [sub_zero] at hN1
    exact hN1
  have h1 := hd hn
  have h2 := hd hm
  rw [←abs_neg_eq_abs, neg_sub] at h2
  replace h1 := lt_of_le_lt (triangle_add_le_add _ _) (lt_of_add_lt_lt h1 h2)
  rw [←add_assoc, sub_add_cancel, add_half] at h1
  exact h1

theorem monotone_convergence_dec : ∀s : Seq ℝ, decreasing s → seq_bounded_below s → is_conv s :=
  fun s h h' =>
    let s2 := -s
    have h2 : increasing s2 := fun n m hl => neg_le_neg_of_le (h n m hl)
    have h2' : seq_bounded_above s2 := ⟨-h'.choose, fun n => neg_le_neg_of_le (h'.choose_spec n)⟩
    neg_neg s ▸ is_conv_of_neg (monotone_convergence_inc s2 h2 h2')


theorem monotone_convergence : ∀s : Seq ℝ, monotone s → seq_bounded s → is_conv s :=
  fun s h h' => h.elim (monotone_convergence_inc s · (seq_bounded_above_of_bounded h')) (monotone_convergence_dec s · (seq_bounded_below_of_bounded h'))


set_option maxHeartbeats 40000
theorem axiom_of_completeness : ∀S : ℝSet, nonempty S ∧ is_above_bounded S → ∃b, is_supremum b S := by
  intro S ⟨h, h'⟩
  have ⟨l, hl, _⟩ := h
  replace hl : ∃x ∈ S, l ≤ x := ⟨l, hl, le_self _⟩
  have ⟨r, hr⟩ := h'
  let' s (n : ℕ) : Σ'(lr' : ℝ × ℝ), (∃x ∈ S, lr'.fst ≤ x) ∧ is_upperbound lr'.snd S := by
    induction n
    case _zero => exact ⟨⟨l, r⟩, hl, hr⟩
    case succ n hn =>
      have ⟨_, hlr⟩ := hn
      let l := hn.fst.fst
      let r := hn.fst.snd
      have hl := hn.snd.left
      have hr := hn.snd.right
      let m := half (l + r)
      by_cases h' : is_upperbound m S
      case pos =>
        exact ⟨⟨l, m⟩, hl, h'⟩
      case neg =>
        simp only [is_upperbound, not_forall] at h'
        have hl' : ∃x ∈ S, m ≤ x := ⟨h'.choose, ⟨h'.choose_spec.choose, le_of_not_le h'.choose_spec.choose_spec⟩⟩
        exact ⟨⟨m, r⟩, hl', hr⟩
  let s' : Seq ℝ := fun n => (s n).fst.snd
  have hs' : is_conv s' := monotone_convergence_dec s' (by
    intro n m ⟨x, hx⟩
    rw [hx] at *
    induction x
    case _zero => exact le_self _
    case succ x hx' =>
      refine' le_of_le_le _ (hx' rfl)
      rw [ℕ.add_succ]
      generalize n+x = m
      clear hx hx' n x
      let l := (s m).fst.fst
      let r := (s m).fst.snd
      let md := half (l + r)
      simp only [s', s]
      by_cases h' : is_upperbound md S
      case pos =>
        rw [dite_cond_eq_true (eq_true h')]
        change half (l + r) ≤ r
        have hlr : l ≤ r := le_of_le_le (s m).snd.left.choose_spec.right ((s m).snd.right (s m).snd.left.choose (s m).snd.left.choose_spec.left)
        refine' le_of_mul_le_mul_pos_right _ two_pos
        rw [half_twice_cancel', ←add_eq_mul_two]
        exact add_le_add_right _ hlr
      case neg =>
        rw [dite_cond_eq_false (eq_false h')]
        exact le_self _
  ) ⟨hl.choose, fun n => (s n).snd.right _ hl.choose_spec.left⟩
  let b := limit s' hs'
  have hbb : is_upperbound b S := (fun x hx => limit_of_le_const_le _ _ fun n => (s n).snd.right x hx)
  refine' ⟨b, is_supremum_alt hbb _⟩
  intro ε hε
  have hc := half_pow_conv_to_zero (s:=fun n =>(s n).fst.snd - (s n).fst.fst) (by
    intro n
    let l := (s n).fst.fst
    let r := (s n).fst.snd
    let m := half (l + r)
    simp only [s]
    by_cases h' : is_upperbound m S
    case pos =>
      rw [dite_cond_eq_true (eq_true h')]
      change half (l + r) - l = half (r - l)
      apply mul_right_inj two_nonzero
      rw [add_mul, half_twice_cancel', half_twice_cancel', ←add_eq_mul_two]
      rw [add_comm, ←add_assoc, sub_add_cancel, add_comm]
    case neg =>
      rw [dite_cond_eq_false (eq_false h')]
      change r - half (l + r) = half (r - l)
      show r - half (l + r) = half (r - l)
      apply mul_right_inj two_nonzero
      rw [add_mul, half_twice_cancel', mul_neg_left, half_twice_cancel', ←add_eq_mul_two]
      rw [neg_sum, add_left_comm, add_sub_cancel, add_comm]
  )
  let ε2 := half ε
  have hε2 := half_of_pos_is_pos hε
  have ⟨N1, hN1⟩ := conv_to_limit s' hs' ε2 hε2
  have ⟨N2, hN2⟩ := hc ε2 hε2
  let N := max N1 N2
  replace hN1 := hN1 N max_ge_fst
  replace hN2 := hN2 N max_ge_snd
  let sn := s N
  let l := sn.fst.fst
  let r := sn.fst.snd
  have ⟨hl, hr⟩ := sn.snd
  replace ⟨x, ⟨hx, hl⟩⟩ := hl
  refine' ⟨x, ⟨hx, _⟩⟩
  change abs (r - b) < ε2 at hN1
  simp only [sub_zero] at hN2
  change abs (r - l) < ε2 at hN2
  have hrx := hr x hx
  rw [abs_of_nonneg (sub_nonneg_of_le (le_of_le_le hl hrx))] at hN2
  replace hN2 := sub_right_lt_of_lt_add (sub_add_cancel _ _ ▸ lt_of_add_lt_le hN2 hl)
  change r - x < ε2 at hN2
  rw [←abs_of_nonneg (sub_nonneg_of_le hrx)] at hN2
  replace hN1 := lt_of_le_lt (triangle_sub_le_add _ _) (lt_of_add_lt_lt hN2 hN1)
  rw [add_half, neg_sub, add_left_comm, add_comm r, add_sub_cancel] at hN1
  exact hN1






end my
