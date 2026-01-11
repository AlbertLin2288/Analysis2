import Analysis2.Comp
import Analysis2.Operator
import Analysis2.Structure
import Analysis2.CompStructure

namespace my
open Classical
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing
open Comp
open Zero One
open OrderedMonoid OrderedCommMonoid OrderedCommGroup OrderedSemiRing OrderedCommSemiRing OrderedCommRing

instance : Comp Int where
  le := Int.le
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_total := Int.le_total
  le_antisymm := @Int.le_antisymm

instance : Zero Int where
  zero := 0

instance : One Int where
  one := 1

instance : Add Int where
  add := Int.add

instance : Neg Int where
  neg := Int.neg

instance : Mul Int where
  mul := Int.mul

instance : CommMonoid Int where
  _add_zero := Int.add_zero
  _add_assoc := Int.add_assoc
  add_comm := Int.add_comm

instance : CommSemiRing Int where
  _mul_one := Int.mul_one
  _mul_assoc := Int.mul_assoc
  _mul_zero := Int.mul_zero
  _add_mul := Int.add_mul
  _zero_ne_one := Int.zero_ne_one
  mul_comm := Int.mul_comm

instance : CommGroup Int where
  add_neg := Int.add_right_neg

instance : CommRing Int where

instance : OrderedCommMonoid Int where
  _add_le_add_left := fun c h => Int.add_le_add_left h c

instance : OrderedCommGroup Int where

instance : OrderedCommRing Int where
  mul_nonneg := Int.mul_nonneg
  _zero_le_one := Int.le_of_lt Int.zero_lt_one

theorem lt_def {a b : Int} : a < b ↔ a.lt b := Int.not_le


def Z2 := Int × Int


instance : Comp Z2 where
  le := fun ⟨a, a'⟩ ⟨b, b'⟩ => a < b ∨ a = b ∧ a' ≤ b'
  le_refl := fun _ => Or.inr ⟨rfl, le_refl _⟩
  le_trans := fun _ _ _ h h' =>
    h.elim
      (fun h => Or.inl (h'.elim (lt_trans h ·) (·.left.subst h)))
      (fun h => h'.elim (fun h' => Or.inl (h.left.substr h'))
        (fun h' => Or.inr ⟨h.left.substr h'.left, le_of_le_le h.right h'.right⟩))
  le_antisymm := fun _ _ h h' => h.elim
    (fun h => False.elim (h'.elim (not_lt_of_lt h ·) (ne_of_lt h ·.left.symm)))
    (fun h => h'.elim (fun h' => (ne_of_lt h' h.left.symm).elim)
      (fun h' => Prod.ext h.left (le_antisymm _ _ h.right h'.right)))
  le_total := fun _ _ => (lt_or_eq_or_gt _ _).elim
    (fun h => Or.inl (Or.inl h)) (·.elim
    (fun h => (le_or_ge _ _).elim
      (fun h' => Or.inl (Or.inr ⟨h, h'⟩))
      (fun h' => Or.inr (Or.inr ⟨h.symm, h'⟩)))
    (fun h => Or.inr (Or.inl h)))


instance : Zero Z2 := ⟨⟨zero, zero⟩⟩

instance : One Z2 := ⟨⟨one, zero⟩⟩

instance : Add Z2 where
  add := fun ⟨a1, a2⟩ ⟨b1, b2⟩ => ⟨a1 + b1, a2 + b2⟩

theorem add_def {a b : Z2} : a + b = ⟨a.fst + b.fst, a.snd + b.snd⟩ := rfl

instance : Neg Z2 where
  neg := fun ⟨a1, a2⟩ => ⟨-a1, -a2⟩

instance : Mul Z2 where
  mul := fun ⟨a1, a2⟩ ⟨b1, b2⟩ => ⟨a1 * b1, a1 * b2 + a2 * b1⟩

theorem mul_def {a b : Z2} : a * b = ⟨a.fst * b.fst, a.fst * b.snd + a.snd * b.fst⟩ := rfl

instance : CommMonoid Z2 where
  _add_zero := fun _ => Prod.ext (add_zero _) (add_zero _)
  _add_assoc := fun _ _ _ => Prod.ext (add_assoc _ _ _) (add_assoc _ _ _)
  add_comm := fun _ _ => Prod.ext (add_comm _ _) (add_comm _ _)

instance : CommSemiRing Z2 where
  _mul_one := fun a => Prod.ext (mul_one _) ((mul_one _).substr (p := (_*_+·=_)) ((mul_zero _).substr (zero_add _)))
  _mul_assoc := fun _ _ _ => Prod.ext (mul_assoc _ _ _) (by simp only [mul_def, add_mul, mul_add];ac_nf)
  _mul_zero := fun a => Prod.ext (mul_zero _) ((add_mul a.fst a.snd zero).subst (motive:=(·=zero)) (mul_zero (a.fst + a.snd))) -- ((mul_zero a.snd).substr (add_zero (a.fst * zero)))
  _add_mul := fun a b c => Prod.ext (add_mul _ _ _) (by simp only [mul_def, add_def, add_mul];ac_nf)
  _zero_ne_one := fun h => zero_ne_one (Prod.mk.inj h).left
  mul_comm := fun a b => Prod.ext (mul_comm _ _) (by simp only [mul_def];ac_nf)

instance : CommGroup Z2 where
  add_neg := fun _ => Prod.ext (add_neg _) (add_neg _)

instance : CommRing Z2 where

instance : OrderedCommMonoid Z2 where
  _add_le_add_left := fun _ h => h.elim (fun h => Or.inl (add_lt_add_left _ h)) (fun ⟨h, h'⟩ => Or.inr ⟨congrArg _ h, add_le_add_left _ h'⟩)

instance : OrderedCommGroup Z2 where

instance : OrderedCommRing Z2 where
  _zero_le_one := Or.inl zero_lt_one
  mul_nonneg {a b} :=
  by
    intro h h'
    simp only [Comp.le, Mul.mul, Int.mul_def, lt_def, Add.add, Int.add_def] at *
    cases h
    all_goals cases h'
    all_goals
      simp only [@id (zero = (0 : Int)) rfl] at *
    case inl.inl h h' =>
      apply Or.inl
      refine' Int.mul_pos h h'
    case inl.inr h h' =>
      apply Or.inr
      refine' ⟨_, _⟩
      all_goals rw [← h'.left, Int.mul_zero]
      simp only [Int.add_zero]
      exact Int.mul_nonneg (Int.le_of_lt h) h'.right
    case inr.inl h h' =>
      refine' Or.inr ⟨_, _⟩
      all_goals rw [← h.left, Int.zero_mul]
      simp only [Int.zero_add]
      exact Int.mul_nonneg h.right (Int.le_of_lt h')
    case inr.inr h h' =>
      refine' Or.inr ⟨_, _⟩
      all_goals simp only [← h.left, ← h'.left, Int.mul_zero, Int.zero_mul]
      simp only [Int.zero_add]
      exact Int.le_refl _

def mul_pos := ∀(a b : Z2), a > zero → b > zero → a * b > zero

def mul_eq_zero := ∀(a b : Z2), a * b = zero → a = zero ∨ b = zero

example : mul_pos → mul_eq_zero := by
  unfold mul_pos mul_eq_zero
  apply contrapos'
  simp only [not_forall]
  intro ⟨a, ⟨b, ⟨h, h'⟩⟩⟩
  have ⟨ha, hb⟩ := not_or.mp h'
  replace ⟨a, ha, h⟩ : ∃(a : Z2), a > zero ∧ (a * b = zero) := by
    refine' (lt_or_eq_or_gt a zero).elim _ (·.elim (fun h'' => (ha h'').elim) _)
    intro ha
    replace h : (-a) * b = zero := by rw [mul_neg_left, h, neg_zero]
    replace ha : zero < -a := by rwa [← neg_zero, neg_lt_neg_iff]
    exact ⟨-a, ha, h⟩
    intro ha; exact ⟨a, ha, h⟩
  replace ⟨b, hb, h⟩ : ∃(b : Z2), b > zero ∧ (a * b = zero) := by
    refine' (lt_or_eq_or_gt b zero).elim _ (·.elim (fun h'' => (hb h'').elim) _)
    intro hb
    replace h : a * (-b) = zero := by rw [mul_neg_right, h, neg_zero]
    replace hb : zero < -b := by rwa [← neg_zero, neg_lt_neg_iff]
    exact ⟨-b, hb, h⟩
    intro hb; exact ⟨b, hb, h⟩
  refine' ⟨a, b, ha, hb, _⟩
  rw [h]
  exact not_lt_self _

example : ¬mul_eq_zero := by
  unfold mul_eq_zero
  simp only [not_forall]
  exists ⟨zero, one⟩, ⟨zero, one⟩
  refine' ⟨_, _⟩
  refine' Prod.ext (mul_zero _) _
  simp only [mul_def, mul_zero, zero_mul, zero_add]
  rfl
  simp only [not_or]
  refine ⟨?a, ?a⟩
  intro h
  exact zero_ne_one.symm (Prod.mk.inj h).right


end my
