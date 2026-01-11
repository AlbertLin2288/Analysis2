import Analysis2.Comp
import Analysis2.Structure
import Analysis2.CompStructure
noncomputable section
namespace my
open Classical
open Comp
open Zero One

section test
inductive N where
| zero' : N
| ofN : Nat → N

namespace N

  -- def add : N → N → N
  -- | zero' zero' => zero'
  -- | zero' (ofNat n) => ofNat n
  abbrev A (a b : Nat) := @HAdd.hAdd Nat Nat Nat instHAdd a b


  @[reducible] instance : Add N where
    add
    | zero', m => m
    | ofN n, zero' => ofN n
    | ofN n, ofN m => ofN (A n m)

  @[reducible] instance : Zero N := ⟨zero'⟩

  theorem h : ∀(a : N), a + zero = a
  | zero' => rfl
  | ofN _ => rfl

  #print h
  theorem h2 : ∀(a : N), zero + a = a
  | zero' => rfl
  | ofN _ => rfl

  #print h2

  @[reducible] instance : Comp N where
    le
    | zero', _ => True
    | ofN _, zero' => False
    | ofN n, ofN m => n.le m
    le_refl
    | zero' => True.intro
    | ofN n => Nat.le_refl n
    le_trans
    | zero', _, _, _, _ => True.intro
    | ofN _, zero', _, h, _ => False.elim h
    | ofN _, ofN _, zero', _, h => False.elim h
    | ofN _, ofN _, ofN _, h, h' => Nat.le_trans h h'
    le_antisymm
    | zero', zero', _, _ => rfl
    | zero', ofN _, _, h => False.elim h
    | ofN _, zero', h, _ => False.elim h
    | ofN _, ofN _, h, h' => congrArg _ (Nat.le_antisymm h h')
    le_total
    | zero', _ => Or.inl True.intro
    | ofN _, zero' => Or.inr True.intro
    | ofN n, ofN m => Nat.le_total n m

  instance : Monoid N where
    add_zero
    | zero' => rfl
    | ofN _ => rfl
    zero_add
    | zero' => rfl
    | ofN _ => rfl
    add_assoc
    | zero', _, _ => rfl
    | ofN _, zero', _ => rfl
    | ofN _, ofN _, zero' => rfl
    | ofN _, ofN _, ofN _ => congrArg _ (Nat.add_assoc _ _ _)

  instance : OrderedMonoid N where
    add_le_add_left {a b : N} := fun c h => match a, b, c, h with
    | zero', zero', _, _ => le_refl _
    | zero', ofN _, zero', _ => True.intro
    | zero', ofN _, ofN _, _ => Nat.le_add_right _ _
    | ofN _, zero', _, h => False.elim h
    | ofN _, ofN _, zero', h => h
    | ofN _, ofN _, ofN _, h => Nat.add_le_add_left h _
    add_le_add_right {a b : N} := fun c h => match a, b, c, h with
    | zero', zero', _, _ => le_refl _
    | zero', ofN _, zero', _ => True.intro
    | zero', ofN _, ofN _, _ => Nat.le_add_left _ _
    | ofN _, zero', _, h => False.elim h
    | ofN _, ofN _, zero', h => h
    | ofN _, ofN _, ofN _, h => Nat.add_le_add_right h _

  instance : OrderedCommMonoid N where
    add_comm
    | zero', zero' => rfl
    | zero', ofN _ => rfl
    | ofN _, zero' => rfl
    | ofN _, ofN _ => congrArg _ (Nat.add_comm _ _)

  instance : One N := ⟨ofN 1⟩

  instance : Mul N where
    mul
    | zero', _ => zero'
    | ofN _, zero' => zero'
    | ofN n, ofN m => ofN (n.mul m)

  instance : SemiRing N where
    mul_one
    | zero' => rfl
    | ofN n => congrArg _ n.mul_one
    one_mul
    | zero' => rfl
    | ofN n => congrArg _ n.one_mul
    mul_assoc
    | zero', _, _ => rfl
    | ofN _, zero', _ => rfl
    | ofN _, ofN _, zero' => rfl
    | ofN _, ofN _, ofN _ => congrArg _ (Nat.mul_assoc _ _ _)
    mul_zero
    | zero' => rfl
    | ofN _ => rfl
    zero_mul := fun _ => rfl
    mul_add
    | zero', _, _ => rfl
    | ofN _, zero', _ => rfl
    | ofN _, ofN _, zero' => rfl
    | ofN _, ofN _, ofN _ => congrArg _ (Nat.mul_add _ _ _)
    add_mul
    | zero', _, _ => rfl
    | ofN _, zero', zero' => rfl
    | ofN _, zero', ofN _ => rfl
    | ofN _, ofN _, zero' => rfl
    | ofN _, ofN _, ofN _ => congrArg _ (Nat.add_mul _ _ _)
    zero_ne_one := N.noConfusion

  instance : OrderedSemiRing N where
    mul_nonneg := fun _ _ => True.intro
    zero_le_one := True.intro

  instance : CommSemiRing N where
    mul_comm
    | zero', zero' => rfl
    | zero', ofN _ => rfl
    | ofN _, zero' => rfl
    | ofN _, ofN _ => congrArg _ (Nat.mul_comm _ _)

  instance : OrderedCommSemiRing N where


  @[reducible] def add_le_add_iff_right := ∀ {a b : N}, ∀(c : N), a + c ≤ b + c ↔ a ≤ b

  example : ¬add_le_add_iff_right := by
    simp only [not_forall]
    exists (ofN 0), zero', (ofN 0)
    intro ⟨h, _⟩
    have h' : ofN 0 + ofN 0 ≤ zero' + ofN 0 := by
      unfold le
      simp only [Nat.add_zero]
      exact Nat.le_refl _
    exact h h'

  @[reducible] def add_left_inj := ∀{a b : N}, ∀ (c : N), a + c = b + c → a = b

  example : ¬add_left_inj := by
    simp only [not_forall]
    exists (ofN 0), zero', ofN 0
    refine' ⟨_, _⟩
    rfl
    exact N.noConfusion

#check N.noConfusionType
end N

end test
end my
