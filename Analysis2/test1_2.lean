import Analysis2.CompStructure.CompStructure
noncomputable section
namespace my
open Classical
open Comp
open Zero One


inductive N where
| z : N
| o : N

namespace N

  instance : Zero N where
    zero := z

  instance : Add N where
    add
    | z, z => z
    | o, _ => o
    | _, o => o

  instance : Comp N where
    le
    | z, _ => True
    | o, z => False
    | o, o => True
    le_refl
    | z => True.intro
    | o => True.intro
    le_trans
    | z, _, _ => fun _ _ => True.intro
    | o, _, o => fun _ _ => True.intro
    | o, o, z => fun _ h => h.elim
    | o, z, z => fun h _ => h.elim
    le_antisymm
    | z, z => fun _ _ => rfl
    | o, o => fun _ _ => rfl
    | z, o => fun _ h => h.elim
    | o, z => fun h _ => h.elim
    le_total
    | z, _ => Or.inl True.intro
    | o, z => Or.inr True.intro
    | o, o => Or.inr True.intro

  instance : One N where
    one := o

  instance : Mul N where
    mul
    | z, _ => z
    | _, z => z
    | o, o => o

  instance : CommMonoid N where
    _add_zero
    | z => rfl
    | o => rfl
    _add_assoc
    | z, z, z => rfl
    | z, z, o => rfl
    | z, o, _ => rfl
    | o, _, _ => rfl
    add_comm
    | z, z => rfl
    | z, o => rfl
    | o, z => rfl
    | o, o => rfl


  instance : CommSemiRing N where
    _mul_one | o => rfl | z => rfl
    _mul_assoc
    | z, _, _ => rfl
    | o, z, _ => rfl
    | o, o, z => rfl
    | o, o, o => rfl
    _mul_zero |z=>rfl|o=>rfl
    _add_mul
    | z, z, z => rfl
    | z, z, o => rfl
    | z, o, z => rfl
    | z, o, o => rfl
    | o, z, z => rfl
    | o, z, o => rfl
    | o, o, z => rfl
    | o, o, o => rfl
    _zero_ne_one := N.noConfusion
    mul_comm
    | z, z => rfl
    | z, o => rfl
    | o, z => rfl
    | o, o => rfl

  instance : OrderedCommMonoid N where
    _add_le_add_left := fun {a b} c h => match a, b, c, h with
    | _, _, o, _ => True.intro
    | z, z, z, _ => True.intro
    | z, o, z, _ => True.intro
    | o, z, _, h => h.elim
    | o, o, z, _ => True.intro

  instance : OrderedCommSemiRing N where
    _mul_le_mul_of_nonneg_right := fun {a b c} h _ => match a,b,c,h with
    | z, _, _, _ => True.intro
    | o, _, z, _ => True.intro
    | o, z, o, h => h.elim
    | o, o, o, _ => True.intro
    _zero_le_one := True.intro

  open OrderedCommSemiRing
  open CommSemiRing
  open OfNat

  def le_of_ofNat_le := ∀(n m : ℕ), ofNat' N n ≤ ofNat m → n ≤ m

  example : ¬le_of_ofNat_le :=
    fun h => not_le_of_lt ℕ._one.lt_succ (h ℕ.num.two one True.intro)

end N
end my
