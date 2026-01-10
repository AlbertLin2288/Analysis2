noncomputable section
namespace my
open Classical

class Zero (α : Type) where
  zero : α

class One (α : Type) where
  one : α

class Add (α : Type) where
  add : α → α → α

class Mul (α : Type) where
  mul : α → α → α

class Sub (α : Type) where
  sub : α → α → α

class Neg (α : Type) where
  neg : α → α

infixl:65(priority := high) " + "   => Add.add
infixl:65(priority := high) " - "   => Sub.sub
infixl:70(priority := high) " * "   => Mul.mul
-- infixl:70(priority := high) " / "   => Div.div
prefix:75(priority := high) "-"     => Neg.neg



-- #check Lean.Meta.Symm.symmExt

end my
