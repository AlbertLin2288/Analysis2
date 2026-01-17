noncomputable section
namespace my
open Classical

class Zero (α : Type) where
  zero : α

class One (α : Type) where
  one : α

class Add (α : Type) where
  add : α → α → α

class Max (α : Type) where
  max : α → α → α

class Min (α : Type) where
  min : α → α → α

class Mul (α : Type) where
  mul : α → α → α

-- class Sub (α : Type) where
--   sub : α → α → α

class Neg (α : Type) where
  neg : α → α

class Abs (α : Type) where
  abs : α → α

class Inv (α : Type) [Zero α] where
  inv : (Σ'(a : α), a ≠ Zero.zero) → α

infixl:65(priority := high) " + "   => Add.add
prefix:75(priority := high) "-"     => Neg.neg
notation:65 (priority := high) lhs:65 " - " rhs:66 => lhs + -rhs
-- infixl:65(priority := high) " - "   => Sub.sub

infixl:70(priority := high) " * "   => Mul.mul
-- infixl:70(priority := high) " / "   => Div.div
postfix:max (priority := high) "⁻¹" => Inv.inv

end my
