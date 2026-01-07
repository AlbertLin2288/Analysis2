noncomputable section
namespace my

universe u

axiom True : Prop
macro "⊤" : term => `(True)

axiom True.intro : True

-- macro "⊤.intro" : term => `(True.intro)
-- macro "⊤." x:term : term => `(True$x)

axiom False : Prop
macro "⊥" : term => `(False)

axiom False.elim {hf : ⊥} (p : Prop) : p

theorem imp_true (p : Prop) {q : Prop} (hq : q) : p → q := fun _ => hq

theorem false_imp (p : Prop) : ⊥ → p := fun hf => hf.elim p

theorem imp_imp_ord {p q r : Prop} (h : p → q → r) : q → p → r :=
  fun hq hp => h hp hq

def Not (p : Sort u) : Prop := p → ⊥

notation:max (priority := high) "¬" p:40 => Not p

def Nand (p q : Prop) : Prop := p → q → ⊥

def And (p q : Prop) : Prop := Not (Nand p q)

infixr:35 (priority := high) " ∧ " => And

def Or (p q : Prop) : Prop := Nand (¬p) (¬q)

infixr:30 (priority := high) " ∨  "  => Or

def Or.inl {p : Prop} (q : Prop) (hp : p) : p ∨ q :=
  fun hnp _ => hnp hp

def Or.inr (p : Prop) {q : Prop} (hq : q) : p ∨ q :=
  fun _ hnq => hnq hq

theorem Nand.swap {p q : Prop} (hpq : Nand p q) : Nand q p :=
  fun hq hp => hpq hp hq

def And.intro {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  fun h => h hp hq

theorem And.swap {p q : Prop} (hpq : p ∧ q) : q ∧ p :=
  fun hqp => hpq hqp.swap

theorem em {p : Prop} : p ∨ ¬p :=
  fun hnp hnnp => hnnp hnp

axiom dne {p : Sort u} : ¬¬p → p

theorem And.right {p q : Prop} (hpq : p ∧ q) : q :=
  dne (fun hnq => hpq (fun _ hq => hnq hq))

theorem And.left {p q : Prop} (hpq : p ∧ q) : p :=
  And.right hpq.swap

def Or.elim {p q: Prop} (hpq : p ∨ q) {r : Sort u} (fp : p → r) (fq : q → r) : r :=
  dne (fun hnr => hpq (fun hp => hnr (fp hp)) (fun hq => hnr (fq hq)))

-- def Forall {α : Sort u} (p : α → Prop) : Prop := p

-- def Exists {α : Sort u} (p : α → Prop) (a : α) : Prop := p a
def Exists {α : Sort u} (p : α → Prop) (a : α) := p
def Forall {α : Sort u} (p : α → Prop) : Prop := p
section
open Lean.TSyntax.Compat
macro (priority := high) "∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``Exists xs b
macro (priority := high) "∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``Forall xs b
end

#check ∃a : Nat, a = 1
#check ∀a : Nat, a = 1

example (h : ∃a : Nat, a = 1):0=1 :=
  h 0

-- example : \

-- def Exists {α : Sort u} (p : α → Prop) : Prop :=

class Eq (α : Type u) where
  eq : α → α → Prop
  refl : ∀(a : α), eq a a
  symm : ∀(a b : α), eq a b → eq b a
  trans : ∀(a b c : α), eq a b → eq b c → eq a c

attribute [refl] Eq.refl

infix:50 (priority := high) " = "  => Eq.eq

-- axiom from_exists {α : Sort u} {p : α → Prop} : (∃(a : α), p a) → Σ (a : α), p a

end my
#check Exists
