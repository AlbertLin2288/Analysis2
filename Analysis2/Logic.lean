noncomputable section
namespace my
open Classical


def contrapos {p q : Prop} : (p → q) → (¬q → ¬p) :=
  fun h h' h'' => h' (h h'')

def contrapos' {p q : Prop} : (¬p → ¬q) → (q → p) :=
  fun h h' => (em p).resolve_right (h · h')


end my
