noncomputable section

def Or.wlog {a b c : Prop} (h : a ∨ b) : (a → c) → ((a → c) → b → c) → c :=
  fun h1 h2 => h.elim h1 (h2 h1)

def Or.wlog_right {a b c : Prop} (h : a ∨ b) : (b → c) → ((b → c) → a → c) → c :=
  fun h1 h2 => h.elim (h2 h1) h1


namespace my



end my
