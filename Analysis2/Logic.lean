noncomputable section

namespace Or

  universe u

  private def elim'_aux (a b : Prop) (c : Sort u) (h : a ∨ b) (f : a → c) (f' : b → c) : ∃(ic : c), (∀{p : c → Prop} (_:(ha' : a) → p (f ha')) (_:(hb' : b) → p (f' hb')), p ic) :=
    h.elim (fun x => ⟨f x, fun ha _ => ha x⟩) (fun x => ⟨f' x, fun _ hb => hb x⟩)

  def elim' {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) : c := (elim'_aux a b c h f f').choose

  def elim'_spec {a b : Prop} {c : Sort u} {h : a ∨ b} {f : a → c} {f' : b → c} {p : c → Prop} (ha : (ha' : a) → p (f ha')) (hb : (hb' : b) → p (f' hb')) : p (elim' h f f') := (elim'_aux a b c h f f').choose_spec ha hb

end Or

namespace my
open Classical


def contrapos {p q : Prop} : (p → q) → (¬q → ¬p) :=
  fun h h' h'' => h' (h h'')

def contrapos' {p q : Prop} : (¬p → ¬q) → (q → p) :=
  fun h h' => (em p).resolve_right (h · h')



  -- def e2.{u} {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) :=
  --   -- Exists.choose (h.elim (c := ∃(_:c), True) (⟨f ·, True.intro⟩) (⟨f' ·, True.intro⟩))
  --   (h.elim (c:=∃_,True) (⟨f ·, True.intro⟩) (⟨f' ·, True.intro⟩)).choose
  -- section
  --   universe u


    -- @[reducible] def e2'_t2 (a b : Prop) (c : Sort u) (f : a → c) (f' : b → c) (ic : c) := (∀{p : c → Prop} (_:(ha' : a) → p (f ha')) (_:(hb' : b) → p (f' hb')), p ic)

    -- -- @[reducible] def e2'_t

    -- def e2' {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) : Σ'(ic : c), e2'_t2 a b c f f' ic :=
    --   have x := (h.elim (c:=∃ic:c,e2'_t2 a b c f f' ic) (fun x => ⟨f x, fun ha _ => ha x⟩) (fun x => ⟨f' x, fun _ hb => hb x⟩))
    --   ⟨x.choose, x.choose_spec⟩

    -- def e2 {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) : c := (e2' h f f').fst

    -- def e2s {a b : Prop} {c : Sort u} {h : a ∨ b} {f : a → c} {f' : b → c} {p : c → Prop} (ha : (ha' : a) → p (f ha')) (hb : (hb' : b) → p (f' hb')) : p (e2 h f f') := (e2' h f f').snd ha hb


    -- @[reducible] def e2'_t

  --   @[reducible] def e2'_t2 (a b : Prop) (c : Sort u) (f : a → c) (f' : b → c) (ic : c) := (∀{p : c → Prop} (_:(ha' : a) → p (f ha')) (_:(hb' : b) → p (f' hb')), p ic)
  --   def e2' {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) : ∃(ic : c), e2'_t2 a b c f f' ic :=
  --     (h.elim (c:=∃ic:c,e2'_t2 a b c f f' ic) (fun x => ⟨f x, fun ha _ => ha x⟩) (fun x => ⟨f' x, fun _ hb => hb x⟩))

  --   def e2 {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) : c := (e2' h f f').choose

  --   def e2s {a b : Prop} {c : Sort u} {h : a ∨ b} {f : a → c} {f' : b → c} {p : c → Prop} (ha : (ha' : a) → p (f ha')) (hb : (hb' : b) → p (f' hb')) : p (e2 h f f') := (e2' h f f').choose_spec ha hb

  -- end section
  -- def e2'.{u} {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c) : Σ'(ic : c), (∀{p : c → Prop} (ha : (ha' : a) → p (f ha')) (hb : (hb' : b) → p (f' hb')), p ic) :=
  --   -- Exists.choose (h.elim (c := ∃(_:c), True) (⟨f ·, True.intro⟩) (⟨f' ·, True.intro⟩))
  --   have x := (h.elim (c:=∃_,(ic:c) → (∀{p : c → Prop} (ha : (ha' : a) → p (f ha')) (hb : (hb' : b) → p (f' hb')), p ic)) (⟨f ·, sorry⟩) (⟨f' ·, sorry⟩))
  --   ⟨x.choose, x.choose_spec x.choose⟩
  -- def er.{u} {a b : Prop} {c : Sort u} (h : a ∨ b) (f : a → c) (f' : b → c)

#check Sort 0

  -- set_option pp.proofs true
  -- def e2'.{u} {a b : Prop} {c : Sort u} {h : a ∨ b} {f : a → c} {f' : b → c} {p : c → Prop} (ha : (ha' : a) → p (f ha')) (hb : (hb' : b) → p (f' hb')) : p (e2 h f f') :=
  --   by
  --     unfold e2
    --sorry-- (g : a → (f av) → p) : p :=

    -- Exists.choose (h.elim (c := ∃(_:c), True) (⟨f ·, True.intro⟩) (⟨f' ·, True.intro⟩))
    -- (h.elim (c:=∃_,True) (⟨f ·, True.intro⟩) (⟨f' ·, True.intro⟩)).choose_spec


end my
