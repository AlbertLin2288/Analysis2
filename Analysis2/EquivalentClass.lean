noncomputable section
namespace my
open Classical

-- #check eqv

structure EquivalentClass.{u} {α : Sort u} (R : α → α → Prop) where
  S : α → Prop
  isEqv : Equivalence R
  p : ∃(a : α), S a ∧ (∀(b : α), S b ↔ R a b)

namespace EquivalentClass

  universe u
  variable {α : Sort u}-- (R : α → α → Prop) (eqv : Equivalence R)

  -- def from_elm (a : α) : EquivalentClass R eqv := by
  --   apply PSigma.mk
  --   case fst => exact R a
  --   case snd =>
  --     exact ⟨_, And.intro (eqv.refl _) fun _ => Iff.refl _⟩
  def from_elm {R : α → α → Prop} (eqv : Equivalence R) (a : α) : EquivalentClass R :=
    EquivalentClass.mk (R a) eqv ⟨_, And.intro (eqv.refl _) fun _ => Iff.refl _⟩

  def is_member (a : α) {R : α → α → Prop} (S : EquivalentClass R) : Prop := S.S a

  theorem has_member {R : α → α → Prop} (S : EquivalentClass R) : ∃(a : α), is_member a S :=
    Exists.intro S.p.choose S.p.choose_spec.left

  theorem member_related {R : α → α → Prop} (S : EquivalentClass R) : ∀(a b : α), is_member a S ∧ is_member b S → R a b :=
    fun a b ⟨ha, hb⟩ => S.isEqv.trans (S.isEqv.symm ((S.p.choose_spec.right a).mp ha)) ((S.p.choose_spec.right b).mp hb)

  theorem is_member_of_from_elm (a : α) {R : α → α → Prop} (eqv : Equivalence R) : is_member a (from_elm eqv a) :=
    eqv.refl a

  theorem from_elm_of_is_member {R : α → α → Prop} (S : EquivalentClass R) : ∀(a : α), is_member a S → S = (from_elm S.isEqv a) :=
    fun a ha =>
      (mk.injEq S.S S.isEqv S.p (R a) S.isEqv _).mpr
        (funext fun c => propext
          (Iff.trans
            (S.p.choose_spec.right c)
            ⟨
              (S.isEqv.trans (S.isEqv.symm ((S.p.choose_spec.right a).mp ha)) .),
              (S.isEqv.trans ((S.p.choose_spec.right a).mp ha) .)
            ⟩
          )
        )


  def sys_of_repr' {R : α → α → Prop} : Σ'(f : EquivalentClass R → α), ∀(S : EquivalentClass R), is_member (f S) S :=
    PSigma.mk (fun S => S.has_member.choose) (fun S => S.has_member.choose_spec)

  def sys_of_repr {R : α → α → Prop} : EquivalentClass R → α := sys_of_repr'.fst

  theorem sys_of_repr_spec {R : α → α → Prop} : ∀(S : EquivalentClass R), is_member (sys_of_repr S) S := sys_of_repr'.snd

  theorem from_sys_of_repr {R : α → α → Prop} : ∀(S : EquivalentClass R), S = from_elm S.isEqv (sys_of_repr S) :=
    (from_elm_of_is_member _ _ ·.sys_of_repr_spec)

  theorem sound {R : α → α → Prop} (eqv : Equivalence R) {a b : α} : R a b → from_elm eqv a = from_elm eqv b :=
    fun h => (mk.injEq (R a) eqv _ (R b) eqv _).mpr (funext fun _ => Eq.propIntro (fun h' => eqv.trans (eqv.symm h) h') (fun h' => eqv.trans h h'))

  theorem sound_inv {R : α → α → Prop} (eqv : Equivalence R) {a b : α} : from_elm eqv a = from_elm eqv b → R a b :=
    fun h => member_related (from_elm eqv a) a b ⟨is_member_of_from_elm a eqv, h.substr (is_member_of_from_elm b eqv)⟩

  theorem sound' {R : α → α → Prop} (eqv : Equivalence R) {S1 S2 : EquivalentClass R}  {a b : α} (ha : is_member a S1) (hb : is_member b S2) : R a b → S1 = S2 :=
    fun h' => (from_elm_of_is_member S2 b hb).substr ((from_elm_of_is_member S1 a ha).substr (sound eqv h'))

  theorem sound_inv' {R : α → α → Prop} {S1 S2 : EquivalentClass R}  {a b : α} (ha : is_member a S1) (hb : is_member b S2) : S1 = S2 → R a b :=
    fun h => member_related S2 _ _ ⟨h.subst ha, hb⟩

  set_option linter.unusedVariables false in
  def lift.{v} {R : α → α → Prop} (eqv : Equivalence R) {β : Sort v} (f : α → β) (h : ∀ (a b : α), R a b → f a = f b) : EquivalentClass R → β :=
    fun S => f (sys_of_repr S)

  -- theorem lift_spec.{v} {R : α → α → Prop} {eqv : Equivalence R} {β : Sort v} {f : α → β} {h : ∀ (a b : α), R a b → f a = f b} : ∀(a : α), lift eqv f h (from_elm eqv a) = f a :=
  --   fun a => h _ _ (member_related (from_elm eqv a) (from_elm eqv a).sys_of_repr a ⟨sys_of_repr_spec (from_elm eqv a), is_member_of_from_elm a (from_elm eqv a).isEqv⟩)
  theorem lift_spec.{v} {R : α → α → Prop} {β : Sort v} {f : α → β} {h : ∀ (a b : α), R a b → f a = f b} (S : EquivalentClass R) : ∀(a : α), is_member a S → lift S.isEqv f h S = f a :=
    fun a h' => h _ _ (member_related S S.sys_of_repr a ⟨S.sys_of_repr_spec, h'⟩)

  -- set_option linter.unusedVariables false in
  -- def hlift.{v} {R : α → α → Prop} (eqv : Equivalence R) {β : α → Sort v} (f : (a : α) → β a) (h : ∀ (a b : α), R a b → f a ≍ f b) : EquivalentClass R → β :=
  --   fun S => f (sys_of_repr S)

  -- theorem hlift_spec.{v} {R : α → α → Prop} {β : α → Sort v} {f : (a : α) → β a} {h : ∀ (a b : α), R a b → f a ≍ f b} (S : EquivalentClass R) : ∀(a : α), is_member a S → hlift S.isEqv f h S = f a :=
  --   fun a h' => eq_of_heq (h _ _ (member_related S S.sys_of_repr a ⟨S.sys_of_repr_spec, h'⟩))

-- #check Quotient

--   def lift2.{v} {R : α → α → Prop} (eqv : Equivalence R) {β : Sort v} (f : α → α → β) (h : ∀ (a1 a2 b1 b2 : α), R a1 a2 → R b1 b2 → f a1 b1 = f a2 b2) : EquivalentClass R → EquivalentClass R → β :=
--     -- have h : ∀(a1 a2 : α), R a1 a2 → f a1 = f a2 := fun a1 a2 h' => funext fun b => h a1 a2 b b h' (eqv.refl b)
--     have h2 : ∀(a b1 b2 : α), R b1 b2 → f a b1 = f a b2 := fun a b1 b2 h' => h a a b1 b2 (eqv.refl a) h'
--     have f' : α → EquivalentClass R → β := lift f h2
--     have h1 : ∀(a1 a2 : α), R a1 a2 → f' a1 = f' a2 := fun a1 a2 h' => funext fun S =>
--     fun S1 S2 =>
-- #check Quotient.pliftOn

end EquivalentClass
-- axiom α : Type
-- axiom R : α→α→Prop
-- axiom e1 : Equivalence R
-- axiom e2 : Equivalence R
-- example :e1=e2 := rfl

-- section EquivalentClass


-- end EquivalentClass

end my
