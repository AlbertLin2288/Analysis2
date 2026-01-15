import Analysis2.Structure.CommMonoid
import Analysis2.CompStructure.OrderedMonoid
noncomputable section
namespace my
open Classical
open Comp
open Zero One
open Monoid CommMonoid
open OrderedMonoid



class OrderedCommMonoid (α : Type) [Zero α] [Add α] [Comp α] [CommMonoid α] where
  _add_le_add_left {a b : α} (c : α) : a ≤ b → c + a ≤ c + b

namespace OrderedCommMonoid

  open Monoid CommMonoid
  open OrderedMonoid
  variable {α : Type} [Zero α] [Add α] [Comp α] [CommMonoid α] [OrderedCommMonoid α]

  theorem _add_le_add_right {a b : α} (c : α) : a ≤ b → a + c ≤ b + c := by
    intro h
    simp only [add_comm _ c, _add_le_add_left c h]

  @[default_instance] instance : OrderedMonoid α := ⟨_add_le_add_left, _add_le_add_right⟩

end OrderedCommMonoid

end my
