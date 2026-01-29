import Analysis2.Structure.CommRing
noncomputable section
namespace my
open Classical
open Zero One
open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing'


class Field (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [CommMonoid α] [CommGroup α] [CommRing α] where
  mul_inv_cancel {a : α} : (h0 : a ≠ zero) → a * ⟨a, h0⟩⁻¹ = one

namespace Field
  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing CommRing'
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [CommMonoid α] [CommGroup α] [CommRing α] [Field α]

  theorem inv_of_one : ⟨(one : α), zero_ne_one.symm⟩⁻¹ = one :=
    one_mul ⟨(one : α), one_ne_zero⟩⁻¹ ▸ mul_inv_cancel one_ne_zero

  theorem inv_nonzero {a : α} (ha : a ≠ zero) : ⟨a, ha⟩⁻¹ ≠ zero :=
    fun h => zero_ne_one (mul_zero a ▸ h ▸ mul_inv_cancel ha)

  theorem inv_mul_cancel {a : α} : (h : a ≠ zero) → ⟨a, h⟩⁻¹ * a = one :=
    fun h => (mul_comm a ⟨a, h⟩⁻¹) ▸ (mul_inv_cancel h)

  theorem mul_inv_mul_cancel_right {a b : α} (h : b ≠ zero) : (a * ⟨b, h⟩⁻¹) * b = a := by
    rw [mul_assoc, inv_mul_cancel , mul_one]

  theorem mul_inv_mul_cancel_left {a b : α} (h : a ≠ zero) : a * (⟨a, h⟩⁻¹ * b) = b := by
    rw [←mul_assoc, mul_inv_cancel, one_mul]

  theorem mul_mul_inv_cancel_right {a b : α} (h : b ≠ zero) : (a * b) * ⟨b, h⟩⁻¹ = a := by
    rw [mul_assoc, mul_inv_cancel, mul_one]

  theorem mul_mul_inv_cancel_left1 {a b : α} (h : a ≠ zero) : (a * b) * ⟨a, h⟩⁻¹ = b := by
    rw [mul_right_comm, mul_inv_cancel, one_mul]

  theorem mul_mul_inv_cancel_left2 {a b : α} (h : a ≠ zero) : a * (b * ⟨a, h⟩⁻¹) = b := by
    rw [mul_left_comm, mul_inv_cancel, mul_one]

  theorem _mul_eq_zero {a b : α} : a * b = zero → a = zero ∨ b = zero := by
    intro h
    apply byContradiction _
    intro h'
    replace h' := not_or.mp h'
    replace h := congrArg (.*⟨b,h'.right⟩⁻¹*⟨a,h'.left⟩⁻¹) h
    simp only [zero_mul, mul_mul_inv_cancel_right, mul_inv_cancel] at h
    exact zero_ne_one h.symm

  @[default_instance] instance : CommRing' α where
    mul_eq_zero := _mul_eq_zero

  theorem mul_left_inj {a b c : α} (hc : c ≠ zero) : c * a = c * b → a = b :=
    fun h => (mul_mul_inv_cancel_left1 (b:=b) hc ▸ mul_mul_inv_cancel_left1 (b:=a) hc ▸ congrArg (·*⟨c,hc⟩⁻¹) h)

  theorem mul_right_inj {a b c : α} (hc : c ≠ zero) : a * c = b * c → a = b :=
    fun h => (mul_mul_inv_cancel_right (a:=b) hc ▸ mul_mul_inv_cancel_right (a:=a) hc ▸ congrArg (·*⟨c,hc⟩⁻¹) h)

  theorem inv_neg (a : α) (ha : a ≠ zero) : ⟨-a, neg_nonzero ha⟩⁻¹ = -⟨a, ha⟩⁻¹ :=
    mul_left_inj (neg_nonzero ha) (mul_neg_both a ⟨a,ha⟩⁻¹ ▸ mul_inv_cancel ha ▸ (mul_inv_cancel (neg_nonzero ha)))

  theorem inv_inv {a : α} (ha : a ≠ zero) : ⟨⟨a, ha⟩⁻¹, inv_nonzero ha⟩⁻¹ = a := by
    refine' mul_right_inj (inv_nonzero ha) _
    rw [mul_inv_cancel,inv_mul_cancel]

  theorem inv_mul_rev {a b : α} (ha : a ≠ zero) (hb : b ≠ zero) : ⟨a * b, mul_nonzero_nonzero ha hb⟩⁻¹ = ⟨b, hb⟩⁻¹ * ⟨a, ha⟩⁻¹ := by
    refine' mul_right_inj (mul_nonzero_nonzero ha hb) _
    rw [inv_mul_cancel, ←mul_assoc, mul_inv_mul_cancel_right, inv_mul_cancel]

  theorem inv_mul {a b : α} (ha : a ≠ zero) (hb : b ≠ zero) : ⟨a * b, mul_nonzero_nonzero ha hb⟩⁻¹ = ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := by
    rw [inv_mul_rev, mul_comm]

  theorem inv_mul_rev' {a b : α} (hab : a * b ≠ zero) : ⟨a * b, hab⟩⁻¹ = ⟨b, right_nonzero_of_mul_nonzero _ _ hab⟩⁻¹ * ⟨a, left_nonzero_of_mul_nonzero _ _ hab⟩⁻¹ :=
    inv_mul_rev (left_nonzero_of_mul_nonzero _ _ hab) (right_nonzero_of_mul_nonzero _ _ hab)

  theorem inv_mul' {a b : α} (hab : a * b ≠ zero) : ⟨a * b, hab⟩⁻¹ = ⟨a, left_nonzero_of_mul_nonzero _ _ hab⟩⁻¹ * ⟨b, right_nonzero_of_mul_nonzero _ _ hab⟩⁻¹ :=
    inv_mul (left_nonzero_of_mul_nonzero _ _ hab) (right_nonzero_of_mul_nonzero _ _ hab)



end Field

end my
