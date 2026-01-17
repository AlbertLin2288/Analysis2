import Analysis2.Structure.CommSemiRing
import Analysis2.CompStructure.OrderedSemiRing
noncomputable section
namespace my
open Classical
open Comp
open Zero One
open OfNat
open Monoid CommMonoid SemiRing CommSemiRing
open OrderedMonoid OrderedCommMonoid OrderedSemiRing


class OrderedCommSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [CommSemiRing α] [OrderedCommMonoid α] where
  _mul_le_mul_of_nonneg_right {a b c : α} : a ≤ b → zero ≤ c → a * c ≤ b * c
  _zero_le_one : (zero : α) ≤ one -- WLOG


namespace OrderedCommSemiRing

  open CommSemiRing
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [CommSemiRing α] [OrderedCommMonoid α] [OrderedCommSemiRing α]

  theorem _mul_le_mul_of_nonneg_left {a b c : α} : a ≤ b → c ≥ zero → c * a ≤ c * b := by
    intro h h'
    simp only [mul_comm]
    exact _mul_le_mul_of_nonneg_right h h'

  @[default_instance] instance : OrderedSemiRing α := ⟨_mul_le_mul_of_nonneg_right, _mul_le_mul_of_nonneg_left, _zero_le_one⟩

  open ℕ (_zero succ)

  theorem ofNat_le_of_le {n m : ℕ} : n ≤ m → ofNat' α n ≤ ofNat m :=
    match n, m with
    | _, _zero => (ℕ.eq_zero_of_le_zero · ▸ le_self _)
    | _zero, succ m => fun _ => nonneg_add_nonneg_is_nonneg (ofNat_le_of_le (ℕ.zero_le m)) zero_le_one
    | succ _, succ _ => fun h => add_le_add_right one (ofNat_le_of_le (ℕ.le_of_succ_le_succ h))

  theorem ofNat_nonneg (n : ℕ) : (zero : α) ≤ ofNat n :=
    ofNat_le_of_le (α:=α) (ℕ.zero_le n)

  theorem lt_of_ofNat_lt {n m : ℕ} : ofNat' α n < ofNat m → n < m :=
    (fun h' => · (ofNat_le_of_le h'))

  --Not possible
  -- see test1_2.lean

  -- theorem ofNat_lt_of_lt {n m : ℕ} : n < m → ofNat' α n < ofNat m :=
  --   fun h => lt_of_le_ne (ofNat_le_of_le (le_of_lt h)) (
  --     match n, m with
  --     | _, _zero => (ℕ.not_lt_zero _ h).elim
  --     | _zero, succ m => sorry
  --     | succ n, succ m => sorry
  --     -- | _, _zero => (ℕ.eq_zero_of_le_zero · ▸ le_self _)
  --     -- | _zero, succ m => fun _ => nonneg_add_nonneg_is_nonneg (ofNat_le_of_le (ℕ.zero_le m)) zero_le_one
  --     -- | succ _, succ _ => fun h => add_le_add_right one (ofNat_le_of_le (ℕ.le_of_succ_le_succ h))
  --   )

  -- theorem le_of_ofNat_le {n m : ℕ} : ofNat' α n ≤ ofNat m → n ≤ m :=
  --   match n, m with
  --   | _zero, _ => fun _ => ℕ.zero_le _
  --   | succ n, _zero =>
  --     fun h =>
  --       (not_le_of_lt (α:=α) zero_lt_one (zero_add (one:α) ▸ le_of_le_le (add_le_add_right one (ofNat_nonneg n)) h)).elim
  --   | succ n, succ m =>
  --     sorry

  -- theorem ofNat_le_iff {n m : ℕ} : ofNat' α n ≤ ofNat m ↔ n ≤ m :=
  --   ⟨le_of_ofNat_le, ofNat_le_of_le⟩

end OrderedCommSemiRing



end my
