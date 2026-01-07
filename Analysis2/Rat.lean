import Analysis2.EquivalentClass
import Analysis2.Nat
import Analysis2.Int

noncomputable section
namespace my
open Classical

open my renaming EquivalentClass → EC


structure ℤ_pair where
  fst : ℤ
  snd : ℤ

structure ℚ_con where
  fst : ℤ
  snd : ℤ
  h : snd.gt ℤ.zero


def ℚ.eqv : ℚ_con → ℚ_con → Prop :=
  fun a b => a.fst.mul b.snd = a.snd.mul b.fst

namespace ℚ.eqv

  theorem refl : ∀ (a : ℚ_con), ℚ.eqv a a :=
    fun ⟨a1, a2, _⟩ => ℤ.mul_comm a1 a2

  theorem symm : ∀ {a b : ℚ_con}, ℚ.eqv a b → ℚ.eqv b a := by
    unfold eqv
    intro ⟨a1, a2, _⟩ ⟨b1, b2, _⟩ h
    simp only [a1.mul_comm, a2.mul_comm] at *
    exact h.symm

  theorem trans : ∀ {a b c : ℚ_con}, ℚ.eqv a b → ℚ.eqv b c → ℚ.eqv a c := by
    unfold eqv
    intro ⟨a1, a2, _⟩ ⟨b1, b2, hb⟩ ⟨c1, c2, hc⟩ h1 h2
    simp only [] at *
    by_cases hb0 : b1 = ℤ.zero
    case pos =>
      simp only [hb0, ℤ.mul_zero, ℤ.zero_mul] at h1 h2
      have ha0 : a1 = ℤ.zero := (ℤ.mul_eq_zero h1).resolve_right (ℤ.ne_of_lt hb).symm
      have hc0 : c1 = ℤ.zero := (ℤ.mul_eq_zero h2.symm).resolve_left (ℤ.ne_of_lt hb).symm
      rw [ha0, hc0, ℤ.mul_zero, ℤ.zero_mul]
    case neg =>
      replace h1 := congrArg (ℤ.mul · c1) h1--(ℤ.mul_left_inj (b2.mul c1)).mpr h1
      simp only [ℤ.mul_assoc, ←h2] at h1
      replace h1 := congrArg (ℤ.mul · c2) h1--(ℤ.mul_left_inj (b2.mul c1)).mpr h1
      simp only [ℤ.mul_left_inj (ℤ.ne_of_lt hc).symm] at h1
      simp only [ℤ.mul_left_comm _ b1, ℤ.mul_right_inj hb0] at h1
      exact h1

  def eqv : Equivalence ℚ.eqv where
    refl := refl
    symm := symm
    trans := trans

end ℚ.eqv

def ℚ := EquivalentClass ℚ.eqv


end my
