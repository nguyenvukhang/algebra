import Algebra.Prelude

open DihedralGroup

universe u

-- In Mathlib, we use the default "ZMod 0 = ℤ".
example {n : ℕ} (h : (1 : ZMod n) = (0 : ZMod n)) : n = 1 := ZMod.one_eq_zero_iff.mp h

-- Exercise 7(a).
section Exercise7a
variable {n : ℕ} (h₃ : n ≥ 3) (hn : Odd n)

example : Subgroup.center (DihedralGroup n) = ⊥
  := by --
  refine DihedralGroup.center_eq_bot_of_odd_ne_one hn ?_
  by_contra h₁
  subst h₁
  exact h₃.not_gt (Nat.one_lt_succ_succ 1) -- ∎

example : Subgroup.center (DihedralGroup n) = ⊥
  := by --
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  cases x with
  | r i => -- it's a rotation.
    haveI : sr i * r i = r i * sr i := hx (sr i)
    haveI : sr (i + i) = sr (i - i) := hx (sr i)
    have heq : i + i = i - i := sr.inj (hx (sr i))
    rw [sub_self] at heq
    have h₀ : i = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hn).mp heq
    subst h₀
    exact r_zero
  | sr i => -- it's a reflection.
    have heq : i - 1 = i + 1 := sr.inj (hx (r 1))
    rw [sub_eq_iff_eq_add, add_assoc, left_eq_add] at heq
    rw [ZMod.add_self_eq_zero_iff_eq_zero hn] at heq
    rw [ZMod.one_eq_zero_iff] at heq
    subst heq
    exact False.elim <| h₃.not_gt (Nat.one_lt_succ_succ 1) -- ∎

end Exercise7a
