-- Bezout's Identity for ℤ.
-- That if (a b : ℤ) are non-zero, then there exists (x y : ℤ) such that
-- gcd(a, b) = ax + by.

import Mathlib.Analysis.Normed.Ring.Lemmas

variable {a b : ℤ}

-- Named after the existing `IsBezout.gcd_eq_sum` in Mathlib.
theorem Int.gcd_eq_sum (ha₀ : a ≠ 0) (b : ℤ) : ∃ x y, a * x + b * y = Int.gcd a b
  := by --
  let S := { z | ∃ x y, z = a * x + b * y ∧ z > 0 }
  have hS₀ : ∀ x ∈ S, 0 < x := fun _ ⟨_, _, _, h⟩ => h
  have : ∃ x, Minimal (· ∈ S) x := by
    refine Set.IsPWO.exists_minimal ?_ ?_
    · rw [Set.isPWO_iff_isWF]
      exact BddBelow.isWF ⟨0, fun x hx => (hS₀ x hx).le⟩
    · use |a|, a.sign, 0
      refine ⟨?_, abs_pos.mpr ha₀⟩
      rw [Int.mul_sign_self, mul_zero, add_zero]
      exact Int.abs_eq_natAbs a
  obtain ⟨d, ⟨s, t, hd, hd₀⟩, hd'⟩ := this
  suffices d = a.gcd b by rw [<-this]; exact ⟨s, t, hd.symm⟩
  have hda : d ∣ a
    := by --
    refine Int.dvd_of_emod_eq_zero ?_
    let q := a / d
    let r := a % d
    have hr : r ∈ S ∨ r = 0 := by
      rw [or_iff_not_imp_right]
      intro hr₀
      replace hr₀ : 0 < r := (Int.emod_nonneg a hd₀.ne').lt_of_ne' hr₀
      have : q * d + r = a := Int.ediv_mul_add_emod a d
      have : r = a * (1 - q * s) + b * (-q * t) := by grind only
      exact ⟨1 - q * s, -q * t, this, hr₀⟩
    have hrd : r < d := Int.emod_lt_of_pos a hd₀
    have hrS : r ∉ S := by
      by_contra h'
      refine (hd' h' hrd.le).not_gt hrd
    exact hr.resolve_left hrS -- ∎
  have hdb : d ∣ b
    := by --
    refine Int.dvd_of_emod_eq_zero ?_
    let q := b / d
    let r := b % d
    have hr : r ∈ S ∨ r = 0 := by
      rw [or_iff_not_imp_right]
      intro hr₀
      replace hr₀ : 0 < r := (Int.emod_nonneg b hd₀.ne').lt_of_ne' hr₀
      have : q * d + r = b := Int.ediv_mul_add_emod b d
      have : r = a * (-q * s) + b * (1 - q * t) := by grind only
      exact ⟨-q * s, 1 - q * t, this, hr₀⟩
    have hrd : r < d := Int.emod_lt_of_pos b hd₀
    have hrS : r ∉ S := by
      by_contra h'
      refine (hd' h' hrd.le).not_gt hrd
    exact hr.resolve_left hrS -- ∎
  refine Int.gcd_greatest hd₀.le hda hdb ?_
  intro c ⟨u, hu⟩ ⟨v, hv⟩
  use u * s + v * t
  rw [mul_add, <-mul_assoc, <-mul_assoc, <-hu, <-hv]
  exact hd -- ∎

-- Named after the existing `IsBezout.gcd_eq_sum` in Mathlib.
theorem Int.gcd_eq_sum' (a : ℤ) (hb₀ : b ≠ 0) : ∃ x y, a * x + b * y = Int.gcd a b
  := by --
  obtain ⟨x, y, h⟩ := Int.gcd_eq_sum hb₀ a
  rw [add_comm, Int.gcd_comm] at h
  exact ⟨y, x, h⟩ -- ∎
