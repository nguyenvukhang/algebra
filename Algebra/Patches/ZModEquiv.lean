-- Explorations surrounding ⟨x⟩ ≃ ZMod |x|. The equivalence of a cyclic group
-- to ℤ/nℤ  where n is the order of that generating element.
--
-- Inspired by ../DummitFoote/S02_E03_Cyclic_Groups_and_Subgroups.lean

import Algebra.Prelude

universe u

variable {G : Type u}

section Bijection.Subtype

variable [Group G] {x : G}

private noncomputable def φ₀' (hx : ¬IsOfFinOrder x) : Subgroup.zpowers x ≃ ℤ
  := by --
  let φ (k : ℤ) : Subgroup.zpowers x := ⟨x ^ k, k, rfl⟩
  refine (Equiv.ofBijective φ ?_).symm
  rw [Function.bijective_iff_existsUnique]
  rintro ⟨g, i, hi : x ^ i = g⟩
  have hi' : φ i = ⟨g, _⟩ := Subtype.mk.congr_simp _ _ hi _
  refine ⟨i, hi', ?_⟩
  intro j hj'
  have hj : x ^ j = g := by
    rw [Subtype.mk.injEq] at hj'
    exact hj'
  have : x ^ (-j) = g⁻¹ := by
    rw [<-hj]
    exact zpow_neg x j
  have : x ^ (i - j) = 1 := by
    rw [zpow_sub, hi, hj]
    exact mul_inv_cancel g
  have : x ^ |i - j| = 1 := (zpow_abs_eq_one x (i - j)).mpr this
  obtain ⟨k, hk⟩ : (orderOf x : ℤ) ∣ |i - j| := orderOf_dvd_iff_zpow_eq_one.mpr this
  by_contra! hne
  have : 0 < orderOf x := by
    refine Nat.zero_lt_of_ne_zero ?_
    by_contra h₀
    rw [h₀, CharP.cast_eq_zero, zero_mul, abs_eq_zero] at hk
    exact (sub_ne_zero_of_ne hne.symm) hk
  have : IsOfFinOrder x := orderOf_pos_iff.mp this
  refine hx this -- ∎

private noncomputable def φ₁' (hx : IsOfFinOrder x) : Subgroup.zpowers x ≃ ZMod (orderOf x)
  := by --
  let n := orderOf x
  let H := Subgroup.zpowers x
  have : 0 < orderOf x := hx.orderOf_pos
  have : NeZero (orderOf x) := NeZero.of_pos hx.orderOf_pos
  let φ (k : ZMod n) : H := ⟨x ^ k.val, k.val, zpow_natCast x k.val⟩
  -- The same unpacker on both sides of the if statement.
  refine (Equiv.ofBijective φ ?_).symm
  rw [Function.bijective_iff_existsUnique]
  rintro ⟨g, k, hk : x ^ k = g⟩
  -- Solve.
  let i : ZMod n := k
  have hi : x ^ i.val = g := by
    rw [<-zpow_natCast x i.val, ZMod.val_intCast k, <-hk]
    exact zpow_mod_orderOf x k
  have hi : φ i = ⟨g, _⟩ := Subtype.mk.congr_simp _ _ hi _
  refine ⟨i, hi, ?_⟩
  intro j hj
  rw [<-hi, Subtype.mk.injEq] at hj
  rw [<-ZMod.natCast_zmod_val i]
  rw [<-ZMod.natCast_zmod_val j]
  rw [ZMod.natCast_eq_natCast_iff' j.val i.val n]
  exact hx.pow_inj_mod.mp hj -- ∎

noncomputable def l₀' (x : G) : (Subgroup.zpowers x) ≃ ZMod (orderOf x)
  := by --
  by_cases hx : IsOfFinOrder x
  · exact φ₁' hx
  · rw [orderOf_eq_zero hx]
    exact φ₀' hx -- ∎

end Bijection.Subtype

section Bijection
open Subgroup
variable [Group G] {x : G}

private noncomputable def φ₀ (hx : ¬IsOfFinOrder x) (h : zpowers x = ⊤) : G ≃ ℤ
  := by --
  let φ (k : ℤ) := x ^ k
  refine (Equiv.ofBijective φ ?_).symm
  rw [Function.bijective_iff_existsUnique]
  intro g
  have hg := Subgroup.mem_top g
  rw [<-h] at hg
  obtain ⟨i, hi : x ^ i = g⟩ := hg
  refine ⟨i, hi, ?_⟩
  intro j (hj : x ^ j = g)
  have : x ^ (-j) = g⁻¹ := by
    rw [<-hj]
    exact zpow_neg x j
  have : x ^ (i - j) = 1 := by
    rw [zpow_sub, hi, hj]
    exact mul_inv_cancel g
  have : x ^ |i - j| = 1 := (zpow_abs_eq_one x (i - j)).mpr this
  obtain ⟨k, hk⟩ : (orderOf x : ℤ) ∣ |i - j| := orderOf_dvd_iff_zpow_eq_one.mpr this
  by_contra! hne
  have : 0 < orderOf x := by
    refine Nat.zero_lt_of_ne_zero ?_
    by_contra h₀
    rw [h₀, CharP.cast_eq_zero, zero_mul, abs_eq_zero] at hk
    exact (sub_ne_zero_of_ne hne.symm) hk
  have : IsOfFinOrder x := orderOf_pos_iff.mp this
  refine hx this -- ∎

section Verify
variable (ψ : ¬IsOfFinOrder x) (h : zpowers x = ⊤) (k : ℤ)

example : (φ₀ ψ h).symm k = x ^ k := rfl
example : φ₀ ψ h (x ^ k) = k := (φ₀ ψ h).apply_eq_iff_eq_symm_apply.mpr rfl
end Verify

-- Suppose that G = ⟨x⟩, that G is cyclic. And suppose that |x| = n is finite.
-- Then G is isomorphic to ℤ/nℤ, and that isomorphism is given by φ([k]) = xᵏ.
private noncomputable def φ₁ (hx : IsOfFinOrder x) (h : zpowers x = ⊤) : G ≃ ZMod (orderOf x)
  := by --
  let n := orderOf x
  have : 0 < orderOf x := hx.orderOf_pos
  have : NeZero (orderOf x) := NeZero.of_pos hx.orderOf_pos
  let φ (k : ZMod n) : G := x ^ k.val
  -- The same unpacker on both sides of the if statement.
  refine (Equiv.ofBijective φ ?_).symm
  rw [Function.bijective_iff_existsUnique]
  intro g
  have hg := Subgroup.mem_top g
  rw [<-h] at hg
  obtain ⟨k, hk : x ^ k = g⟩ := hg
  -- Solve.
  let i : ZMod n := k
  have hi : x ^ i.val = g := by
    rw [<-zpow_natCast x i.val, ZMod.val_intCast k, <-hk]
    exact zpow_mod_orderOf x k
  refine ⟨i, hi, ?_⟩
  intro j hj
  rw [<-hi] at hj
  rw [<-ZMod.natCast_zmod_val i]
  rw [<-ZMod.natCast_zmod_val j]
  rw [ZMod.natCast_eq_natCast_iff' j.val i.val n]
  exact hx.pow_inj_mod.mp hj -- ∎

section Verify
variable (ψ : IsOfFinOrder x) (h : zpowers x = ⊤) (k : ZMod (orderOf x))

example : (φ₁ ψ h).symm k = x ^ k.val := rfl
example : φ₁ ψ h (x ^ k.val) = k := (φ₁ ψ h).apply_eq_iff_eq_symm_apply.mpr rfl
end Verify

noncomputable def l₀ {x : G} (h : zpowers x = ⊤) : G ≃ ZMod (orderOf x)
  := by --
  by_cases hx : IsOfFinOrder x
  · exact φ₁ hx h
  · rw [orderOf_eq_zero hx]
    exact φ₀ hx h -- ∎

end Bijection

noncomputable def zpowers_equiv_zmod_orderOf [Group G] {x : G}
  (htop : Subgroup.zpowers x = ⊤)
  : Additive G ≃+ ZMod (orderOf x)
  := by --
  by_cases hx : IsOfFinOrder x
  · let f : ZMod (orderOf x) ≃+ Additive G := by
      refine {
        toEquiv := (φ₁ hx htop).symm
        map_add' k₁ k₂ := by
          change x ^ (k₁ + k₂).val = x ^ k₁.val * x ^ k₂.val
          have : NeZero (orderOf x) := ⟨orderOf_ne_zero_iff.mpr hx⟩
          rw [<-pow_add, pow_inj_mod, ZMod.val_add k₁ k₂, Nat.mod_mod]
      }
    exact f.symm
  · rw [orderOf_eq_zero hx]
    change Additive G ≃+ ℤ
    let f : ℤ ≃+ Additive G := { toEquiv := (φ₀ hx htop).symm, map_add' := zpow_add x }
    exact f.symm -- ∎

noncomputable def zmultiples_equiv_zmod_addOrderOf [AddGroup G] {x : G}
  (htop : AddSubgroup.zmultiples x = ⊤)
  : G ≃+ ZMod (addOrderOf x)
  := by --
  let y : Multiplicative G := x
  have htop' : Subgroup.zpowers y = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro h
    have hg := AddSubgroup.mem_top h.toAdd
    rw [<-htop] at hg
    exact Subgroup.mem_zpowers_iff.mpr hg
  exact zpowers_equiv_zmod_orderOf htop' -- ∎
