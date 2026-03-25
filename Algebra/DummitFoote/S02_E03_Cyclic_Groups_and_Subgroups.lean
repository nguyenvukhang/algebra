import Algebra.Prelude

open DihedralGroup Cardinal

universe u
variable {H : Type u}

example [Fintype H] : #H = Fintype.card H := mk_fintype H

section Proposition2
variable [Group H] {x : H}

@[reducible]
private noncomputable def f₀ [Fintype H] (x : H) : Fintype (Subgroup.closure {x})
  := by --
  exact Fintype.ofFinite (Subgroup.closure {x}) -- ∎

@[reducible]
private noncomputable def f₁ (H : Type u) [Group H] [Fintype H] : Fintype (⊤ : Subgroup H)
  := by --
  exact Fintype.ofFinite (⊤ : Subgroup H) -- ∎

private def φ (H : Type u) [Group H] : (⊤ : Subgroup H) ≃ H
  := Equiv.subtypeUnivEquiv Subgroup.mem_top

private lemma o₀ (hx : 0 < orderOf x) (n : ℕ) : ∃ m < orderOf x, x ^ m = x ^ n
  := ⟨n % orderOf x, Nat.mod_lt n hx, pow_mod_orderOf x n⟩

private lemma o₁ (hx : 0 < orderOf x) (n : ℤ) : ∃ m < orderOf x, x ^ m = x ^ n
  := by --
  let m := n % orderOf x
  have hmeq : m = m.toNat := by
    rw [Int.eq_natCast_toNat]
    refine Int.emod_nonneg n ?_
    rw [Int.natCast_ne_zero_iff_pos]
    exact hx
  use m.toNat
  have : x ^ m = x ^ m.toNat := by
    rw [hmeq]
    exact zpow_natCast x m.toNat
  rw [<-this]
  refine ⟨?_, zpow_mod_orderOf x n⟩
  refine (Int.toNat_lt ?_).mpr ?_
  · exact Int.natCast_toNat_eq_self.mp hmeq.symm
  · refine Int.emod_lt_of_pos n ?_
    exact Int.natCast_pos.mpr hx -- ∎

private lemma o₂ (hx : 0 < orderOf x) : Subgroup.closure {x} = { x ^ n | n < orderOf x }
  := by --
  refine le_antisymm ?_ ?_
  · intro v (hv : v ∈ Subgroup.closure {x})
    rw [Subgroup.mem_closure_singleton] at hv
    obtain ⟨n, hn⟩ := hv
    obtain ⟨m, hm, heq⟩ := o₁ hx n
    refine ⟨m, hm, ?_⟩
    rw [heq]
    exact hn
  · intro v ⟨m, hm, hv⟩
    rw [SetLike.mem_coe, Subgroup.mem_closure_singleton]
    refine ⟨m, ?_⟩
    rw [<-hv]
    exact zpow_natCast x m -- ∎

@[reducible]
private noncomputable def f₂ (hx : 0 < orderOf x) : Fintype (Subgroup.closure {x})
  := by --
  let N := orderOf x
  have hf : Fintype { x ^ n | n < N } := (Set.Finite.image _ (Set.finite_lt_nat N)).fintype
  rw [<-o₂ hx] at hf
  exact hf -- ∎

example [Fintype H] : haveI := f₁ H
  Fintype.card H = Fintype.card (⊤ : Subgroup H)
  := by --
  let _ := f₁ H
  exact Fintype.card_congr (φ H).symm -- ∎

noncomputable example (A : Finset ℕ) (f : ℕ → H) : Fintype ↑(f '' ↑A) := by
  exact Fintype.ofFinite ↑(f '' ↑A)

example (A : Finset ℕ) (f : ℕ → H) :
  ((A : Set ℕ).image f).ncard ≤ (A : Set ℕ).ncard := by
  let B : Set ℕ := A
  change (B.image f).ncard ≤ B.ncard
  apply Set.ncard_image_le (Finset.finite_toSet A)

-- The nicest goal possible.
example [Fintype H]
  (h : Subgroup.closure {x} = ⊤)
  (hx : 0 < orderOf x)
  : #H = orderOf x := by
  let N := orderOf x
  rw [mk_fintype H, Nat.cast_inj]
  let _ := f₁ H
  rw [<-Fintype.card_congr (φ H)]
  let _ := f₂ hx
  have : Fintype.card (⊤ : Subgroup H) = Fintype.card (Subgroup.closure {x}) := by simp_rw [h]
  rw [this]
  let _ : Fintype { x ^ n | n < N } := (Set.Finite.image _ (Set.finite_lt_nat N)).fintype
  have : Fintype.card (Subgroup.closure {x}) = Fintype.card { x ^ n | n < orderOf x } := by
    simp_rw [<-o₂ hx]
    rfl
  rw [this]
  refine le_antisymm ?_ ?_
  · change Fintype.card { x ^ n | n < N } ≤ N
    let S := (Finset.range N : Set ℕ).image (x ^ ·)
    have : { x ^ n | n < N } = S := by
      dsimp only [S]
      rw [Finset.coe_range]
      exact Set.Subset.antisymm (fun ⦃_⦄ ↦ (·)) fun ⦃_⦄ ↦ (·)
    let _ : Fintype S := Fintype.ofFinite ↑S
    have : Fintype.card { x ^ n | n < N } = Fintype.card S :=
      Fintype.card_congr' (congrArg Set.Elem this)
    rw [this]
    dsimp only [S]
    sorry
  · sorry

example [DecidableEq H] (hx : 0 < orderOf x) : #{ x ^ n | n < orderOf x } = orderOf x := by
  let S := (Finset.range (orderOf x)).image (x ^ ·)
  sorry

noncomputable example [DecidableEq H] (hx : 0 < orderOf x) :
  Finset.card ((Finset.range (orderOf x)).image (x ^ ·)) = orderOf x
  := by
  sorry

end Proposition2
