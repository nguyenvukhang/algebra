-- Dummit & Foote, 1.7 Group Actions

import Algebra.Prelude

open Function

universe u v

variable {G : Type u} {H : Type v}
  
section Page43
-- page 43 "since these groups have the same order, this map must also be
-- surjective".
variable [h₁ : Fintype G] [h₂ : Fintype H] (φ : G → H)
  (heq : Fintype.card G = Fintype.card H)

noncomputable example : G ≃ H := Fintype.equivOfCardEq heq

example : Injective φ → Surjective φ := Injective.surjective_of_finite (Fintype.equivOfCardEq heq)
example : Injective φ → Surjective φ
  := by --
  intro hφ
  let ψ := Fintype.equivOfCardEq heq
  let f := φ ∘ ψ.symm
  have hf : Bijective f := by
    rw [<-Finite.injective_iff_bijective]
    rw [Equiv.injective_comp]
    exact hφ
  refine Bijective.surjective ?_
  have : φ = f ∘ ψ := (ψ.comp_symm_eq f φ).mp rfl
  rw [this]
  exact hf.comp ψ.bijective -- ∎

end Page43
