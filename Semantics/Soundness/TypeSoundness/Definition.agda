module Semantics.Soundness.TypeSoundness.Definition where

open import Semantics.Soundness.LogicalRelation
open import Syntax
open import Semantics.Completeness
open import Semantics.Soundness.SubLogicalRelation.Definition

open ⟦_⟧≃⟦_⟧_∈𝒯

⊧Ty : ∀{Θ Γ A i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A → Set
⊧Ty {Θ} {Γ} {A} ty =
  ∀{Δ σ ρ} → (ρp : ρ ∈⟦ Γ ⟧) → ⊢ₘₛ Θ → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
  → let aux = models-ty ty ρp in Θ ∷ Δ ⊢ sub A σ ® ∈ty aux
