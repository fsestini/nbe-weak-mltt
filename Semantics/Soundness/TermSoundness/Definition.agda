module Semantics.Soundness.TermSoundness.Definition where

open import Syntax
open import Semantics.Completeness
open import Semantics.Soundness.LogicalRelation
open import Semantics.Soundness.SubLogicalRelation.Definition
open import Data.Product

open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒯
open _∈_
open _∈⟦_⟧_
open SemTy

⊧Tm : ∀{Θ Γ t A i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → Set
⊧Tm {Θ} {Γ} {t} {A} td = ∀{Δ σ ρ}
              → (ρp : ρ ∈⟦ Γ ⟧)
              → ⊢ₘₛ Θ
              → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
              → let aux = proj₂ (models td) ρp
                in Θ ∷ Δ ⊢ sub t σ ∶ sub A σ ® ∈ty aux ∋ wit (∈tm aux)
