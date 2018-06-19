module Syntax.Typed.EqSubstitution where

open import Data.Product hiding (_,_)
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Model
open import Syntax.Typed.MegaLemma

open Modeling subModel

open RTy
open RTm

open SubDef public

eqsub-ctx : ∀{Θ Γ Δ σ τ} → ⊢ Θ ∷ Γ → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → ⊢ Θ ∷ Δ
eqsub-ctx c = ctx-meaning (model-ctx c)

eqsub-ty : ∀{Θ Γ Δ A σ τ} → Θ ∷ Γ ⊢ A → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ
         → Θ ∷ Δ ⊢ sub A σ ∼ sub A τ
eqsub-ty ty σ = eq (model-ty ty σ)

eqsub-tm : ∀{Θ Γ Δ A t σ τ} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ
         → Θ ∷ Δ ⊢ sub t σ ∼ sub t τ ∶ sub A σ
eqsub-tm td σ = eq (proj₂ (model-tm td σ))

eqsub-ty∼ : ∀{Θ Γ Δ A B σ τ} → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ
          → Θ ∷ Δ ⊢ sub A σ ∼ sub B τ
eqsub-ty∼ eq' σ = eq (model-ty∼ eq' σ)

eqsub-tm∼ : ∀{Θ Γ Δ A t s σ τ} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ
          → Θ ∷ Δ ⊢ sub t σ ∼ sub s τ ∶ sub A σ
eqsub-tm∼ eq' σ = eq (proj₂ (model-tm∼ eq' σ))
