module Semantics.Soundness.SubLogicalRelation.Definition where

open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Data.Product renaming (_,_ to _,,_)
open import Semantics.Soundness.LogicalRelation.Definition

open SemTy
open _∈⟦_⟧_
open _∈_


infix 4 ⊢ₘₛ_
data ⊢ₘₛ_ : (Θ : Ctxtₗ) → Set where
  m◇® : ⊢ₘₛ ◇
  m#® : ∀{Θ A} (p : Free (clen Θ) ∈⟦ A ⟧ Id)
     → ⊢ₘₛ Θ
     → Θ ∷ ◇ ⊢ A ® inT p
     → ⊢ₘₛ Θ # A


-- infix 4 _⊢ₘₛ_
-- data _⊢ₘₛ_ (Δ : Ctxtₗ) : (Θ : Ctxtₗ) → Set where
--   ◇® : Δ ⊢ₘₛ ◇
--   #® : ∀{Θ A} {p : Free (clen Θ) ∈⟦ A ⟧ Id}
--      → Δ ⊢ₘₛ Θ
--      → Δ ∷ ◇ ⊢ A ® inT p
--      → Δ ⊢ₘₛ Θ # A

infix 4 _∷_⊢ₛ_∶_®_
data _∷_⊢ₛ_∶_®_ (Θ : Ctxtₗ) : ∀{ρ} → (Δ Γ : Ctxt) → Subst → ρ ∈⟦ Γ ⟧ → Set where

  ◇® : ∀{Δ σ ρ} {ρp : ρ ∈⟦ ◇ ⟧} → Θ ∷ Δ ⊢ₛ σ ∶ ◇ → Θ ∷ Δ ⊢ₛ ◇ ∶ σ ® ρp

  #® : ∀{Γ Δ A σ ρ t a} {ρp : ρ ∈⟦ Γ ⟧} {p : a ∈⟦ A ⟧ ρ}
     → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
     -- → Θ ∷ Γ ⊢ A ® inT p
     → Θ ∷ Δ ⊢ t ∶ sub A σ ® inT p ∋ wit (nn p)
     → Θ ∷ Δ ⊢ₛ Γ # A ∶ (σ , t) ® cExt ρp p

  ·® : ∀{Γ ∇ Δ σ ρ w} {ρp : ρ ∈⟦ Γ ⟧}
     → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
     → Θ ∷ ∇ ⊢ᵣ w ∶ Δ
     → Θ ∷ ∇ ⊢ₛ Γ ∶ σ · w ® cWk {w = w} ρp

derₛ : ∀{Θ Γ Δ σ ρ} {p : ρ ∈⟦ Γ ⟧} → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® p → Θ ∷ Δ ⊢ₛ σ ∶ Γ
derₛ (◇® x) = x
derₛ (#® {p = p} rel y) = ⊢Cons (derₛ rel) (derₜ {ty = inT p} y)
derₛ (·® rel x) = ⊢Wk (derₛ rel) x
