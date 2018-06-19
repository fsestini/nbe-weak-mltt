module Syntax.Typed.Substitution where

open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p₁ ; proj₂ to p₂)
open import Syntax.Raw.Term
open import Syntax.Raw.Substitution
open import Syntax.Typed.Context
open import Syntax.Typed.Inversion
open import Syntax.Typed.Typed
open import Syntax.Typed.SizeLemma
open import Syntax.Typed.Renaming

open import Syntax.Typed.EqSubstitution
open import Syntax.Typed.EqLemma

infix 4 _∷_⊢ₛ_∶_
data _∷_⊢ₛ_∶_ : Ctxt → Ctxt → Subst → Ctxt → Set where
  ⊢Id   : ∀{Θ Γ} → Θ ∷ Γ ⊢ₛ Id ∶ Γ
  ⊢Cons : ∀{Θ Δ Γ A σ t}
        → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ Δ ⊢ t ∶ sub A σ
        → Θ ∷ Δ ⊢ₛ σ , t ∶ Γ # A
  ⊢Wk   : ∀{Θ ∇ Δ Γ σ w} → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ ∇ ⊢ᵣ w ∶ Δ
        → Θ ∷ ∇ ⊢ₛ σ · w ∶ Γ

toEqSub : ∀{Θ Γ Δ σ} → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ Δ ⊢ₛ σ ∼ σ ∶ Γ
toEqSub ⊢Id = ∼Id
toEqSub (⊢Cons σ x) = ∼Cons (toEqSub σ) x x (∼refl x) (∼refl x)
toEqSub (⊢Wk σ x) = ∼Wk (toEqSub σ) x

⊢sub-ctx : ∀{Θ Γ Δ σ} → ⊢ Θ ∷ Γ → Θ ∷ Δ ⊢ₛ σ ∶ Γ → ⊢ Θ ∷ Δ
⊢sub-ctx c σ = eqsub-ctx c (toEqSub σ)

⊢sub-ty : ∀{Θ Γ Δ A σ} → Θ ∷ Γ ⊢ A → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ Δ ⊢ sub A σ
⊢sub-ty ty σ = eq-lemma-ty1 (eqsub-ty ty (toEqSub σ))

⊢sub-tm : ∀{Θ Γ Δ A t σ} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Δ ⊢ₛ σ ∶ Γ
         → Θ ∷ Δ ⊢ sub t σ ∶ sub A σ
⊢sub-tm td σ = eq-lemma-tm1 (eqsub-tm td (toEqSub σ))

⊢sub-ty∼ : ∀{Θ Γ Δ A B σ} → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Δ ⊢ₛ σ ∶ Γ
          → Θ ∷ Δ ⊢ sub A σ ∼ sub B σ
⊢sub-ty∼ eq' σ = eqsub-ty∼ eq' (toEqSub σ)

⊢sub-tm∼ : ∀{Θ Γ Δ A t s σ} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Δ ⊢ₛ σ ∶ Γ
          → Θ ∷ Δ ⊢ sub t σ ∼ sub s σ ∶ sub A σ
⊢sub-tm∼ eq' σ = eqsub-tm∼ eq' (toEqSub σ)
