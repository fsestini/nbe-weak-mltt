module Syntax.Typed.EqLemma where

open import Data.Product hiding (_,_)
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Model
open import Syntax.Typed.MegaLemma

open Modeling subModel

open RTy
open RTm

invert-type : ∀{Θ Γ t A} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Γ ⊢ A
invert-type td = ≡ty (id-sub _) (lx (proj₁ (model-tm td ∼Id)))

eq-lemma-ty1 : ∀{Θ Γ A B} → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Γ ⊢ A
eq-lemma-ty1 eq' = ≡ty (id-sub _) (lx (model-ty∼ eq' ∼Id))

eq-lemma-ty2 : ∀{Θ Γ A B} → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Γ ⊢ B
eq-lemma-ty2 eq' = ≡ty (id-sub _) (rx (model-ty∼ eq' ∼Id))

eq-lemma-tm1 : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t ∶ A
eq-lemma-tm1 eq' = ≡tm (id-sub _) (id-sub _) (lx (proj₂ (model-tm∼ eq' ∼Id)))

eq-lemma-tm2 : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ s ∶ A
eq-lemma-tm2 eq' = ≡tm (id-sub _) (id-sub _) (rx (proj₂ (model-tm∼ eq' ∼Id)))
