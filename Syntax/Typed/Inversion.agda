module Syntax.Typed.Inversion where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming
open import Syntax.Raw.Substitution
open import Syntax.Raw.MetaSubstitution hiding (_,_)
open import Data.Nat
open import Size
open import Syntax.Typed.Typed
open import Syntax.Typed.Context
open import Data.Product renaming (_,_ to _,,_)

mutual

  invert-ctx-ctx : ∀{Θ Γ} {i : Size} → ⊢⟨ i ⟩ Θ ∷ Γ → ⊢⟨ i ⟩ Θ
  invert-ctx-ctx (⊢◇ x) = x
  invert-ctx-ctx (⊢# ctx x) = invert-ctx-ctx ctx

  invert-ctx-ty : ∀{Θ Γ A} {i : Size} → ⟨ i ⟩ Θ ∷ Γ ⊢ A → ⊢⟨ i ⟩ Θ ∷ Γ
  invert-ctx-ty (U x) = x
  invert-ctx-ty (El x) = invert-ctx-tm x
  invert-ctx-ty (Π ty ty₁) = invert-ctx-ty ty

  invert-ctx-tm : ∀{Θ Γ A t} {i : Size} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → ⊢⟨ i ⟩ Θ ∷ Γ
  invert-ctx-tm (free x x₁) = x
  invert-ctx-tm (bound x x₁) = x
  invert-ctx-tm (lam tm) with invert-ctx-tm tm
  invert-ctx-tm (lam tm) | ⊢# q x = q
  invert-ctx-tm (app tm tm₁ _) = invert-ctx-tm tm
  invert-ctx-tm (U-Π tm tm₁) = invert-ctx-tm tm
  invert-ctx-tm (coe tm x) = invert-ctx-tm tm

  invert-ctx-ty∼ : ∀{Θ Γ A B} {i : Size} → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → ⊢⟨ i ⟩ Θ ∷ Γ
  invert-ctx-ty∼ (∼refl x) = invert-ctx-ty x
  invert-ctx-ty∼ (∼symm eq) = invert-ctx-ty∼ eq
  invert-ctx-ty∼ (∼trans eq eq₁) = invert-ctx-ty∼ eq
  invert-ctx-ty∼ (∼Pi eq eq₁) = invert-ctx-ty∼ eq
  invert-ctx-ty∼ (∼El x) = invert-ctx-tm∼ x

  invert-ctx-tm∼ : ∀{Θ Γ A t s i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ⊢⟨ i ⟩ Θ ∷ Γ
  invert-ctx-tm∼ (∼refl x) = invert-ctx-tm x
  invert-ctx-tm∼ (∼symm eq) = invert-ctx-tm∼ eq
  invert-ctx-tm∼ (∼trans eq eq₁) = invert-ctx-tm∼ eq
  invert-ctx-tm∼ (∼β x x₁ x₂) = x
  invert-ctx-tm∼ (∼ξ x eq) = invert-ctx-ty∼ x
  invert-ctx-tm∼ (∼compPi eq eq₁) = invert-ctx-tm∼ eq
  invert-ctx-tm∼ (∼compApp eq eq₁ _) = invert-ctx-tm∼ eq
  invert-ctx-tm∼ (∼coe eq x) = invert-ctx-tm∼ eq

invert-ctx-aux : ∀{Θ Γ A i} → ⊢⟨ i ⟩ Θ ∷ Γ # A → ⊢⟨ i ⟩ Θ ∷ Γ × ⟨ i ⟩ Θ ∷ Γ ⊢ A
invert-ctx-aux (⊢# h x) = h ,, x
