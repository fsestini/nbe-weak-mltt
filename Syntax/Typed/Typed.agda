module Syntax.Typed.Typed where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Typed.Context
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming
open import Syntax.Raw.Substitution
open import Syntax.Raw.MetaSubstitution hiding (_,_)
open import Data.Nat
open import Size

mutual

  infix 4 ⊢⟨_⟩
  data ⊢⟨_⟩ (i : Size) : Ctxtₗ → Set where
    ⊢◇  : ⊢⟨ i ⟩ ◇
    ⊢# : ∀{Θ A} {j k : Size< i} → ⊢⟨ j ⟩ Θ → ⟨ k ⟩ Θ ∷ ◇ ⊢ A → ⊢⟨ i ⟩ (Θ # A)

  infix 4 ⊢⟨_⟩_∷_
  data ⊢⟨_⟩_∷_ (i : Size) : Ctxtₗ → Ctxt → Set where
    ⊢◇  : ∀{Θ} {j : Size< i} → ⊢⟨ j ⟩ Θ → ⊢⟨ i ⟩ Θ ∷ ◇
    ⊢# : ∀{Θ Γ A} {j k : Size< i}
       → ⊢⟨ j ⟩ Θ ∷ Γ → ⟨ k ⟩ Θ ∷ Γ ⊢ A → ⊢⟨ i ⟩ Θ ∷ Γ # A

  infix 4 ⟨_⟩_∷_⊢_
  data ⟨_⟩_∷_⊢_ (i : Size) : Ctxtₗ → Ctxt → Term → Set where
    U  : ∀{Θ Γ} {j : Size< i} → ⊢⟨ j ⟩ Θ ∷ Γ → ⟨ i ⟩ Θ ∷ Γ ⊢ U
    El : ∀{Θ Γ A} {j : Size< i} → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∶ U → ⟨ i ⟩ Θ ∷ Γ ⊢ A
    Π  : ∀{Θ Γ A B} {j k : Size< i}
       → ⟨ j ⟩ Θ ∷ Γ ⊢ A → ⟨ k ⟩ Θ ∷ Γ # A ⊢ B → ⟨ i ⟩ Θ ∷ Γ ⊢ Π A B

  infix 4 ⟨_⟩_∷_⊢_∶_
  data ⟨_⟩_∷_⊢_∶_ (i : Size) : Ctxtₗ → Ctxt → Term → Term → Set where
    free  : ∀{Θ Γ A n} {j : Size< i}
          → ⊢⟨ j ⟩ Θ ∷ Γ → Θ [ n ]ₗ↦ A → ⟨ i ⟩ Θ ∷ Γ ⊢ Free n ∶ A
    bound : ∀{Θ Γ A n} {j : Size< i}
          → ⊢⟨ j ⟩ Θ ∷ Γ → Γ [ n ]↦ A → ⟨ i ⟩ Θ ∷ Γ ⊢ Bound n ∶ A
    lam   : ∀{Θ Γ A B t} {j : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ # A ⊢ t ∶ B → ⟨ i ⟩ Θ ∷ Γ ⊢ Lam A t ∶ Π A B
    app   : ∀{Θ Γ A B t s} {j k l : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ t ∶ Π A B → ⟨ k ⟩ Θ ∷ Γ ⊢ s ∶ A → ⟨ l ⟩ Θ ∷ Γ # A ⊢ B
          → ⟨ i ⟩ Θ ∷ Γ ⊢ App t s ∶ B [ s ]
    U-Π   : ∀{Θ Γ A B} {j k : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∶ U → ⟨ k ⟩ Θ ∷ Γ # A ⊢ B ∶ U
          → ⟨ i ⟩ Θ ∷ Γ ⊢ Π A B ∶ U
    coe   : ∀{Θ Γ A B t} {j k : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ t ∶ A → ⟨ k ⟩ Θ ∷ Γ ⊢ A ∼ B → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ B

  infix 4 ⟨_⟩_∷_⊢_∼_
  data ⟨_⟩_∷_⊢_∼_ (i : Size) : Ctxtₗ → Ctxt → Term → Term → Set where

    ∼refl : ∀{Θ Γ A} {j : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ A → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ A
    ∼symm : ∀{Θ Γ A B} {j : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∼ B → ⟨ i ⟩ Θ ∷ Γ ⊢ B ∼ A
    ∼trans : ∀{Θ Γ A B C} {j k : Size< i}
           → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∼ B → ⟨ k ⟩ Θ ∷ Γ ⊢ B ∼ C → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ C

    ∼Pi : ∀{Θ Γ A A' B B'} {j k : Size< i}
        → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∼ A' → ⟨ k ⟩ Θ ∷ Γ # A ⊢ B ∼ B'
        → ⟨ i ⟩ Θ ∷ Γ ⊢ Π A B ∼ Π A' B'
    ∼El : ∀{Θ Γ A B} {j : Size< i}
        → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∼ B ∶ U → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B

  infix 4 ⟨_⟩_∷_⊢_∼_∶_
  data ⟨_⟩_∷_⊢_∼_∶_ (i : Size) : Ctxtₗ → Ctxt → Term → Term → Term → Set where

    -- Equivalence rules
    ∼refl : ∀{Θ Γ t A} {j : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ t ∶ A → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ t ∶ A
    ∼symm : ∀{Θ Γ t s A} {j : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ⟨ i ⟩ Θ ∷ Γ ⊢ s ∼ t ∶ A
    ∼trans : ∀{Θ Γ t s w A} {j k : Size< i}
           → ⟨ j ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ⟨ k ⟩ Θ ∷ Γ ⊢ s ∼ w ∶ A
           → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ w ∶ A

    ∼coe  : ∀{Θ Γ A B t s} {j k : Size< i}
          → ⟨ j ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ⟨ k ⟩ Θ ∷ Γ ⊢ A ∼ B
          → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ B

    -- Computation rules
    ∼β : ∀{Θ Γ A B t s} {j k l : Size< i}
       → ⊢⟨ j ⟩ Θ ∷ Γ → ⟨ k ⟩ Θ ∷ ◇ # A ⊢ t ∶ B → ⟨ l ⟩ Θ ∷ ◇ ⊢ s ∶ A
       → ⟨ i ⟩ Θ ∷ Γ ⊢ App (Lam A t) s ∼ t [ s ] ∶ B [ s ]

    -- Compatibility rules
    ∼ξ : ∀{Θ Γ A A' B t t'} {j k : Size< i}
       → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∼ A' → ⟨ k ⟩ Θ ∷ Γ # A ⊢ t ∼ t' ∶ B
       → ⟨ i ⟩ Θ ∷ Γ ⊢ Lam A t ∼ Lam A' t' ∶ Π A B
    ∼compPi : ∀{Θ Γ A A' B B'} {j k : Size< i}
            → ⟨ j ⟩ Θ ∷ Γ ⊢ A ∼ A' ∶ U → ⟨ k ⟩ Θ ∷ Γ # A ⊢ B ∼ B' ∶ U
            → ⟨ i ⟩ Θ ∷ Γ ⊢ Π A B ∼ Π A' B' ∶ U
    ∼compApp : ∀{Θ Γ r r' s s' A B} {j k l : Size< i}
             → ⟨ j ⟩ Θ ∷ Γ ⊢ r ∼ r' ∶ Π A B → ⟨ k ⟩ Θ ∷ Γ ⊢ s ∼ s' ∶ A
             → ⟨ l ⟩ Θ ∷ Γ # A ⊢ B
             → ⟨ i ⟩ Θ ∷ Γ ⊢ App r s ∼ App r' s' ∶ B [ s ]

infix 4 _∷_⊢_
_∷_⊢_ : Ctxt → Ctxt → Term → Set
Θ ∷ Γ ⊢ A = ⟨ ∞ ⟩ Θ ∷ Γ ⊢ A

infix 4 _∷_⊢_∼_
_∷_⊢_∼_ : Ctxt → Ctxt → Term → Term → Set
Θ ∷ Γ ⊢ A ∼ B = ⟨ ∞ ⟩ Θ ∷ Γ ⊢ A ∼ B

infix 4 _∷_⊢_∶_
_∷_⊢_∶_ : Ctxt → Ctxt → Term → Term → Set
Θ ∷ Γ ⊢ t ∶ A = ⟨ ∞ ⟩ Θ ∷ Γ ⊢ t ∶ A

_∷_⊢_∼_∶_ : Ctxt → Ctxt → Term → Term → Term → Set
Θ ∷ Γ ⊢ t ∼ s ∶ A = ⟨ ∞ ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A

⊢_∷_ : Ctxt → Ctxt → Set
⊢ Θ ∷ Γ = ⊢⟨ ∞ ⟩ Θ ∷ Γ

⊢_ : Ctxt → Set
⊢ Θ = ⊢⟨ ∞ ⟩ Θ

≡tm : ∀{Θ Γ A A' t t' i} → A ≡ A' → t ≡ t'
    → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → ⟨ i ⟩ Θ ∷ Γ ⊢ t' ∶ A'
≡tm refl refl tm = tm

≡tm'' : ∀{Θ Γ A A' t t' i} → A' ≡ A → t' ≡ t
      → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → ⟨ i ⟩ Θ ∷ Γ ⊢ t' ∶ A'
≡tm'' refl refl tm = tm

≡tm' : ∀{Θ Γ Γ' A A' t t' i} → Γ ≡ Γ' → A ≡ A' → t ≡ t'
    → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → ⟨ i ⟩ Θ ∷ Γ' ⊢ t' ∶ A'
≡tm' refl refl refl tm = tm

≡ty : ∀{Θ Γ A A'} → A ≡ A' → Θ ∷ Γ ⊢ A → Θ ∷ Γ ⊢ A'
≡ty refl ty = ty

≡ty' : ∀{Θ Γ Γ' A A'} → Γ ≡ Γ' → A ≡ A' → Θ ∷ Γ ⊢ A → Θ ∷ Γ' ⊢ A'
≡ty' refl refl ty = ty

≡ty'' : ∀{Θ Γ A A'} → A' ≡ A → Θ ∷ Γ ⊢ A → Θ ∷ Γ ⊢ A'
≡ty'' refl ty = ty

≡∼ : ∀{Θ Γ t t' s s' A A' i}
   → t ≡ t' → s ≡ s' → A ≡ A'
   → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ⟨ i ⟩ Θ ∷ Γ ⊢ t' ∼ s' ∶ A'
≡∼ refl refl refl eq = eq

≡ty∼ : ∀{i A A' B B' Θ Γ} → A ≡ A' → B ≡ B'
     → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → ⟨ i ⟩ Θ ∷ Γ ⊢ A' ∼ B'
≡ty∼ refl refl x = x

≡tm∼ : ∀{i A A' t t' s s' Θ Γ}
     → t ≡ t' → s ≡ s' → A ≡ A'
     → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ⟨ i ⟩ Θ ∷ Γ ⊢ t' ∼ s' ∶ A'
≡tm∼ refl refl refl x = x



-- ∼zymm : ∀{Θ Γ A B i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → ⟨ i ⟩ Θ ∷ Γ ⊢ B ∼ A
-- ∼zymm (∼refl x) = ∼refl x
-- ∼zymm (∼symm eq) = ∼symm (∼zymm eq)
-- ∼zymm (∼trans eq eq₁) = ∼trans (∼zymm eq₁) (∼zymm eq)
-- ∼zymm (∼Pi eq eq₁) = ∼Pi (∼zymm eq) {!∼zymm eq₁!}
-- ∼zymm (∼El x) = {!!}
