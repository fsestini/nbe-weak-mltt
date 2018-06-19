module Syntax.Typed.Model where

open import Syntax.Raw
open import Syntax.Typed.Context
open import Syntax.Typed.Typed
open import Syntax.Typed.Inversion

record Model : Set₁ where
  field
    ⊧⊧_ : Ctxtₗ → Set
    ⊧_∷_ : Ctxtₗ → Ctxt → Set
    _∷_⊧_ : Ctxt → Ctxt → Term → Set
    _∷_⊧_∶_ : Ctxt → Ctxt → Term → Term → Set
    _∷_⊧_∼_ : Ctxt → Ctxt → Term → Term → Set
    _∷_⊧_∼_∶_ : Ctxt → Ctxt → Term → Term → Term → Set

    M-⊢ₘ◇  : ⊧⊧ ◇
    M-⊢ₘ# : ∀{Θ A} → ⊧⊧ Θ → Θ ∷ ◇ ⊧ A → ⊧⊧ (Θ # A)

    M-⊢◇  : ∀{Θ} → ⊧⊧ Θ → ⊧ Θ ∷ ◇
    M-⊢# : ∀{Θ Γ A} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A → ⊧ Θ ∷ (Γ # A)

    M-U : ∀{Θ Γ} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ U
    M-El : ∀{Θ Γ A} → Θ ∷ Γ ⊧ A ∶ U → Θ ∷ Γ ⊧ A
    M-Π  : ∀{Θ Γ A B} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A → Θ ∷ Γ # A ⊧ B → Θ ∷ Γ ⊧ Π A B

    M-free  : ∀{Θ Γ A n} → ⊢ Θ ∷ Γ → ⊧ Θ ∷ Γ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ Free n ∶ A
    M-bound : ∀{Θ Γ A n}
            → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → Θ ∷ Γ ⊧ Bound n ∶ A
    M-lam   : ∀{Θ Γ A B t} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A
            → Θ ∷ Γ # A ⊧ t ∶ B → Θ ∷ Γ ⊧ Lam A t ∶ Π A B
    M-app   : ∀{Θ Γ A B t s} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A
            → Θ ∷ Γ ⊧ t ∶ Π A B → Θ ∷ Γ ⊧ s ∶ A → Θ ∷ Γ # A ⊧ B
            → Θ ∷ Γ ⊧ App t s ∶ (B [ s ])
    M-U-Π   : ∀{Θ Γ A B} → ⊧ Θ ∷ Γ
            → Θ ∷ Γ ⊧ A ∶ U → Θ ∷ Γ # A ⊧ B ∶ U → Θ ∷ Γ ⊧ Π A B ∶ U
    M-coe   : ∀{Θ Γ A B t} → Θ ∷ Γ ⊧ t ∶ A → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ t ∶ B

    M-∼refl : ∀{Θ Γ A} → Θ ∷ Γ ⊧ A → Θ ∷ Γ ⊧ A ∼ A
    M-∼symm : ∀{Θ Γ A B} → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ B ∼ A
    M-∼trans : ∀{Θ Γ A B C} → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ B ∼ C → Θ ∷ Γ ⊧ A ∼ C
    M-∼Pi : ∀{Θ Γ A A' B B'} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A
          → Θ ∷ Γ ⊧ A ∼ A' → Θ ∷ Γ # A ⊧ B ∼ B' → Θ ∷ Γ ⊧ Π A B ∼ Π A' B'
    M-∼El : ∀{Θ Γ A B} → Θ ∷ Γ ⊧ A ∼ B ∶ U → Θ ∷ Γ ⊧ A ∼ B

    M-∼refl' : ∀{Θ Γ t A} → Θ ∷ Γ ⊧ t ∶ A → Θ ∷ Γ ⊧ t ∼ t ∶ A
    M-∼symm' : ∀{Θ Γ t s A} → Θ ∷ Γ ⊧ t ∼ s ∶ A → Θ ∷ Γ ⊧ s ∼ t ∶ A
    M-∼trans' : ∀{Θ Γ t s w A}
              → Θ ∷ Γ ⊧ t ∼ s ∶ A → Θ ∷ Γ ⊧ s ∼ w ∶ A → Θ ∷ Γ ⊧ t ∼ w ∶ A
    M-∼coe  : ∀{Θ Γ A B t s}
          → Θ ∷ Γ ⊧ t ∼ s ∶ A → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ t ∼ s ∶ B
    M-∼β : ∀{Θ Γ A B t s} → Θ ∷ ◇ # A ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
         → ⊧ Θ ∷ Γ → Θ ∷ ◇ # A ⊧ t ∶ B → Θ ∷ ◇ ⊧ s ∶ A
         → Θ ∷ Γ ⊧ App (Lam A t) s ∼ (t [ s ]) ∶ (B [ s ])
    M-∼ξ : ∀{Θ Γ A A' B t t'} → ⊧ Θ ∷ Γ
         → Θ ∷ Γ ⊧ A ∼ A' → Θ ∷ Γ # A ⊧ t ∼ t' ∶ B
         → Θ ∷ Γ ⊧ Lam A t ∼ Lam A' t' ∶ Π A B
    M-∼compPi : ∀{Θ Γ A A' B B'} → ⊧ Θ ∷ Γ
              → Θ ∷ Γ ⊧ A ∼ A' ∶ U → Θ ∷ Γ # A ⊧ B ∼ B' ∶ U
              → Θ ∷ Γ ⊧ Π A B ∼ Π A' B' ∶ U
    M-∼compApp : ∀{Θ Γ r r' s s' A B} → ⊧ Θ ∷ Γ
               → Θ ∷ Γ ⊧ r ∼ r' ∶ Π A B → Θ ∷ Γ ⊧ s ∼ s' ∶ A → Θ ∷ Γ # A ⊧ B
               → Θ ∷ Γ ⊧ App r s ∼ App r' s' ∶ (B [ s ])

module Modeling (M : Model) where

  open Model

  mutual

    model-mctx : ∀{Θ i} → ⊢⟨ i ⟩ Θ → ⊧⊧_ M Θ
    model-mctx ⊢◇ = M-⊢ₘ◇ M
    model-mctx (⊢# ctx x) = M-⊢ₘ# M (model-mctx ctx) (model-ty x)

    model-ctx : ∀{Θ Γ i} → ⊢⟨ i ⟩ Θ ∷ Γ → ⊧_∷_ M Θ Γ
    model-ctx (⊢◇ x) = M-⊢◇ M (model-mctx x)
    model-ctx (⊢# ctx x) = M-⊢# M (model-ctx ctx) (model-ty x)

    model-ty : ∀{Θ Γ A i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A → _∷_⊧_ M Θ Γ A
    model-ty (U x) = M-U M (model-ctx x)
    model-ty (El x) = M-El M (model-tm x)
    model-ty (Π Ad Bd) =
      M-Π M (model-ctx (invert-ctx-ty Ad)) (model-ty Ad) (model-ty Bd)

    model-tm : ∀{Θ Γ A t i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → _∷_⊧_∶_ M Θ Γ t A
    model-tm (free ctx x) = M-free M ctx (model-ctx ctx) x
    model-tm (bound ctx x) = M-bound M (model-ctx ctx) x
    model-tm (lam td) with invert-ctx-tm td
    model-tm (lam td) | ⊢# w x = M-lam M (model-ctx w) (model-ty x) (model-tm td)
    model-tm (app td sd x) with invert-ctx-ty x
    model-tm (app td sd x) | ⊢# w x₁ =
      M-app M (model-ctx w) (model-ty x₁) (model-tm td) (model-tm sd) (model-ty x)
    model-tm (U-Π Ad Bd) =
      M-U-Π M (model-ctx (invert-ctx-tm Ad)) (model-tm Ad) (model-tm Bd)
    model-tm (coe td x) = M-coe M (model-tm td) (model-ty∼ x)

    model-ty∼ : ∀{Θ Γ A B i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → _∷_⊧_∼_ M Θ Γ A B
    model-ty∼ (∼refl x) = M-∼refl M (model-ty x)
    model-ty∼ (∼symm eq) = M-∼symm M (model-ty∼ eq)
    model-ty∼ (∼trans eq eq') = M-∼trans M (model-ty∼ eq) (model-ty∼ eq')
    model-ty∼ (∼Pi eq eq') with invert-ctx-ty∼ eq'
    model-ty∼ (∼Pi eq eq') | ⊢# w x =
      M-∼Pi M (model-ctx w) (model-ty x) (model-ty∼ eq) (model-ty∼ eq')
    model-ty∼ (∼El x) = M-∼El M (model-tm∼ x)

    model-tm∼ : ∀{Θ Γ A t s i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → _∷_⊧_∼_∶_ M Θ Γ t s A
    model-tm∼ (∼refl x) = M-∼refl' M (model-tm x)
    model-tm∼ (∼symm eq) = M-∼symm' M (model-tm∼ eq)
    model-tm∼ (∼trans eq eq') = M-∼trans' M (model-tm∼ eq) (model-tm∼ eq')
    model-tm∼ (∼coe eq eq') = M-∼coe M (model-tm∼ eq) (model-ty∼ eq')
    model-tm∼ (∼β ctx td sd) =
      M-∼β M td sd (model-ctx ctx) (model-tm td) (model-tm sd)
    model-tm∼ (∼ξ tyeq eq) =
      M-∼ξ M (model-ctx (invert-ctx-ty∼ tyeq)) (model-ty∼ tyeq) (model-tm∼ eq)
    model-tm∼ (∼compPi eq eq') =
      M-∼compPi M (model-ctx (invert-ctx-tm∼ eq)) (model-tm∼ eq) (model-tm∼ eq')
    model-tm∼ (∼compApp eq eq' Bd) =
      M-∼compApp M (model-ctx (invert-ctx-tm∼ eq)) (model-tm∼ eq)
        (model-tm∼ eq') (model-ty Bd)
