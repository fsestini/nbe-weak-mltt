module Syntax.Typed.MetaRenaming where

open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Context
open import Syntax.Typed.Model
open import Syntax.Typed.Inversion
open import Data.Nat

private
  ⊧⊧_ : Ctxtₗ → Set
  ⊧⊧ Θ = ∀{X} → Θ ∷ ◇ ⊢ X → ⊢ (Θ # X)

  ⊧_∷_ : Ctxtₗ → Ctxt → Set
  ⊧ Θ ∷ Γ = ∀{X} → Θ ∷ ◇ ⊢ X → ⊢ Θ # X ∷ Γ

  _∷_⊧_ : Ctxtₗ → Ctxt → Term → Set
  Θ ∷ Γ ⊧ A = ∀{X} → Θ ∷ ◇ ⊢ X → Θ # X ∷ Γ ⊢ A

  _∷_⊧_∶_ : Ctxtₗ → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ t ∶ A = ∀{X} → Θ ∷ ◇ ⊢ X → Θ # X ∷ Γ ⊢ t ∶ A

  _∷_⊧_∼_ : Ctxtₗ → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ A ∼ B = ∀{X} → Θ ∷ ◇ ⊢ X → Θ # X ∷ Γ ⊢ A ∼ B

  _∷_⊧_∼_∶_ : Ctxtₗ → Ctxt → Term → Term → Term → Set
  Θ ∷ Γ ⊧ t ∼ s ∶ A = ∀{X} → Θ ∷ ◇ ⊢ X → (Θ # X) ∷ Γ ⊢ t ∼ s ∶ A

metaRenamingModel : Model
metaRenamingModel = record
  { ⊧⊧_ = ⊧⊧_ ; ⊧_∷_ = ⊧_∷_ ; _∷_⊧_ = _∷_⊧_ ; _∷_⊧_∶_ = _∷_⊧_∶_
  ; _∷_⊧_∼_ = _∷_⊧_∼_ ; _∷_⊧_∼_∶_ = _∷_⊧_∼_∶_ ; M-⊢ₘ◇ = λ x → ⊢# ⊢◇ x
  ; M-⊢ₘ# = λ _ _ x → ⊢# (invert-ctx-ctx (invert-ctx-ty x)) x
  ; M-⊢◇ = λ x y → ⊢◇ (x y) ; M-⊢# = λ x y z → ⊢# (x z) (y z)
  ; M-U = λ x y → U (x y) ; M-El = λ x y → El (x y)
  ; M-Π = λ x y z w → Π (y w) (z w) ; M-free = λ _ x y z → free (x z) (there y)
  ; M-bound = λ x y z → bound (x z) y ; M-lam = λ _ _ z w → lam (z w)
  ; M-app = λ _ _ t s B x → app (t x) (s x) (B x)
  ; M-U-Π = λ _ a b x → U-Π (a x) (b x) ; M-coe = λ x y z → coe (x z) (y z)
  ; M-∼refl = λ x y → ∼refl (x y) ; M-∼symm = λ x y → ∼symm (x y)
  ; M-∼trans = λ x y z → ∼trans (x z) (y z) ; M-∼Pi = λ _ _ a b x → ∼Pi (a x) (b x)
  ; M-∼El = λ x y → ∼El (x y) ; M-∼refl' = λ x y → ∼refl (x y)
  ; M-∼symm' = λ x y → ∼symm (x y) ; M-∼trans' = λ x y z → ∼trans (x z) (y z)
  ; M-∼coe = λ x y z → ∼coe (x z) (y z) ; M-∼β = λ _ _ c t s x → ∼β (c x) (t x) (s x)
  ; M-∼ξ = λ _ x y z → ∼ξ (x z) (y z) ; M-∼compPi = λ _ x y z → ∼compPi (x z) (y z)
  ; M-∼compApp = λ _ x y z w → ∼compApp (x w) (y w) (z w) }

open Modeling metaRenamingModel

extend-ctx : ∀{Θ Γ} → ⊢ Θ ∷ Γ → ∀{X} → Θ ∷ ◇ ⊢ X → ⊢ Θ # X ∷ Γ
extend-ctx = model-ctx

extend-ty : ∀{Θ Γ A} → Θ ∷ Γ ⊢ A → ∀{X} → Θ ∷ ◇ ⊢ X → Θ # X ∷ Γ ⊢ A
extend-ty = model-ty

extend-tm : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → ∀{X} → Θ ∷ ◇ ⊢ X → Θ # X ∷ Γ ⊢ t ∶ A
extend-tm = model-tm

extend-ty∼ : ∀{Θ Γ A B} → Θ ∷ Γ ⊢ A ∼ B → ∀{X} → Θ ∷ ◇ ⊢ X → Θ # X ∷ Γ ⊢ A ∼ B
extend-ty∼ = model-ty∼

extend-tm∼ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → ∀{X} → Θ ∷ ◇ ⊢ X
           → (Θ # X) ∷ Γ ⊢ t ∼ s ∶ A
extend-tm∼ = model-tm∼


punch-mctx : ∀{Θ A n i} → ⊢⟨ i ⟩ Θ → Θ [ n ]ₗ↦ A → Θ ∷ ◇ ⊢ A
punch-mctx (⊢# ctx t) (here x) = extend-ty t t
punch-mctx (⊢# ctx t) (there x) = extend-ty (punch-mctx ctx x) t
