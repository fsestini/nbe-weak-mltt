module Syntax.Typed.EqMetaSubstitution where

open import Syntax.Typed.EqSubstitution
open import Size
open import Relation.Nullary
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p₁ ; proj₂ to p₂)
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Context
open import Syntax.Typed.ContextLemma
open import Syntax.Typed.SizeLemma
open import Syntax.Typed.Inversion
open import Syntax.Typed.MetaSizeLemma
  hiding (⊧_ ; ⊧_∷_ ; _∷_⊧_ ; _∷_⊧_∶_ ; _∷_⊧_∼_∶_ ; _∷_⊧_∼_)
open import Syntax.Typed.Renaming
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Typed.ContextLemma
open import Data.Empty

infix 4 _⊢ₘₛ_∼_∶_
data _⊢ₘₛ_∼_∶_ : Ctxtₗ → MetaSubst → MetaSubst → Ctxtₗ → Set where
  ⊢⟨⟩   : ∀{Θ} → ⊢ Θ → Θ ⊢ₘₛ ⟨⟩ ∼ ⟨⟩ ∶ ◇
  ⊢Cons : ∀{Δ Γ A σ τ t s} → Δ ⊢ₘₛ σ ∼ τ ∶ Γ
        → Δ ∷ ◇ ⊢ t ∼ s ∶ msub A σ
        → Δ ∷ ◇ ⊢ s ∼ t ∶ msub A τ
        → Δ ⊢ₘₛ σ , t ∼ τ , s ∶ Γ # A

flip : ∀{Θ ∇ σ τ} → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ → ∇ ⊢ₘₛ τ ∼ σ ∶ Θ
flip (⊢⟨⟩ x) = ⊢⟨⟩ x
flip (⊢Cons σ x y) = ⊢Cons (flip σ) y x

one-side : ∀{Θ ∇ σ τ} → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ → ∇ ⊢ₘₛ σ ∼ σ ∶ Θ
one-side (⊢⟨⟩ x) = ⊢⟨⟩ x
one-side (⊢Cons σ x y) = ⊢Cons (one-side σ) {!!} {!!}

one-side' : ∀{Θ ∇ σ τ} → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ → ∇ ⊢ₘₛ τ ∼ τ ∶ Θ
one-side' (⊢⟨⟩ x) = ⊢⟨⟩ x
one-side' (⊢Cons σ x y) = ⊢Cons (one-side' σ) {!!} {!!}

mutual

  msub-mctx : ∀{Θ ∇ σ τ i} → ⊢⟨ i ⟩ Θ → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ → ⊢ ∇
  msub-mctx ⊢◇ (⊢⟨⟩ x) = x
  msub-mctx (⊢# ctx x) (⊢Cons σ x₁ y) = msub-mctx ctx σ

  msub-ctx : ∀{Θ ∇ Γ σ τ i} → ⊢⟨ i ⟩ Θ ∷ Γ → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ → ⊢ ∇ ∷ msubc Γ σ
  msub-ctx (⊢◇ x) σ = ⊢◇ (msub-mctx x σ)
  msub-ctx (⊢# ctx x) σ = ⊢# (msub-ctx ctx σ) {!!}

  msub-ctx' : ∀{Θ ∇ Γ σ τ i} → ⊢⟨ i ⟩ Θ ∷ Γ → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ
            → ∇ ⊢ msubc Γ σ ∼ msubc Γ τ
  msub-ctx' (⊢◇ x) σ = ceq◇ (msub-mctx x σ)
  msub-ctx' (⊢# ctx x) σ = ceq# (msub-ctx' ctx σ) {!!} (msub-ty x σ)
    (clemma-ty∼ (msub-ty x σ) (msub-ctx' ctx σ))

  msub-ty : ∀{Θ ∇ Γ A σ τ i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ
          → ∇ ∷ msubc Γ σ ⊢ msub A σ ∼ msub A τ
  msub-ty (U x) σ = ∼refl (U (msub-ctx x σ))
  msub-ty (El x) σ = ∼El (msub-tm x σ)
  msub-ty (Π Ad Bd) σ = ∼Pi (msub-ty Ad σ) (msub-ty Bd σ)

  msub-tm : ∀{Θ ∇ Γ A t σ τ i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ
          → ∇ ∷ msubc Γ σ ⊢ msub t σ ∼ msub t τ ∶ msub A σ
  msub-tm (free x x₁) σ = {!!}
  msub-tm (bound x x₁) σ = {!!}
  msub-tm (lam td) σ with invert-ctx-tm td
  msub-tm (lam td) σ | ⊢# w x = ∼ξ (msub-ty x σ) (msub-tm td σ)
  msub-tm (app td sd) σ =
    ≡∼ refl refl {!!} (∼compApp (msub-tm td σ) (msub-tm sd σ))
  msub-tm (U-Π Ad Bd) σ = ∼compPi (msub-tm Ad σ) (msub-tm Bd σ)
  msub-tm (coe td eq) σ = ∼coe (msub-tm td σ) (msub-ty∼ eq (one-side σ))

  msub-ty∼ : ∀{Θ ∇ Γ A B σ τ i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ
           → ∇ ∷ msubc Γ σ ⊢ msub A σ ∼ msub B τ
  msub-ty∼ (∼refl x) σ = msub-ty x σ
  msub-ty∼ (∼symm eq) σ = clemma-ty∼ (∼symm (msub-ty∼ eq (flip σ)))
    (msub-ctx' (invert-ctx-ty∼ eq) (flip σ))
  msub-ty∼ (∼trans eq eq') σ = ∼trans (msub-ty∼ eq (one-side σ)) (msub-ty∼ eq' σ)
  msub-ty∼ (∼Pi eq eq') σ = ∼Pi (msub-ty∼ eq σ) (msub-ty∼ eq' σ)
  msub-ty∼ (∼El x) σ = ∼El (msub-tm∼ x σ)

  msub-tm∼ : ∀{Θ ∇ Γ A t s σ τ i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → ∇ ⊢ₘₛ σ ∼ τ ∶ Θ
           → ∇ ∷ msubc Γ σ ⊢ msub t σ ∼ msub s τ ∶ msub A σ
  msub-tm∼ (∼refl x) σ = msub-tm x σ
  msub-tm∼ (∼symm eq) σ = {!!}
  msub-tm∼ (∼trans eq eq') σ = {!!}
  msub-tm∼ (∼coe eq x) σ = ∼coe (msub-tm∼ eq σ) (msub-ty∼ x (one-side σ))
  msub-tm∼ (∼β ctx td sd) σ =
    ∼trans (≡∼ refl refl {!!} aux)
      (≡∼ {!!} {!!} {!!} (⊢wk-tm-∼ (⊢up (msub-ctx ctx σ)) (RTm∼.eq aux')))
    where
      aux =
        ∼β (msub-ctx ctx σ)
         (p₁ (∼lemma-tm (msub-tm td σ)))
         (p₁ (∼lemma-tm (msub-tm sd σ)))
      aux' = p₂ (⊢sub-tm∼ (msub-tm td σ)
              (∼Cons ∼Id {!!} {!!} {!!} {!!}
                (≡tm (sym (id-sub _)) refl (p₂ (∼lemma-tm (msub-tm sd σ))))
                (≡∼ refl refl (sym (id-sub _)) (msub-tm sd σ))))
  msub-tm∼ (∼ξ x eq) σ = {!!}
  msub-tm∼ (∼compPi eq eq₁) σ = {!!}
  msub-tm∼ (∼compApp eq eq₁) σ = {!!}
