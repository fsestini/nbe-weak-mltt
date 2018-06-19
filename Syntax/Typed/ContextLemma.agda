module Syntax.Typed.ContextLemma where

open import Syntax.Typed.Renaming
open import Syntax.Typed.Inversion
open import Syntax.Typed.Typed
open import Syntax.Typed.Context
open import Syntax.Raw
open import Data.Product renaming (_,_ to _,,_)
open import Size

infix 4 _⊢_∼_
data _⊢_∼_ : Ctxt → Ctxt → Ctxt → Set where
  ceq◇ : ∀{Θ} → ⊢ Θ → Θ ⊢ ◇ ∼ ◇
  ceq# : ∀{Θ Γ Δ A B} → Θ ⊢ Γ ∼ Δ → Θ ∷ Δ ⊢ B
       → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Δ ⊢ A ∼ B → Θ ⊢ Γ # A ∼ Δ # B

crefl : ∀{Θ Γ} → ⊢ Θ ∷ Γ → Θ ⊢ Γ ∼ Γ
crefl (⊢◇ x) = ceq◇ x
crefl (⊢# ctx x) = ceq# (crefl ctx) x (∼refl x) (∼refl x)

clemma-ctx : ∀{Θ Γ Δ} → Θ ⊢ Γ ∼ Δ → ⊢ Θ ∷ Δ
clemma-ctx (ceq◇ x) = ⊢◇ x
clemma-ctx (ceq# eq x x₁ z) = ⊢# (clemma-ctx eq) x

clemma↦ : ∀{Θ Γ Δ A n} → Θ ⊢ Γ ∼ Δ → Γ [ n ]↦ A
        → Σ Term λ B → Δ [ n ]↦ B × Θ ∷ Δ ⊢ B ∼ A
clemma↦ (ceq◇ _) ()
clemma↦ (ceq# ctx ty x₂ eq) here = _ ,, here ,, ⊢wk-ty-∼ (∼symm eq) (⊢Up ⊢Id ty)
clemma↦ (ceq# ctx x₁ x₂ x₃) (there x) with clemma↦ ctx x
clemma↦ (ceq# ctx x₁ x₂ x₃) (there x) | C ,, q ,, r =
  _ ,, there q ,, ⊢wk-ty-∼ r (⊢Up ⊢Id x₁)

idctx∼ : ∀ {Θ Γ} → ⊢ Θ ∷ Γ → Θ ⊢ Γ ∼ Γ
idctx∼ (⊢◇ x) = ceq◇ x
idctx∼ (⊢# ctx x) = ceq# (idctx∼ ctx) x (∼refl x) (∼refl x)

mutual

  clemma-ty : ∀{Θ Γ Δ A i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A → Θ ⊢ Γ ∼ Δ → Θ ∷ Δ ⊢ A
  clemma-ty (U x) ctx = U (clemma-ctx ctx)
  clemma-ty (El x) ctx = El (clemma-tm x ctx)
  clemma-ty (Π ty ty') ctx with invert-ctx-ty ty'
  clemma-ty (Π ty ty') ctx | ⊢# q x =
    Π (clemma-ty ty ctx) (clemma-ty ty'
      (ceq# ctx (clemma-ty x ctx) (∼refl x) (∼refl (clemma-ty x ctx))))

  clemma-tm : ∀{Θ Γ Δ A t i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → Θ ⊢ Γ ∼ Δ → Θ ∷ Δ ⊢ t ∶ A
  clemma-tm (free x x₁) ctx = free (clemma-ctx ctx) x₁
  clemma-tm (bound x x₁) ctx =
    coe (bound (clemma-ctx ctx) (proj₁ (proj₂ h))) (proj₂ (proj₂ h))
    where h = clemma↦ ctx x₁
  clemma-tm (lam tm) ctx with invert-ctx-tm tm
  clemma-tm (lam tm) ctx | ⊢# q x =
    lam (clemma-tm tm (ceq# ctx (clemma-ty x ctx)
      (∼refl x) (∼refl (clemma-ty x ctx))))
  clemma-tm (app tm tm₁ tmB) ctx =
    app (clemma-tm tm ctx) (clemma-tm tm₁ ctx)
      (clemma-ty tmB (ceq# ctx ih (∼refl ihc) (∼refl ih)))
    where ihc = proj₂ (invert-ctx-aux (invert-ctx-ty tmB))
          ih = clemma-ty ihc ctx
  clemma-tm (U-Π tm tm₁) ctx =
    U-Π ih (clemma-tm tm₁ (ceq# ctx (El ih) (∼refl (El tm)) (∼refl (El ih))))
    where ih = clemma-tm tm ctx
  clemma-tm (coe tm x) ctx = coe (clemma-tm tm ctx) (clemma-ty∼ x ctx)

  clemma-ty∼ : ∀{Θ Γ Δ A B i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → Θ ⊢ Γ ∼ Δ → Θ ∷ Δ ⊢ A ∼ B
  clemma-ty∼ (∼refl x) ctx = ∼refl (clemma-ty x ctx)
  clemma-ty∼ (∼symm eq) ctx = ∼symm (clemma-ty∼ eq ctx)
  clemma-ty∼ (∼trans eq eq₁) ctx =
    ∼trans (clemma-ty∼ eq ctx) (clemma-ty∼ eq₁ ctx)
  clemma-ty∼ (∼Pi eq eq₁) ctx with invert-ctx-ty∼ eq₁
  clemma-ty∼ (∼Pi eq eq₁) ctx | ⊢# q x =
    ∼Pi (clemma-ty∼ eq ctx) (clemma-ty∼ eq₁
      (ceq# ctx (clemma-ty x ctx) (∼refl x) (∼refl (clemma-ty x ctx))))
  clemma-ty∼ (∼El x) ctx = ∼El (clemma-tm∼ x ctx)

  clemma-tm∼ : ∀{Θ Γ Δ A t s i}
             → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ⊢ Γ ∼ Δ → Θ ∷ Δ ⊢ t ∼ s ∶ A
  clemma-tm∼ (∼refl x) ctx = ∼refl (clemma-tm x ctx)
  clemma-tm∼ (∼symm eq) ctx = ∼symm (clemma-tm∼ eq ctx)
  clemma-tm∼ (∼trans e1 e2) ctx = ∼trans (clemma-tm∼ e1 ctx) (clemma-tm∼ e2 ctx)
  clemma-tm∼ (∼β x x₁ x₂) ctx = ∼β (clemma-ctx ctx) x₁ x₂
  clemma-tm∼ (∼ξ x eq) ctx with invert-ctx-tm∼ eq
  clemma-tm∼ (∼ξ x eq) ctx | ⊢# q y =
    ∼ξ (clemma-ty∼ x ctx) (clemma-tm∼ eq (ceq# ctx (clemma-ty y ctx)
      (∼refl y) (∼refl (clemma-ty y ctx))))
  clemma-tm∼ (∼compPi e1 e2) ctx with invert-ctx-tm∼ e2
  clemma-tm∼ (∼compPi e1 e2) ctx | ⊢# q x =
    ∼compPi (clemma-tm∼ e1 ctx) (clemma-tm∼ e2 (ceq# ctx (clemma-ty x ctx)
      (∼refl x) (∼refl (clemma-ty x ctx))))
  clemma-tm∼ (∼coe eq x) ctx = ∼coe (clemma-tm∼ eq ctx) (clemma-ty∼ x ctx)
  clemma-tm∼ (∼compApp eq eq' Bd) ctx =
    ∼compApp (clemma-tm∼ eq ctx) (clemma-tm∼ eq' ctx)
      (clemma-ty Bd (ceq# ctx ih (∼refl ihc) (∼refl ih)))
    where ihc = proj₂ (invert-ctx-aux (invert-ctx-ty Bd))
          ih = clemma-ty ihc ctx
