module Syntax.Typed.MetaSubstitution where

open import Size
open import Relation.Nullary
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p₁ ; proj₂ to p₂)
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Context
open import Syntax.Typed.SizeLemma
open import Syntax.Typed.MetaSizeLemma
  hiding (⊧_ ; ⊧_∷_ ; _∷_⊧_ ; _∷_⊧_∶_ ; _∷_⊧_∼_∶_ ; _∷_⊧_∼_)
open import Syntax.Typed.Renaming
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Typed.ContextLemma
import Relation.Binary.EqReasoning
import Relation.Binary.PreorderReasoning as Pre
open import Data.Empty

infix 4 _⊢ₘₛ_∶_
data _⊢ₘₛ_∶_ : Ctxtₗ → MetaSubst → Ctxtₗ → Set where
  ⊢⟨⟩   : ∀{Θ} → ⊢ Θ → Θ ⊢ₘₛ ⟨⟩ ∶ ◇
  ⊢Cons : ∀{Δ Γ A σ t} → Δ ⊢ₘₛ σ ∶ Γ → Δ ∷ ◇ ⊢ t ∶ msub A σ
        → Δ ⊢ₘₛ σ , t ∶ Γ # A

c-sub-len : ∀{σ Δ Θ} → Θ ⊢ₘₛ σ ∶ Δ → msLen σ ≡ clen Δ
c-sub-len (⊢⟨⟩ x) = refl
c-sub-len (⊢Cons σ x) = cong suc (c-sub-len σ)

⊧_ : Ctxt → Set
⊧ Δ = ∀{σ Θ} → Θ ⊢ₘₛ σ ∶ Δ → ⊢ Θ

⊧_∷_ : Ctxt → Ctxt → Set
⊧ Δ ∷ Γ = ∀{σ Θ} → Θ ⊢ₘₛ σ ∶ Δ → ⊢ Θ ∷ msubc Γ σ

_∷_⊧_ : Ctxt → Ctxt → Term → Set
Θ ∷ Γ ⊧ A = ∀{σ Δ} → Δ ⊢ₘₛ σ ∶ Θ → Δ ∷ msubc Γ σ ⊢ msub A σ

infix 4 _∷_⊧_∶_
_∷_⊧_∶_ : Ctxt → Ctxt → Term → Term → Set
Θ ∷ Γ ⊧ t ∶ A = ⊧ Θ ∷ Γ
              × (∀{σ Δ} → Δ ⊢ₘₛ σ ∶ Θ → Δ ∷ msubc Γ σ ⊢ msub t σ ∶ msub A σ)

_∷_⊧_∼_ : Ctxt → Ctxt → Term → Term → Set
Θ ∷ Γ ⊧ A ∼ B = ⊧ Θ ∷ Γ × (∀{σ Δ} → Δ ⊢ₘₛ σ ∶ Θ → Δ ∷ msubc Γ σ ⊢ msub A σ ∼ msub B σ)

_∷_⊧_∼_∶_ : Ctxt → Ctxt → Term → Term → Term → Set
Θ ∷ Γ ⊧ t ∼ s ∶ A = ⊧ Θ ∷ Γ
  × (∀{σ Δ} → Δ ⊢ₘₛ σ ∶ Θ → Δ ∷ msubc Γ σ ⊢ msub t σ ∼ msub s σ ∶ msub A σ)

⊢msub-mctx : ∀{Θ} → ⊢ Θ → ⊧ Θ
⊢msub-mctx ctx (⊢⟨⟩ c) = c
⊢msub-mctx (⊢# ctx x₁) (⊢Cons σ x) = ⊢msub-mctx ctx σ

⊢msub-var : ∀{Θ Γ A σ n} → ⊢ Θ ∷ Γ → Γ [ n ]↦ A → msubc Γ σ [ n ]↦ msub A σ
⊢msub-var (⊢◇ x₁) ()
⊢msub-var (⊢# {A = A} ctx t) here = ≡↦ (sym (msub-wk A {!!})) here
⊢msub-var (⊢# ctx t) (there {A = A} x) =
  ≡↦ (sym (msub-wk A {!!})) (there (⊢msub-var ctx x))

mutual

  ⊢msub-ctx : ∀{Θ Γ} → ⊢ Θ ∷ Γ → ⊧ Θ ∷ Γ
  ⊢msub-ctx (⊢◇ x) = λ σ → ⊢◇ (⊢msub-mctx x σ)
  ⊢msub-ctx (⊢# ctx x) = λ σ → ⊢# (⊢msub-ctx ctx σ) (⊢msub-ty x σ)

  ⊢msub-ty : ∀{Θ Γ A} → Θ ∷ Γ ⊢ A → Θ ∷ Γ ⊧ A
  ⊢msub-ty (U x) = λ σ → U (⊢msub-ctx x σ)
  ⊢msub-ty (El x) = λ σ → El (proj₂ (⊢msub-tm x) σ)
  ⊢msub-ty (Π ty ty') = λ σ →
    Π (⊢msub-ty ty σ) (⊢msub-ty ty' σ)

  ⊢msub-free' : ∀{n σ Θ Δ A} → ⊢ Θ → Δ ⊢ₘₛ σ ∶ Θ → Θ [ n ]ₗ↦ A
              → Δ ∷ ◇ ⊢ msub-var n σ ∶ msub A σ
  ⊢msub-free' _ (⊢⟨⟩ _) ()
  ⊢msub-free' {n} (⊢# ctx ty) (⊢Cons {σ = σ} σp y) (here x) with n ≟ msLen σ
  ⊢msub-free' {n} (⊢# {A = A} ctx ty) (⊢Cons {σ = σ} {t = t} σp y) (here x)
    | yes p =
    ≡tm (sym (mtm-msub-lemma {σ} {A} {t} {n} (trans x (sym (c-sub-len σp)))
      (MTm≡ (sym x) refl aux))) refl y where aux = tyMLen ty
  ⊢msub-free' (⊢# ctx ty) (⊢Cons σp y) (here x) | no ¬p =
    ⊥-elim (¬p (trans x (sym (c-sub-len σp))))
  ⊢msub-free' {n} (⊢# ctx ty) (⊢Cons {σ = σ} σp y) (there x) with n ≟ msLen σ
  ⊢msub-free' {n} (⊢# ctx ty) (⊢Cons {σ = σ} σp y) (there x) | yes p =
    {!!}
  ⊢msub-free' {n} (⊢# ctx ty) (⊢Cons {σ = σ} σp y) (there x) | no ¬p =
    ≡tm {!!} refl (⊢msub-free' ctx σp x)

  ⊢msub-free : ∀{σ n Θ Δ Γ A} → ⊢ Θ ∷ Γ → Δ ⊢ₘₛ σ ∶ Θ → Θ [ n ]ₗ↦ A
             → Δ ∷ msubc Γ σ ⊢ msub-var n σ ∶ msub A σ
  ⊢msub-free (⊢◇ ctx) σp x = ⊢msub-free' ctx σp x
  ⊢msub-free (⊢# ctx x₁) σp x =
    ≡tm {!!} {!!} (⊢wk-tm (⊢Up ⊢Id (⊢msub-ty x₁ σp)) (⊢msub-free ctx σp x))

  ⊢msub-tm : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Γ ⊧ t ∶ A
  ⊢msub-tm (free x x₁) = ⊢msub-ctx x ,, λ σ → ⊢msub-free x σ x₁
  ⊢msub-tm (bound x x₁) = ⊢msub-ctx x ,, λ σ →
    bound (⊢msub-ctx x σ) (⊢msub-var x x₁)
  -- ⊢msub-tm (lam x td) = p₁ (⊢msub-ty x) ,, λ σ →
  --   lam (p₂ (⊢msub-ty x) σ) (p₂ (⊢msub-tm td) σ)
  ⊢msub-tm (app td sd) = p₁ (⊢msub-tm td) ,, λ σ →
    ≡tm {!!} refl (app (p₂ (⊢msub-tm td) σ) (p₂ (⊢msub-tm sd) σ))
  ⊢msub-tm (U-Π Ad Bd) = p₁ (⊢msub-tm Ad) ,, λ σ →
    U-Π (p₂ (⊢msub-tm Ad) σ) (p₂ (⊢msub-tm Bd) σ)
  ⊢msub-tm (coe td eq) = {!!}
  ⊢msub-tm (lam td) = {!!}

--   ⊢sub-ty-∼ : ∀{Θ Γ A B} → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Γ ⊧ A ∼ B
--   ⊢sub-ty-∼ (∼refl x) = p₁ ih ,, λ σ → ∼refl (p₂ ih σ) where ih = ⊢sub-ty x
--   ⊢sub-ty-∼ (∼symm eq) = p₁ ih ,, λ σ → ∼symm (p₂ ih σ) where ih = ⊢sub-ty-∼ eq
--   ⊢sub-ty-∼ (∼trans eq eq') = p₁ ih ,, λ σ → ∼trans (p₂ ih σ) (p₂ ih' σ)
--     where ih = ⊢sub-ty-∼ eq ; ih' = ⊢sub-ty-∼ eq'
--   ⊢sub-ty-∼ (∼Pi x eq eq') =
--     p₁ ih' ,, λ σ → ∼Pi (p₂ ih σ) (p₂ ih' σ) (p₂ ih'' (⊢sh σ (p₁ ih σ) (p₂ ih σ)))
--     where ih = ⊢sub-ty x ; ih' = ⊢sub-ty-∼ eq ; ih'' = ⊢sub-ty-∼ eq'
--   ⊢sub-ty-∼ (∼El x) = p₁ ih ,, λ σ → ∼El (p₂ ih σ) where ih = ⊢sub-tm-∼ x

--   ⊢sub-tm-∼ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊧ t ∼ s ∶ A
--   ⊢sub-tm-∼ (∼refl x) = p₁ ih ,, λ σ → ∼refl (p₂ ih σ) where ih = ⊢sub-tm x
--   ⊢sub-tm-∼ (∼symm eq) = p₁ ih ,, λ σ → ∼symm (p₂ ih σ) where ih = ⊢sub-tm-∼ eq
--   ⊢sub-tm-∼ (∼trans eq eq') = p₁ ih ,, λ σ → ∼trans (p₂ ih σ) (p₂ ih' σ)
--     where ih = ⊢sub-tm-∼ eq ; ih' = ⊢sub-tm-∼ eq'
--   ⊢sub-tm-∼ (∼β {A = A} {B = B} {t = t} {s = s} ctx td sd) =
--     ⊢sub-ctx ctx ,, λ { {σ} σp →
--     ≡∼ (sym (null-sub {σ} (tmApp tmB (tmLam tmA tmt) tms)))
--        (sym (null-sub {σ} {t [ s ]} (sub-cover-lemma 0 0 tmt tms)))
--        (sym (null-sub {σ} {B [ s ]} (sub-cover-lemma 0 0 tmB tms)))
--        (∼β (⊢sub-ctx ctx σp) td sd) }
--     where
--       ih = ⊢sub-tm td ; ih' = ⊢sub-tm sd
--       tmt = p₂ (tmLen td) ; tmB = p₂ (p₁ (tmLen td)) ; tms = p₂ (tmLen sd)
--       tmA = p₂ (p₁ (tmLen sd))
--   ⊢sub-tm-∼ (∼recZ {A = A} {z = z} {s = s} ctx Ad zd sd) =
--     ⊢sub-ctx ctx ,, λ { {σ} σp →
--     ≡∼ (sym (null-sub {σ} (tmRec tmA tmz tms tmZero)))
--        (sym (null-sub {σ} tmz))
--        (sym (null-sub {σ} {A [ Zero ]} (sub-cover-lemma 0 0 tmA tmZero)))
--        (∼recZ (⊢sub-ctx ctx σp) Ad zd sd) }
--     where
--       tmA = p₂ (tyLen Ad) ; tmz = p₂ (tmLen zd) ; tms = p₂ (tmLen sd)
--   ⊢sub-tm-∼ (∼recS ctx Ad zd sd nd) = ⊢sub-ctx ctx ,, λ { {σ} σp →
--     ≡∼ (sym (null-sub {σ} (tmRec tmA tmz tms (tmSucc tmn))))
--        (sym (null-sub {σ} (tmRecSApp tmA tmz tms tmn)))
--        (sym (null-sub {σ} (sub-cover-lemma 0 0 tmA (tmSucc tmn))))
--        (∼recS (⊢sub-ctx ctx σp) Ad zd sd nd) }
--     where
--       tmA = p₂ (tyLen Ad) ; tmz = p₂ (tmLen zd)
--       tms = p₂ (tmLen sd) ; tmn = p₂ (tmLen nd)
--   ⊢sub-tm-∼ (∼ξ {B = B} ty eq eq') = p₁ ih ,,
--     λ σ → ∼ξ (p₂ ih σ) (p₂ ih' σ) (p₂ ih'' (⊢sh σ (p₁ ih σ) (p₂ ih σ)))
--     where ih = ⊢sub-ty ty ; ih' = ⊢sub-ty-∼ eq ; ih'' = ⊢sub-tm-∼ eq'
--   ⊢sub-tm-∼ (∼compSucc eq) = p₁ ih ,, λ σ → ∼compSucc (p₂ ih σ)
--     where ih = ⊢sub-tm-∼ eq
--   ⊢sub-tm-∼ (∼compPi x eq eq') = p₁ ih' ,,
--     λ σ → ∼compPi (p₂ ih σ) (p₂ ih' σ) (p₂ ih'' (⊢sh σ (p₁ ih σ) (p₂ ih σ)))
--     where ih = ⊢sub-ty x ; ih' = ⊢sub-tm-∼ eq ; ih'' = ⊢sub-tm-∼ eq'
--   ⊢sub-tm-∼ (∼compApp {s = s} {B = B} Ad eq eq' eq'') = p₁ ih' ,, λ { {σ} σp →
--     ≡∼ refl refl (sym (sub-comp-aux B s σ))
--       (∼compApp (p₂ aih σp) (p₂ ih (⊢sh σp (p₁ ih' σp) (p₂ aih σp)))
--       (p₂ ih' σp) (p₂ ih'' σp)) }
--     where
--       aih = ⊢sub-ty Ad ; ih = ⊢sub-ty-∼ eq
--       ih' = ⊢sub-tm-∼ eq' ; ih'' = ⊢sub-tm-∼ eq''
--   ⊢sub-tm-∼ (∼compRec {A = A} {n = n} eq eq' eq'' eq''') = p₁ ih₂ ,,
--     λ { {σ} σp → ≡∼ refl refl (sym (sub-comp-aux A n σ))
--       (∼compRec (p₂ ih (⊢sh σp (p₁ ih₂ σp) (El (U-N (U (p₁ ih₂ σp))))))
--         (≡∼ refl refl (sub-comp-aux A Zero σ) (p₂ ih₂ σp))
--         (≡∼ refl refl (cong₂ Π refl (cong (Π (sub A (sh σ))) (sub-swap-aux A σ)))
--           (p₂ ih₃ σp)) (p₂ ih₄ σp)) }
--     where
--       ih = ⊢sub-ty-∼ eq ; ih₂ = ⊢sub-tm-∼ eq'
--       ih₃ = ⊢sub-tm-∼ eq'' ; ih₄ = ⊢sub-tm-∼ eq'''
