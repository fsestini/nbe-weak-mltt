module Semantics.Completeness.Rule where

open import Function
open import Data.Nat
open import Data.Maybe
open import Syntax
open import Semantics.Domain.Domain
open import Semantics.Completeness.Type
open import Data.Unit hiding (_≤_ ; _≟_)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Data.Sum hiding ([_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Syntax.Typed.Inversion
open import Syntax.Typed.Model
open import Syntax.Typed.MetaSizeLemma
open import Size

open SemTy
open ⟦_⟧≃⟦_⟧_∈𝒯
open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open _∈⟦_⟧_
open _∈_

data _∈⟦_⟧ : Subst → Ctxt → Set where
  cEmpty : ∀{ρ} → ρ ∈⟦ ◇ ⟧
  cExt   : ∀{Γ A ρ a} → ρ ∈⟦ Γ ⟧ → a ∈⟦ A ⟧ ρ → (ρ , a) ∈⟦ Γ # A ⟧
  cWk    : ∀{Γ ρ w} → ρ ∈⟦ Γ ⟧ → (ρ · w) ∈⟦ Γ ⟧

zero-env : ∀{Γ ρ} → ρ ∈⟦ Γ ⟧ → ρ ∈⟦ ◇ ⟧
zero-env p = cEmpty

mutual

  infix 4 ⊧_
  ⊧_ : Ctxtₗ → Set
  ⊧ ◇ = ⊤
  ⊧ (Θ # A) = ⊧ Θ × (Θ ∷ ◇ ⊧ A)

  infix 4 ⊧_∷_
  ⊧_∷_ : Ctxtₗ → Ctxt → Set
  ⊧ Θ ∷ ◇ = ⊧ Θ
  ⊧ Θ ∷ (Γ # A) = ⊧ Θ ∷ Γ × Θ ∷ Γ ⊧ A

  infix 4 _∷_⊧_
  _∷_⊧_ : Ctxt → Ctxt → Term → Set
  Θ ∷ Γ ⊧ A = ∀{ρ} → ρ ∈⟦ Γ ⟧ → ⟦ A ⟧≃⟦ A ⟧ ρ ∈𝒯

  infix 4 _∷_⊧_∶_
  _∷_⊧_∶_ : Ctxt → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ t ∶ A = Θ ∷ Γ ⊧ A × (∀{ρ} → ρ ∈⟦ Γ ⟧ → ⟦ t ⟧≃⟦ t ⟧ ρ ∈tm⟦ A ⟧)

  infix 4 _∷_⊧_∼_
  _∷_⊧_∼_ : Ctxt → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ A ∼ B = ∀{ρ} → ρ ∈⟦ Γ ⟧ → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯

  infix 4 _∷_⊧_∼_∶_
  _∷_⊧_∼_∶_ : Ctxt → Ctxt → Term → Term → Term → Set
  Θ ∷ Γ ⊧ t ∼ s ∶ A = Θ ∷ Γ ⊧ A × (∀{ρ} → ρ ∈⟦ Γ ⟧ → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧)

bound0' : ∀{A ρ} → ⟦ A ⟧≃⟦ A ⟧ ρ ∈𝒯 → Bound 0 ∈⟦ A ⟧ (ρ · Up Id)
bound0' ih = bound0 (↘t1 ih) (∈ty ih)

⊧sh : ∀{Γ A ρ} Θ → Θ ∷ Γ ⊧ A → ρ ∈⟦ Γ ⟧ → sh ρ ∈⟦ Γ # A ⟧
⊧sh Θ Ah p = cExt (cWk p) (bound0' (Ah p))

⊧sub : ∀{Γ A B B' ρ a w} Θ → Θ ∷ Γ # A ⊧ B ∼ B' → ρ ∈⟦ Γ ⟧
     → a ∈⟦ A ⟧ (ρ · w) → ⟦ B ⟧≃⟦ B' ⟧ (ρ · w , a) ∈𝒯
⊧sub Θ Bh ρ a = Bh (cExt (cWk ρ) a)

⊧sub' : ∀{Γ A B t t' ρ a w} Θ → Θ ∷ Γ # A ⊧ t ∼ t' ∶ B → ρ ∈⟦ Γ ⟧
      → a ∈⟦ A ⟧ (ρ · w) → ⟦ t ⟧≃⟦ t' ⟧ (ρ · w , a) ∈tm⟦ B ⟧
⊧sub' Θ th p a = p2 th (cExt (cWk p) a)

⊧El : ∀{Γ A B} Θ → Θ ∷ Γ ⊧ A ∼ B ∶ U → Θ ∷ Γ ⊧ A ∼ B
⊧El Θ Ah = UtoT ∘ p2 Ah

⊧ty-p1 : ∀{Γ A B} Θ → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ A
⊧ty-p1 Θ eh = ∈𝒯Left ∘ eh

⊧ty-p2 : ∀{Γ A B} Θ → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ B
⊧ty-p2 Θ eh = ∈𝒯Right ∘ eh

lift∈𝒯 : ∀{w A B ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯 → ⟦ A ⟧≃⟦ B ⟧ (ρ · w) ∈𝒯
lift∈𝒯 {w} {A} {B} ⟨ ty ∣ e1 ∣ e2 ⟩ = ⟨ wk𝒯 ty w ∣ wkEval' A e1 ∣ wkEval' B e2 ⟩

lift∈tm : ∀{w A t s ρ} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ t ⟧≃⟦ s ⟧ ρ · w ∈tm⟦ A ⟧
lift∈tm {w} {A} {t} {s}
  record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm ; ↘tm1 = t1 ; ↘tm2 = t2 } =
  record
    { ∈ty = wk𝒯 ty w ; ↘ty = wkEval' A ety ; ∈tm = ∈in (wk-tm-𝒯 w ty (wit tm))
    ; ↘tm1 = wkEval' t t1 ; ↘tm2 = wkEval' s t2 }

private
  wk-aux : ∀{B ρ a} A → A [ ρ ]↘ B → wk A (Up Id) [ ρ , a ]↘ B
  wk-aux A e = ≡Eval (sym (trans (subst-wk A) (≈ˢsub id-wk-sub-L A))) refl e

M-bound-1 : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → Θ ∷ Γ ⊧ A
M-bound-1 ch () cEmpty
M-bound-1 ch here (cExt {A = A} p a) = ⟨ ∈ty h ∣ e ∣ e ⟩
  where h = p2 ch p ; e = wk-aux A (↘t1 h)
M-bound-1 (ch ,, _) (there {A = A} x) (cExt p a) = ⟨ ∈ty h ∣ e ∣ e ⟩
  where h = M-bound-1 ch x p ; e = wk-aux A (↘t1 h)
M-bound-1 ch x (cWk p) = lift∈𝒯 (M-bound-1 ch x p)

M-bound-2 : ∀{Θ Γ A n ρ} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A
          → ρ ∈⟦ Γ ⟧ → ⟦ Bound n ⟧≃⟦ Bound n ⟧ ρ ∈tm⟦ A ⟧
M-bound-2 ch () cEmpty
M-bound-2 ch here (cExt {A = A} p a) =
  record { ∈ty = inT a ; ↘ty = ty ; ∈tm = nn a ; ↘tm1 = e ; ↘tm2 = e }
  where e = nfSelf (isNf (El𝒯 (inT a)) (wit (nn a))) ; ty = wk-aux A (ev a)
M-bound-2 (c ,, a) (there {A = A} x) (cExt p y) =
  record { ∈ty = ∈ty h ; ↘ty = wk-aux A (↘ty h) ; ∈tm = ∈tm h
         ; ↘tm1 = ↘tm1 h ; ↘tm2 = ↘tm2 h } where h = M-bound-2 c x p
M-bound-2 ch x (cWk p) = lift∈tm (M-bound-2 ch x p)

M-bound : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → Θ ∷ Γ ⊧ Bound n ∶ A
M-bound ch x = M-bound-1 ch x ,, M-bound-2 ch x

models-free1 : ∀{Θ Γ A n} → ⊧ Θ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ A
models-free1 (_ ,, a) (here x) p = a (zero-env p)
models-free1 (ch ,, _) (there x) p = models-free1 ch x p

models-free2 : ∀{Θ Γ A n} → ⊧ Θ → Θ [ n ]ₗ↦ A
             → ∀{ρ} → ρ ∈⟦ Γ ⟧ → ⟦ Free n ⟧≃⟦ Free n ⟧ ρ ∈tm⟦ A ⟧
models-free2 ch x p =
  record { ∈ty = ∈ty h ; ↘ty = ↘t1 h ; ∈tm = ∈in (hasNe (El𝒯 (∈ty h)) neFree)
         ; ↘tm1 = eFree ; ↘tm2 = eFree } where h = models-free1 ch x p

models-free : ∀{Θ Γ A n} → ⊢ Θ → ⊧ Θ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ Free n ∶ A
models-free c ctx x = models-free1 ctx x ,, models-free2 ctx x

inv-mctx : ∀{Γ Θ} → ⊧ Θ ∷ Γ → ⊧ Θ
inv-mctx {◇} c = c
inv-mctx {Γ # x} c = inv-mctx {Γ} (p1 c)

complModel : Model
complModel = record
  { ⊧⊧_ = ⊧_ ; ⊧_∷_ = ⊧_∷_ ; _∷_⊧_ = _∷_⊧_ ; _∷_⊧_∶_ = _∷_⊧_∶_ ; _∷_⊧_∼_ = _∷_⊧_∼_
  ; _∷_⊧_∼_∶_ = _∷_⊧_∼_∶_ ; M-⊢ₘ◇ = tt ; M-⊢ₘ# = _,,_ ; M-⊢◇ = id ; M-⊢# = _,,_
  ; M-U = λ _ _ → record { ∈ty = tU ; ↘t1 = eU ; ↘t2 = eU }
  ; M-El = λ {Θ} → ⊧El Θ ; M-Π = λ {Θ} ch Ah Bh ρ → piLemma (Ah ρ) (⊧sub Θ Bh ρ)
  ; M-free = λ {Θ} {Γ} c x y → models-free (invert-ctx-ctx c) (inv-mctx {Γ} x) y
  ; M-bound = λ ch x → M-bound-1 ch x ,, M-bound-2 ch x
  ; M-lam = λ {Θ} ch Ah th → let Bh = p1 th ; th' = p2 th in
    (λ ρ → piLemma (Ah ρ) (⊧sub Θ Bh ρ)) ,,
     λ ρ → lamLemma (Ah ρ) (⊧sub' Θ th ρ)
  ; M-app = λ ch Ah th sh Bh →
    (λ ρ → subTyLemma (p1 sh ρ) (p1 th ρ) (p2 sh ρ)) ,,
    (λ ρ → tmAppLemma (p2 th ρ) (p2 sh ρ))
  ; M-U-Π = λ {Θ} ch Ah Bh →
    p1 Ah ,, λ ρ → piLemmaU (p2 Ah ρ) (p2 Bh (⊧sh Θ (⊧El Θ Ah) ρ)) (⊧sub' Θ Bh ρ)
  ; M-coe = λ {Θ} th eh → ⊧ty-p2 Θ eh ,, λ ρ → coerceLemma (p2 th ρ) (eh ρ)
  ; M-∼refl = id ; M-∼symm = λ x x₂ → tySymm (x x₂)
  ; M-∼trans = λ x x₁ x₃ → tyTrans (x x₃) (x₁ x₃)
  ; M-∼Pi = λ {Θ} _ ih eq eq' ρ → piLemma (eq ρ) (⊧sub Θ eq' ρ)
  ; M-∼El = λ {Θ} → ⊧El Θ
  ; M-∼refl' = id ; M-∼symm' = λ x → p1 x ,, λ ρ → tmSymm (p2 x ρ)
  ; M-∼trans' = λ x y → p1 x ,, λ ρ → tmTrans (p2 x ρ) (p2 y ρ)
  ; M-∼coe = λ {Θ} eq eq' → ⊧ty-p2 Θ eq' ,, λ ρ → coerceLemma (p2 eq ρ) (eq' ρ)
  ; M-∼β =  λ {Θ} td sd ch th sh →
    (λ ρ → let ρ' = cEmpty in subTyLemma (p1 sh ρ')
      (piLemma (p1 sh ρ') (⊧sub Θ (p1 th) ρ')) (p2 sh ρ')) ,,
    λ ρ → let ρ' = cEmpty in tmβLemma
      (lamLemma (p1 sh ρ') (⊧sub' Θ th ρ'))
        (p2 sh ρ') (p1 $ tmLen sd) (p2 $ tmLen td) (p2 $ tmLen sd)
  ; M-∼ξ = λ {Θ} ch Ah th → let Ah' = ⊧ty-p1 Θ Ah in
    (λ ρ → piLemma (Ah' ρ) (⊧sub Θ (p1 th) ρ)) ,,
    (λ ρ → lamLemma (Ah ρ) (⊧sub' Θ th ρ))
  ; M-∼compPi = λ {Θ} x eq eq' → p1 eq ,, λ ρ →
    piLemmaU (p2 eq ρ) (p2 eq' (⊧sh Θ (⊧ty-p1 Θ (⊧El Θ eq)) ρ)) (⊧sub' Θ eq' ρ)
  ; M-∼compApp = λ _ rh sh _ →
    (λ ρ → subTyLemma (p1 sh ρ) (p1 rh ρ) (∈tmLeft $ p2 sh ρ)) ,,
    (λ ρ → tmAppLemma (p2 rh ρ) (p2 sh ρ)) }

open Modeling complModel

models-mctx = model-mctx
models-ctx = model-ctx
models-ty = model-ty
models-ty-eq = model-ty∼
models = model-tm
models-eq = model-tm∼


idid : ∀{Θ Γ} → ⊢ Θ ∷ Γ → idsub Γ ∈⟦ Γ ⟧
idid (⊢◇ x) = cEmpty
idid (⊢# c x) = cExt (cWk (idid c)) (bound0 (↘t1 aux) (∈ty aux))
  where h = idid c ; aux = models-ty x h

nf-ty : ∀{Θ Γ A} → Θ ∷ Γ ⊢ A → Term
nf-ty Ad = resT (models-ty Ad (idid (invert-ctx-ty Ad)))

nf : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → Term
nf td = res aux where aux = p2 (models td) (idid (invert-ctx-tm td))
