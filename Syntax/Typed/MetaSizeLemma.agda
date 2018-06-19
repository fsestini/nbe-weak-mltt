module Syntax.Typed.MetaSizeLemma where

open import Function
open import Utils
open import Syntax.Raw.Term
open import Syntax.Typed.Typed
open import Syntax.Typed.Context
open import Syntax.Typed.Inversion
open import Syntax.Raw.Renaming
open import Syntax.Raw.Substitution
open import Syntax.Raw.MetaSubstitution
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Syntax.Typed.Model

private

  ⊧_ : Ctxtₗ → Set
  ⊧ ◇ = ⊤
  ⊧ (Θ # A) = ⊧ Θ × MTm (clen Θ) A

  infix 4 ⊧_∷_
  ⊧_∷_ : Ctxtₗ → Ctxt → Set
  ⊧ Θ ∷ ◇ = ⊧ Θ
  ⊧ Θ ∷ (Γ # A) = ⊧ Θ ∷ Γ × MTm (clen Θ) A

  inv-c : ∀{Θ Γ} → ⊧ Θ ∷ Γ →  ⊧ Θ
  inv-c {Γ = ◇} c = c
  inv-c {Γ = Γ # x} (c ,, a) = inv-c {Γ = Γ} c

  infix 4 _∷_⊧_
  _∷_⊧_ : Ctxtₗ → Ctxt → Term → Set
  Θ ∷ Γ ⊧ A = MTm (clen Θ) A

  infix 4 _∷_⊧_∼_
  _∷_⊧_∼_ : Ctxtₗ → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ A ∼ B = MTm (clen Θ) A × MTm (clen Θ) B

  infix 4 _∷_⊧_∶_
  _∷_⊧_∶_ : Ctxtₗ → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ t ∶ A = Θ ∷ Γ ⊧ A × MTm (clen Θ) t

  infix 4 _∷_⊧_∼_∶_
  _∷_⊧_∼_∶_ : Ctxtₗ → Ctxt → Term → Term → Term → Set
  Θ ∷ Γ ⊧ t ∼ s ∶ A = Θ ∷ Γ ⊧ A × MTm (clen Θ) t × MTm (clen Θ) s

  mmm : ∀{Θ A n} → ⊧ Θ → Θ [ n ]ₗ↦ A → Θ ∷ ◇ ⊧ Free n ∶ A
  mmm (c ,, a) (here x) rewrite x = (liftMTm 1 a) ,, (mtmFree (≤refl _))
  mmm (c ,, a) (there x) with mmm c x
  mmm (c ,, a) (there x) | p ,, q = (liftMTm 1 p) ,, mtmFree (uhm (↦ₗlemma x))

  vvv : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → Θ ∷ Γ ⊧ A
  vvv (_ ,, a) here = wkMTm a
  vvv (c ,, _) (there x) = wkMTm (vvv c x)

msizeModel : Model
msizeModel = record
  { ⊧⊧_ = ⊧_ ; ⊧_∷_ = ⊧_∷_ ; _∷_⊧_ = _∷_⊧_ ; _∷_⊧_∶_ = _∷_⊧_∶_
  ; _∷_⊧_∼_ = _∷_⊧_∼_ ; _∷_⊧_∼_∶_ = _∷_⊧_∼_∶_
  ; M-⊢ₘ◇ = tt ; M-⊢ₘ# = _,,_ ; M-⊢◇ = id ; M-⊢# = _,,_ ; M-U = λ _ → mtmU
  ; M-El = p2 ; M-Π = λ _ → mtmPi
  ; M-free = λ {Θ} {Γ} _ c x → mmm (inv-c {Γ = Γ} c) x
  ; M-bound = λ x x₁ → vvv x x₁ ,, mtmVar
  ; M-lam = λ x x₁ x₂ → (mtmPi x₁ (p1 x₂)) ,, (mtmLam x₁ (p2 x₂))
  ; M-app = λ _ _ x y z → (mtm-sub zero z (p2 y)) ,, (mtmApp (p2 x) (p2 y))
  ; M-U-Π = λ _ x y → mtmU ,, mtmPi (p2 x) (p2 y)
  ; M-coe = λ x y → p2 y ,, p2 x ; M-∼refl = λ x → x ,, x
  ; M-∼symm = λ x → p2 x ,, p1 x ; M-∼trans = λ x y → p1 x ,, p2 y
  ; M-∼Pi = λ _ _ z w → mtmPi (p1 z) (p1 w) ,, mtmPi (p2 z) (p2 w) ; M-∼El = p2
  ; M-∼refl' = λ x → p1 x ,, p2 x ,, p2 x
  ; M-∼symm' = λ x → p1 x ,, p2 (p2 x) ,, p1 (p2 x)
  ; M-∼trans' = λ x y → p1 y ,, p1 (p2 x) ,, p2 (p2 y)
  ; M-∼coe = λ x y → p2 y ,, p2 x
  ; M-∼β = λ x x₁ x₂ x₃ x₄ →
      mtm-sub zero (p1 x₃) (p2 x₄) ,, mtmApp (mtmLam (p1 x₄) (p2 x₃)) (p2 x₄) ,,
      mtm-sub zero (p2 x₃) (p2 x₄)
  ; M-∼ξ = λ x y z → mtmPi (p1 y) (p1 z) ,, mtmLam (p1 y) (p1 (p2 z)) ,,
                     mtmLam (p2 y) (p2 (p2 z))
  ; M-∼compPi = λ x y z → p1 z ,, mtmPi (p1 (p2 y)) (p1 (p2 z)) ,,
                          mtmPi (p2 (p2 y)) (p2 (p2 z))
  ; M-∼compApp = λ x y z w →
      mtm-sub zero w (p1 (p2 z)) ,, mtmApp (p1 (p2 y)) (p1 (p2 z)) ,,
      mtmApp (p2 (p2 y)) (p2 (p2 z)) }

open Modeling msizeModel

mctxMLen = model-mctx
ctxMLen = model-ctx
tyMLen = model-ty
tmMLen = model-tm
ty∼MLen = model-ty∼
tm∼MLen = model-tm∼


mtm-var-lemma : ∀{Θ A n} → ⊢ Θ → Θ [ n ]ₗ↦ A → MTm n A
mtm-var-lemma (⊢# c a) (here x) rewrite x = tyMLen a
mtm-var-lemma (⊢# c a) (there x) = mtm-var-lemma c x


--   ₗ↦MLen : ∀{Θ A n i} → ⊢⟨ i ⟩ Θ → Θ [ n ]ₗ↦ A → MTm (clen Θ) A
--   ₗ↦MLen ⊢◇ ()
--   ₗ↦MLen (⊢# ctx x₁) (here x) = liftMTm 1 (tyMLen x₁)
--   ₗ↦MLen (⊢# ctx x₁) (there x) = liftMTm 1 (ₗ↦MLen ctx x)

--   ↦MLen : ∀{Θ Γ A n i} → ⊢⟨ i ⟩ Θ ∷ Γ → Γ [ n ]↦ A → MTm (clen Θ) A
--   ↦MLen (⊢◇ x₁) ()
--   ↦MLen (⊢# ctx x₁) here = wkMTm $ tyMLen x₁
--   ↦MLen (⊢# ctx x₁) (there x) = wkMTm $ ↦MLen ctx x

--   ₗ↦MLen' : ∀{Θ A n i} → ⊢⟨ i ⟩ Θ → Θ [ n ]ₗ↦ A → MTm (clen Θ) (Free n)
--   ₗ↦MLen' ⊢◇ ()
--   ₗ↦MLen' (⊢# ctx x₁) (here x) rewrite x = mtmFree (≤refl _)
--   ₗ↦MLen' (⊢# ctx x₁) (there x) = liftMTm 1 (ₗ↦MLen' ctx x)
