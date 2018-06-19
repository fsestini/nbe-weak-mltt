module Syntax.Raw.Evaluation.Evaluation where

open import Syntax.Raw.Term
open import Syntax.Raw.NormalForm
open import Syntax.Raw.Substitution
open import Data.Empty
open import Data.Sum renaming ([_,_] to [_,,,_])
open import Syntax.Raw.Evaluation.Redex
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _,,_)

mutual
  infix 4 _●_↘_
  data _●_↘_ : Term → Term → Term → Set where
    ●β : ∀{A t s ts} → β-Redex (Lam A t) s
       → Eval sub t (Id , s) ↘ ts
       → Lam A t ● s ↘ ts
    ●Ne : ∀{t s} → Ne (App t s) → t ● s ↘ App t s

  data Eval_↘_ : Term → Term → Set where
    eBound : ∀{x} → Eval Bound x ↘ Bound x
    eFree  : ∀{x} → Eval Free x ↘ Free x
    eU     : Eval U ↘ U
    eLam   : ∀{A t A' t'}
           → Eval A ↘ A' → Eval t ↘ t'
           → Eval Lam A t ↘ Lam A' t'
    ePi    : ∀{A B A' B'} → Eval A ↘ A' → Eval B ↘ B' → Eval Π A B ↘ Π A' B'
    eApp   : ∀{t s t' s' ap}
           → Eval t ↘ t' → Eval s ↘ s' → t' ● s' ↘ ap
           → Eval App t s ↘ ap

≡App : ∀{t t' s s' a} → t ≡ t' → s ≡ s' → t ● s ↘ a → t' ● s' ↘ a
≡App refl refl e = e

≡App' : ∀{t t' s s' a b} → t ≡ t' → s ≡ s' → a ≡ b → t ● s ↘ a → t' ● s' ↘ b
≡App' refl refl refl e = e

EvLamSubj : ∀{t A d σ} → Nf t → Eval sub t σ ↘ Lam A d → β-Redex-Subj t
EvLamSubj (nfLam nf nf₁) (eLam ev ev₁) = brsLam nf nf₁
EvLamSubj nfU ()
EvLamSubj (nfPi nf nf₁) ()
EvLamSubj (nfNe x) ev = brsNe x
