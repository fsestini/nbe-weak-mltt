module Syntax.Raw.NormalForm.NormalForm where

open import Syntax.Raw.Term
open import Data.Empty
open import Syntax.Raw.Substitution
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality

mutual

  data Nf : Term → Set where
    nfLam : ∀{A t} → Nf A → Nf t → Nf (Lam A t)
    nfU    : Nf U
    nfPi   : ∀{A B} → Nf A → Nf B → Nf (Π A B)
    nfNe   : ∀{t} → Ne t → Nf t

  data Ne : Term → Set where

    neApp : ∀{t s} → Ne t → Nf s → Tm 0 t → Tm 0 s → Ne (App t s)
    neApp₁ : ∀{t s} → Nf t → Nf s → ¬Tm 0 t → Ne (App t s)
    neApp₂ : ∀{t s} → Nf t → Nf s → Tm 0 t → ¬Tm 0 s → Ne (App t s)

    neFree : ∀{x} → Ne (Free x)
    neBound : ∀{x} → Ne (Bound x)

proj-lam : ∀{A t} -> Nf (Lam A t) -> Nf t
proj-lam (nfLam nf nf₁) = nf₁
proj-lam (nfNe ())
