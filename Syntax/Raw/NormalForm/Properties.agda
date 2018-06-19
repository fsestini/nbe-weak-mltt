module Syntax.Raw.NormalForm.Properties where

open import Syntax.Raw.NormalForm.NormalForm
open import Syntax.Raw.Term
open import Data.Empty
open import Syntax.Raw.Substitution
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality

≡Nf : ∀{t s} → t ≡ s → Nf t → Nf s
≡Nf refl nf = nf

inj-neApp : ∀{t s} → Ne t → Nf s → Ne (App t s)
inj-neApp {t} {s} ne nf with decTm 0 t | decTm 0 s
inj-neApp ne nf | inj₁ x | inj₁ x₁ = neApp ne nf x x₁
inj-neApp ne nf | inj₁ x | inj₂ y = neApp₂ (nfNe ne) nf x y
inj-neApp ne nf | inj₂ y | _ = neApp₁ (nfNe ne) nf y

inj-neApp₂ : ∀{t s} → Nf t → Nf s → ¬Tm 0 s → Ne (App t s)
inj-neApp₂ {t} {s} x y tm with decTm 0 t
inj-neApp₂ x y tm | inj₁ x₁ = neApp₂ x y x₁ tm
inj-neApp₂ x y tm | inj₂ y₁ = neApp₁ x y y₁

data NeView : Term → Set where
  NVApp : ∀{B t s} → Nf B → Nf t → Nf s → NeView (App t s)
  NVFree : ∀{x} → NeView (Free x)
  NVBound : ∀{x} → NeView (Bound x)

neView : ∀{t} → Ne t → NeView t
neView neFree = NVFree
neView neBound = NVBound
neView (neApp x₁ x₂ x₃ x₄) = NVApp x₂ (nfNe x₁) x₂
neView (neApp₁ x x₁ x₂) = NVApp x₁ x x₁
neView (neApp₂ x x₁ x₂ x₃) = NVApp x₁ x x₁

mutual
  nfWkLemma : ∀{t w} → Nf t → Nf (wk t w)
  nfWkLemma (nfLam nf nf') = nfLam (nfWkLemma nf) (nfWkLemma nf')
  nfWkLemma nfU = nfU
  nfWkLemma (nfPi nf nf₁) = nfPi (nfWkLemma nf) (nfWkLemma nf₁)
  nfWkLemma (nfNe x) = nfNe (neWkLemma x)

  neWkLemma : ∀{t w} → Ne t → Ne (wk t w)
  neWkLemma (neApp x₁ x₂ x₃ x₄) =
    neApp (neWkLemma x₁) (nfWkLemma x₂)
          (Tm≡' (sym (null-wk x₃)) x₃) (Tm≡' (sym (null-wk x₄)) x₄)
  neWkLemma (neApp₁ x x₁ x₂) =
    neApp₁ (nfWkLemma x) (nfWkLemma x₁) (sub¬Tm-lemma x₂)
  neWkLemma (neApp₂ x x₁ x₂ x₃) =
    inj-neApp₂ (nfWkLemma x) (nfWkLemma x₁) (sub¬Tm-lemma x₃)
  neWkLemma neFree = neFree
  neWkLemma neBound = neBound

mutual
  -- easy but long
  postulate sameNe : ∀{t} → (p q : Ne t) → p ≡ q

  sameNf : ∀{t} → (p q : Nf t) → p ≡ q
  sameNf (nfLam p p₁) (nfLam q q₁) = cong₂ nfLam (sameNf p q) (sameNf p₁ q₁)
  sameNf (nfLam p p₁) (nfNe ())
  sameNf nfU nfU = refl
  sameNf nfU (nfNe ())
  sameNf (nfPi p p₁) (nfPi q q₁) = cong₂ nfPi (sameNf p q) (sameNf p₁ q₁)
  sameNf (nfPi p p₁) (nfNe ())
  sameNf (nfNe ()) (nfLam q q₁)
  sameNf (nfNe ()) nfU
  sameNf (nfNe ()) (nfPi q q₁)
  sameNf (nfNe x) (nfNe y) = cong nfNe (sameNe x y)
