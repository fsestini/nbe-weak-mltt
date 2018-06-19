module Syntax.Raw.Evaluation.Redex where

open import Syntax.Raw.Term
open import Syntax.Raw.NormalForm
open import Syntax.Raw.Substitution
open import Data.Empty
open import Data.Sum renaming ([_,_] to [_,,,_])
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

data β-Redex : Term → Term → Set where
  βrdx : ∀{A t s} → Tm 0 A → Tm 1 t → Tm 0 s → β-Redex (Lam A t) s

data β-Redex-Subj : Term → Set where
  brsLam : ∀{A t} → Nf A → Nf t → β-Redex-Subj (Lam A t)
  brsNe  : ∀{t} → Ne t → β-Redex-Subj t

βSubjIsNf : ∀{t} → β-Redex-Subj t → Nf t
βSubjIsNf (brsLam x x₁) = nfLam x x₁
βSubjIsNf (brsNe x) = nfNe x

decβ-Redex : ∀{s t} → β-Redex-Subj t → Nf s → β-Redex t s ⊎ Ne (App t s)
decβ-Redex {s} (brsLam {A} {t} x x₁) nf-s with decTm 0 A | decTm 1 t | decTm 0 s
decβ-Redex (brsLam _ _) _ | inj₁ x₂ | inj₁ x₃ | inj₁ x₄ = inj₁ (βrdx x₂ x₃ x₄)
decβ-Redex (brsLam x x₁) nf-s | _ | _ | inj₂ y = inj₂ (inj-neApp₂ (nfLam x x₁) nf-s y)
decβ-Redex (brsLam x x₁) nf-s | inj₁ x₂ | inj₂ y | _ =
  inj₂ (neApp₁ (nfLam x x₁) nf-s (¬tmLam₂ x₂ y))
decβ-Redex (brsLam x x₁) nf-s | inj₂ y | _ | inj₁ x₃ =
  inj₂ (neApp₁ (nfLam x x₁) nf-s (¬tmLam₁ y))
decβ-Redex (brsNe x) nf-s = inj₂ (inj-neApp x nf-s)

NeApp¬β : ∀{t s} → Ne (App t s) → β-Redex t s → ⊥
NeApp¬β (neApp () x x₁ x₂) (βrdx x₃ x₄ x₅)
NeApp¬β (neApp₁ x x₁ x₂) (βrdx x₃ x₄ x₅) = ¬Tm-lemma x₂ (tmLam x₃ x₄)
NeApp¬β (neApp₂ x x₁ x₂ x₃) (βrdx x₄ x₅ x₆) = ¬Tm-lemma x₃ x₆

β-Redex-Tm-t : ∀{t s} → β-Redex t s → Tm 0 t
β-Redex-Tm-t (βrdx x₁ x₂ x₃) = tmLam x₁ x₂

β-Redex-Tm-Lam-A : ∀{A t s} → β-Redex (Lam A t) s → Tm 0 A
β-Redex-Tm-Lam-A (βrdx x₁ x₂ x₃) = x₁

β-Redex-Tm-Lam-t : ∀{A t s} → β-Redex (Lam A t) s → Tm 1 t
β-Redex-Tm-Lam-t (βrdx x₁ x₂ x₃) = x₂

β-Redex-Tm-s : ∀{t s} → β-Redex t s → Tm 0 s
β-Redex-Tm-s (βrdx x₁ x₂ x₃) = x₃

Lam-inj : ∀{A t A' t'} → Lam A t ≡ Lam A' t' → t ≡ t'
Lam-inj refl = refl
