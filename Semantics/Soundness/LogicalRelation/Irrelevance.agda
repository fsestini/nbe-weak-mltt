module Semantics.Soundness.LogicalRelation.Irrelevance where

open import Data.Nat
open import Function
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Semantics.Soundness.LogicalRelation.Definition

open import Size
open import Syntax.Typed.Inversion

open _[_,_]
open _[_,_]∈_
open SemTy
open _●_∈ap_
open _∈_

ty-irrel𝒰 : ∀{Θ Γ A B X Y} → A ≡ B → X ≡ Y → (ty : X ∈𝒰) → (ty' : Y ∈𝒰)
          → Θ ∷ Γ ⊢ A ®𝒰 ty → Θ ∷ Γ ⊢ B ®𝒰 ty'
ty-irrel𝒰 refl refl ty ty' rel rewrite samey𝒰 ty ty' = rel

ty-irrel𝒯 : ∀{Θ Γ A B X Y} → A ≡ B → X ≡ Y → (ty : X ∈𝒯) → (ty' : Y ∈𝒯)
           → Θ ∷ Γ ⊢ A ® ty → Θ ∷ Γ ⊢ B ® ty'
ty-irrel𝒯 refl refl ty ty' rel rewrite samey𝒯 ty ty' = rel

tm-irrel𝒰 : ∀{Θ Γ A B X Y t s a}
          → t ≡ s → A ≡ B → X ≡ Y
          → (ty : X ∈𝒰) → (ty' : Y ∈𝒰)
          → (p : P (El𝒰 ty) a) → (p' : P (El𝒰 ty') a)
          → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ p → Θ ∷ Γ ⊢ s ∶ B ®𝒰 ty' ∋ p'
tm-irrel𝒰 {Θ} {Γ} {A} {t = t}
  refl refl refl ty ty' p p' rel rewrite samey𝒰 ty ty' =
  subst (_∷_⊢_∶_®𝒰_∋_ Θ Γ t A ty') (sameyP𝒰 ty' ty' refl p p') rel

tm-irrel𝒯 : ∀{Θ Γ A B X Y t s a b}
          → t ≡ s → a ≡ b → A ≡ B → X ≡ Y
          → (ty : X ∈𝒯) → (ty' : Y ∈𝒯)
          → (p : P (El𝒯 ty) a) → (p' : P (El𝒯 ty') b)
          → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ p → Θ ∷ Γ ⊢ s ∶ B ® ty' ∋ p'
tm-irrel𝒯 {Θ} {Γ} {A} {t = t}
  refl refl refl refl ty ty' p p' rel rewrite samey𝒯 ty ty' =
  subst (_∷_⊢_∶_®_∋_ Θ Γ t A ty') (sameyP𝒯 ty' ty' refl p p') rel
