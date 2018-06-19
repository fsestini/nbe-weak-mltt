module Semantics.Completeness.Type.BetaReductionLemma where

open import Function
open import Syntax

open import Syntax
open import Semantics.Domain.Domain
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Semantics.Completeness.Type.Type
open import Semantics.Completeness.Type.UniverseProperties
open import Semantics.Completeness.Type.Lemmata
open import Semantics.Completeness.Type.Properties.AppLemma

open SemTy
open _∈_
open _[_,_]
open _●_∈ap_
open ⟦_⟧≃⟦_⟧_∈tm_
open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒰
open ⟦_⟧≃⟦_⟧_∈𝒯

open import Data.Sum
open import Function

Eval0 : ∀{t n a σ} → Tm n t → Eval sub t (shift n σ) ↘ a → Tm n a
Eval0 tm e = Eval-Tm tm (≡Eval (null-sub tm) refl e)

tmβLemma : ∀{ρ A B t s}
         → ⟦ Lam A t ⟧≃⟦ Lam A t ⟧ ρ ∈tm⟦ Π A B ⟧
         → ⟦ s ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧
         → Tm 0 A → Tm 1 t → Tm 0 s
         → ⟦ App (Lam A t) s ⟧≃⟦ sub t (Id , s) ⟧ ρ ∈tm⟦ sub B (Id , s) ⟧
tmβLemma ihlam ihs tmA tmt tms with tmAppLemma ihlam ihs
tmβLemma {t = t} _ _ _ _ _ |
  record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm
         ; ↘tm1 = eApp (eLam e1 e4) e3 (●β x x₁) ; ↘tm2 = e2 } =
  record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm
         ; ↘tm1 = eApp (eLam e1 e4) e3 (●β x x₁)
         ; ↘tm2 = tmSubLemma {t} e4 e3 x₁ }
tmβLemma ihlam ihs tmA tmt tms |
  record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm
         ; ↘tm1 = eApp (eLam e1 e4) e3 (●Ne x) ; ↘tm2 = e2 } =
  ⊥-elim (NeApp¬β x (βrdx (Eval0 tmA e1) (Eval0 tmt e4) (Eval0 tms e3)))
