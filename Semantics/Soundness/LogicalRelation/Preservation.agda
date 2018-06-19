module Semantics.Soundness.LogicalRelation.Preservation where

open import Data.Nat
open import Function
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness.Type.Type
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


≡preserv𝒰 : ∀{Θ Γ A B X} {ty : X ∈𝒰}
           → A ≡ B → Θ ∷ Γ ⊢ A ®𝒰 ty → Θ ∷ Γ ⊢ B ®𝒰 ty
≡preserv𝒰 refl p = p

≡preserv : ∀{Θ Γ A B X} {ty : X ∈𝒯}
           → A ≡ B → Θ ∷ Γ ⊢ A ® ty → Θ ∷ Γ ⊢ B ® ty
≡preserv refl p = p

∼preservation𝒰 : ∀{Θ Γ A B X} {ty : X ∈𝒰}
               → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Γ ⊢ A ®𝒰 ty → Θ ∷ Γ ⊢ B ®𝒰 ty
∼preservation𝒰 {ty = uNe x} eq rel = ∼trans (∼symm eq) rel
∼preservation𝒰 {ty = uPi _ _ _} eq (®𝒰Π conv rel rel') =
  ®𝒰Π (∼trans (∼symm eq) conv) rel rel'

∼preservation : ∀{Θ Γ A B X} {ty : X ∈𝒯}
              → Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Γ ⊢ A ® ty → Θ ∷ Γ ⊢ B ® ty
∼preservation {ty = 𝒰⊆𝒯 x} eq rel = ∼preservation𝒰 eq rel
∼preservation {ty = tU} eq rel = ∼trans (∼symm eq) rel
∼preservation {ty = tPi _ _ _} eq (®𝒯Π conv rel rel') =
  ®𝒯Π (∼trans (∼symm eq) conv) rel rel'

≡preserv𝒰-tm : ∀{Θ Γ A B X t s a} {ty : X ∈𝒰} {d : P (El𝒰 ty) a}
              → A ≡ B → t ≡ s
              → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ d
              → Θ ∷ Γ ⊢ s ∶ B ®𝒰 ty ∋ d
≡preserv𝒰-tm refl refl p = p

∼preservation𝒰-tm : ∀{Θ Γ A B X t s a} {ty : X ∈𝒰} {d : P (El𝒰 ty) a}
                  → Θ ∷ Γ ⊢ A ∼ B
                  → Θ ∷ Γ ⊢ t ∼ s ∶ A
                  → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ d
                  → Θ ∷ Γ ⊢ s ∶ B ®𝒰 ty ∋ d
∼preservation𝒰-tm {ty = uPi _ _ _} eq eq' (®𝒰λ qh ty pf x h x₃ x₄) =
  ®𝒰λ qh ty pf (∼trans (∼symm eq) x) h (∼coe (∼trans (∼symm eq') x₃) eq) x₄
∼preservation𝒰-tm {ty = uPi _ _ _} eq eq' (®𝒰Ne x₂ x₃ k) =
  ®𝒰Ne x₂ (∼coe (∼trans (∼symm eq') x₃) eq) (∼trans (∼symm eq) k)
∼preservation𝒰-tm {ty = uNe x} eq eq' (h1 ,, h2) =
  ∼trans (∼symm eq) h1 ,, ∼coe (∼trans (∼symm eq') h2) eq

≡preserv-tm : ∀{Θ Γ A B X t s a} {ty : X ∈𝒯} {d : P (El𝒯 ty) a}
            → A ≡ B → t ≡ s
            → Θ ∷ Γ ⊢ s ∶ B ® ty ∋ d
            → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ d
≡preserv-tm refl refl p = p

∼preservation-tm : ∀{Θ Γ A B X t s a} {ty : X ∈𝒯} {d : P (El𝒯 ty) a}
                 → Θ ∷ Γ ⊢ A ∼ B
                 → Θ ∷ Γ ⊢ t ∼ s ∶ A
                 → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ d
                 → Θ ∷ Γ ⊢ s ∶ B ® ty ∋ d
∼preservation-tm {ty = 𝒰⊆𝒯 x} = ∼preservation𝒰-tm
∼preservation-tm {ty = tU} {d} eq eq' (rel ,, rel' ,, rel'') =
  (∼trans (∼symm eq) rel) ,, ∼preservation𝒰 (∼El (∼coe eq' rel)) rel' ,,
  ∼trans (∼coe (∼symm eq') rel) rel''
∼preservation-tm {ty = tPi _ _ _} {d} eq eq' (®𝒯λ qh ty pf x₃ z x₅ x₆) =
  ®𝒯λ qh ty pf (∼trans (∼symm eq) x₃) z (∼coe (∼trans (∼symm eq') x₅) eq) x₆
∼preservation-tm {ty = tPi _ _ _} {d} eq eq' (®𝒯Ne x₃ x₄ k) =
  ®𝒯Ne x₃ (∼coe (∼trans (∼symm eq') x₄) eq) (∼trans (∼symm eq) k)
