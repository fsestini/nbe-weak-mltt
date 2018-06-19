module Semantics.Completeness.Type.Properties.AppLemma where

open import Function
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
open import Semantics.Completeness.Type.Properties.PiLemma

open import Data.Sum
open import Function

open SemTy
open _∈_
open _[_,_]
open _●_∈ap_
open ⟦_⟧≃⟦_⟧_∈tm_
open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒰
open ⟦_⟧≃⟦_⟧_∈𝒯

appLemma : ∀{B f a} → (A : Wk → SemTy) → (nf : Nf B)
         → (Bty : ∀{a w} → P (A w) a → SemTy)
         → f ∈ SemPi A Bty → (p : a ∈ A Id)
         → f ● a ∈ap Bty (wit p)
appLemma {a = a} Aty nf Bty (∈in (_ ,, h)) pa =
  record { ∈tm = ∈tm ih ; ↘ap = ≡App (id-wk 0 _) refl (↘ap ih) }
  where ih = h {a} {Id} (wit pa)

pilam : ∀{A B f} → (pi : Π A B ∈𝒯) → (nf : Nf B)
      → f ∈ El𝒯 pi
      → f ∈ SemPi (El𝒯 ∘ proj₁ (asder2 pi))
            λ x → El𝒯 $ ∈t $ proj₂ (asder2 pi) x
pilam (𝒰⊆𝒯 (uPi x x₁ x₂)) nfB (∈in (nf ,, h)) = ∈in (nf ,, λ p → h p)
pilam (𝒰⊆𝒯 (uNe ())) _ (∈in _)
pilam (tPi x pi x₁) nfB (∈in (nf ,, h)) = ∈in (nf ,, λ p → h p)

tmAppLemma : ∀{ρ A B t t' s s'}
            → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ Π A B ⟧ → ⟦ s ⟧≃⟦ s' ⟧ ρ ∈tm⟦ A ⟧
            → ⟦ App t s ⟧≃⟦ App t' s' ⟧ ρ ∈tm⟦ sub B (Id , s) ⟧
tmAppLemma {ρ} {A} {B} {t} {t'} {s} {s'}
  iht@(record { ∈ty = ty ; ↘ty = (ePi {B' = B'} e e₁)
              ; ∈tm = tm ; ↘tm1 = e1 ; ↘tm2 = e2 }) ihs =
  record
    { ∈ty = ∈ty aucs ; ↘ty = ev ; ∈tm = aucs''
    ; ↘tm1 = eApp e1 (↘tm1 ihs) (↘ap ap)
    ; ↘tm2 = eApp e2 (↘tm2 ihs) (↘ap ap) }
  where
    Bh' = invert-Π-2 (invert-ty iht)
    Bh = Bh' (bound0 e (≡∈𝒯 (id-wk 0 _) (proj₁ (asder2 ty) Id)))

    pi = asder2 ty ; pi1 = proj₁ pi ; pi2 = proj₂ pi

    aucs = Bh' (record { ev = ≡Eval (sym (≈ˢsub sub-id-R A)) refl (↘ty ihs)
                       ; inT = ∈ty ihs ; nn = ∈tm ihs })
    aucs' : res ihs ∈ (El𝒯 (pi1 Id))
    aucs' = ∈in (sameT (sym (trans (id-wk 0 _) (Eval-fun e (↘ty ihs))))
      (∈ty ihs) (pi1 Id) (wit (∈tm ihs)))
    ap = appLemma (El𝒯 ∘ pi1) (nfEval e2)
      (λ x → El𝒯 (∈t (pi2 x))) (pilam ty (nfEval e₁) tm) aucs'
    ee = ≡Eval (≈ˢsub (≈ˢcons sub-id-R) B') refl (↘s $ pi2 (wit aucs'))
    ew = sub-comm {B} e₁ (↘t1 aucs)
    ew' =  sub-comm2 {B'} 0 ew (↘tm1 ihs)
    ev = ≡Eval (sym (trans (sub-comp B) (≈ˢsub (≈ˢtrans (sub-comp-R {s})
      (≈ˢcons subid-LR)) B))) refl (sub-uncomm {B} e₁ ew')
    aucs'' : res ap ∈ El𝒯 (∈ty aucs)
    aucs'' = ∈in (sameT (Eval-fun ee ew)
      ((∈t $ pi2 (wit aucs'))) (∈ty aucs) (wit (∈tm ap)))
