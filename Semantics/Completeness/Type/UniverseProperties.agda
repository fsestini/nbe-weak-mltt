module Semantics.Completeness.Type.UniverseProperties where

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
open import Semantics.Completeness.Type.Extensional

open SemTy
open _[_,_]
open ⟦_⟧≃⟦_⟧_∈tm_
open _●_∈ap_
open _∈_

≡𝒰' : ∀{A B a} → (p : A ∈𝒰) → (eq : A ≡ B)
    → P (El𝒰 (≡𝒰 p eq)) a → P (El𝒰 p) a
≡𝒰' p refl q = q

≡𝒯' : ∀{A B a} → (p : A ∈𝒯) → (eq : A ≡ B)
    → P (El𝒯 (≡𝒯 p eq)) a → P (El𝒯 p) a
≡𝒯' p refl q = q

∈𝒰Id : ∀{A} → ((w : Wk) → wk A w ∈𝒰) → A ∈𝒰
∈𝒰Id {A} h = subst _∈𝒰 (id-wk 0 A) (h Id)

∈𝒯Id : ∀{A} → ((w : Wk) → wk A w ∈𝒯) → A ∈𝒯
∈𝒯Id {A} h = subst _∈𝒯 (id-wk 0 A) (h Id)

wk𝒰 : ∀{A} → A ∈𝒰 → (w : Wk) → wk A w ∈𝒰
wk𝒰 (uNe x) _ = uNe (neWkLemma x)
wk𝒰 (uPi {A} {B} nfB Ah Bh) w =

  uPi (nfWkLemma nfB) (λ w' → wk𝒰 (Ah w) w')
    λ {a} {w'} p →
      let azd = sameTerm≃ (wk-comp A) (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) _ p
          aux = Bh azd
      in record { ↘s = ≡Eval (sym (trans (subst-wk B)
                         (≈ˢsub (≈ˢcons w-accum) B))) refl (↘s aux)
                ; ∈t = ∈t aux }

wk𝒯 : ∀{A} → A ∈𝒯 → (w : Wk) → wk A w ∈𝒯
wk𝒯 (𝒰⊆𝒯 x) w = 𝒰⊆𝒯 (wk𝒰 x w)
wk𝒯 tU _ = tU
wk𝒯 {_} (tPi {A} {B} nfB Ah Bh) w =
  tPi (nfWkLemma nfB) (λ w' → wk𝒯 (Ah w) w')
  λ {a} {w'} p →
    let azd = sameTerm𝒯≃ (wk-comp _) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) p
        aux = Bh azd
    in record { ↘s = ≡Eval (sym (trans (subst-wk B)
      (≈ˢsub (≈ˢcons w-accum) B))) refl (↘s aux) ; ∈t = ∈t aux }

wk-tm-𝒰 : ∀{A t} w → (p : A ∈𝒰) → P (El𝒰 p) t → P (El𝒰 (wk𝒰 p w)) (wk t w)
wk-tm-𝒰 w (uNe x₁) x = neWkLemma x
wk-tm-𝒰 {_} {f} w (uPi {A} {B} nfB h1 h2) (nf ,, h) = (nfWkLemma nf) ,, goal
  where
    goal : ∀{a w'} (p : P (El𝒰 (wk𝒰 (h1 w) w')) a) → wk (wk f w) w' ● a ∈ap _
    goal {a} {w'} p =
      record { ∈tm = ∈tm aucs ; ↘ap = ≡App (sym (wk-comp f)) refl (↘ap aucs) }
      where
        p' = sameTerm≃ (wk-comp A) (wk𝒰 (h1 w) w') (h1 (w ·ʷ w')) _ p
        aucs = h p'

transport-𝒰-𝒯 : ∀{A B a} → A ≡ B → (p : A ∈𝒰) → (q : B ∈𝒯) → P (El𝒰 p) a → P (El𝒯 q) a
transport-𝒰-𝒯 refl p q x = sameTerm𝒯≃ refl (𝒰⊆𝒯 p) q x

transport-𝒯-𝒰 : ∀{a A B} → A ≡ B → (p : A ∈𝒰) → (q : B ∈𝒯) → P (El𝒯 q) a → P (El𝒰 p) a
transport-𝒯-𝒰 refl p q x = sameTerm𝒯≃ refl q (𝒰⊆𝒯 p) x

wk-tm-𝒯 : ∀{t A} w → (p : A ∈𝒯) → P (El𝒯 p) t → P (El𝒯 (wk𝒯 p w)) (wk t w)
wk-tm-𝒯 w (𝒰⊆𝒯 x₁) x = wk-tm-𝒰 w x₁ x
wk-tm-𝒯 w tU x = wk𝒰 x w
wk-tm-𝒯 {t} w (tPi {_} {B} _ h1 h2) (nf ,, h) = nfWkLemma nf ,, λ {a} {w'} p →
  let p' = sameTerm𝒯≃ (wk-comp _) (wk𝒯 (h1 w) w') (h1 (w ·ʷ w')) p ; aucs = h p'
  in record { ∈tm = ∈tm aucs ; ↘ap = ≡App (sym (wk-comp t)) refl (↘ap aucs) }


-- sameTerm𝒯≃ : ∀{A B a} → A ≡ B → (p : A ∈𝒯) (q : B ∈𝒯) → P (El𝒯 p) a → P (El𝒯 q) a
-- sameTerm𝒯≃ refl (𝒰⊆𝒯 p) (𝒰⊆𝒯 q) x = sameTerm≃ refl p q _ x
-- sameTerm𝒯≃ refl (𝒰⊆𝒯 (uNe ())) tU x
-- sameTerm𝒯≃ refl (𝒰⊆𝒯 u@(uPi _ _ _)) t@(tPi _ _ _) pf = transport-𝒰-𝒯 refl u t pf
-- sameTerm𝒯≃ refl (𝒰⊆𝒯 (uNe ())) (tPi x₂ pA x₃) x
-- sameTerm𝒯≃ refl tU (𝒰⊆𝒯 (uNe ())) x
-- sameTerm𝒯≃ refl tU tU x = x
-- sameTerm𝒯≃ refl t@(tPi _ _ _) (𝒰⊆𝒯 u@(uPi _ _ _)) pf = transport-𝒯-𝒰 refl u t pf
-- sameTerm𝒯≃ refl (tPi x₁ pA x₂) (𝒰⊆𝒯 (uNe ())) x
-- sameTerm𝒯≃ refl (tPi _ h1 h2) (tPi _ h1' h2') (nf ,, h) = nf ,, λ {a} {w} p →
--   let p' = sameTerm𝒯≃ refl (h1' w) (h1 w) p in
--   record { ∈tm = ∈in (sameTerm𝒯≃ (Eval-fun (↘s (h2 p')) (↘s (h2' p)))
--     (∈t (h2 p')) (∈t (h2' p)) (wit (∈tm (h p')))) ; ↘ap = ↘ap (h p') }
