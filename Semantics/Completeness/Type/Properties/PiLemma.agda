module Semantics.Completeness.Type.Properties.PiLemma where

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

open SemTy
open _∈_
open _[_,_]
open _●_∈ap_
open _∈⟦_⟧_
open ⟦_⟧≃⟦_⟧_∈tm_
open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒰
open ⟦_⟧≃⟦_⟧_∈𝒯

open import Data.Sum
open import Function

invert-Π-1 : ∀{A B A' B' ρ} → ⟦ Π A B ⟧≃⟦ Π A' B' ⟧ ρ ∈𝒯 → ⟦ A ⟧≃⟦ A' ⟧ ρ ∈𝒯
invert-Π-1 ⟨ ty ∣ ePi e1 _ ∣ ePi e3 _ ⟩ =
  ⟨ ≡∈𝒯 (id-wk 0 _) (proj₁ (asder2 ty) Id) ∣ e1 ∣ e3 ⟩

invert-Π-2 : ∀{A B A' B' ρ}
     → ⟦ Π A B ⟧≃⟦ Π A' B' ⟧ ρ ∈𝒯
     → ∀{a w} → a ∈⟦ A ⟧ (ρ · w) → ⟦ B ⟧≃⟦ B' ⟧ (ρ · w , a) ∈𝒯
invert-Π-2 {A} {B} {_} {B'} ⟨ ty ∣ ePi e1 e3 ∣ ePi e2 e4 ⟩ {a} {w} pa =
  ⟨ ∈t aux ∣ ≡Eval (sss B) refl azd ∣ ≡Eval (sss B') refl azd' ⟩
  where
    sss : ∀ B → sub B (((_ · Id) · w) , a) ≡ sub B ((_ · w) , a)
    sss B = ≈ˢsub (≈ˢcons (eq-dot sub-id-R)) B
    pi = asder2 ty
    aux = proj₂ pi (sameT (Eval-fun (ev pa) (≡Eval (wk-subst A)
      refl (wkEval e1))) (inT pa) (proj₁ pi w) (wit (nn pa)))
    azd = sub-uncomm {B} e3 (↘s aux) ; azd' = sub-uncomm {B'} e4 (↘s aux)

piLemma : ∀{A A' B B' ρ}
        → ⟦ A ⟧≃⟦ A' ⟧ ρ ∈𝒯
        → (∀{a w} → a ∈⟦ A ⟧ (ρ · w) → ⟦ B ⟧≃⟦ B' ⟧ (ρ · w , a) ∈𝒯)
        → ⟦ Π A B ⟧≃⟦ Π A' B' ⟧ ρ ∈𝒯
piLemma {A} {A'} {B} {B'} {ρ} h1 h3 =
  ⟨ tPi (nfEval (↘t1 h2)) (wk𝒯 (∈ty h1)) aux
  ∣ ePi (↘t1 h1) (↘t1 h2) ∣ ePi (↘t2 h1) (↘t2 h2) ⟩

  where
    h2 : ⟦ B ⟧≃⟦ B' ⟧ sh ρ ∈𝒯
    h2 = h3 (beeh (↘t1 h1) (∈ty h1) (hasNe (El𝒯 (wk𝒯 (∈ty h1) _)) neBound))

    aux : ∀{a w} → P (El𝒯 (wk𝒯 (∈ty h1) w)) a → resT h2 [ w , a ]∈𝒯
    aux {a} {w} p = record { ↘s = eqq ; ∈t = ∈ty aucs }
      where
        aucs = h3 {a} {w} (beeh (↘t1 h1) (∈ty h1) p)
        eqq = sub-comm {B} {resT aucs} {_} {sh ρ} (↘t1 h2)
          (≡Eval (≈ˢsub (≈ˢcons (eq-dot (≈ˢsym sub-id-R))) B) refl (↘t1 aucs))

-- boooring
postulate
  piLemmaU : ∀{A A' B B' ρ}
           → ⟦ A ⟧≃⟦ A' ⟧ ρ ∈tm⟦ U ⟧ → ⟦ B ⟧≃⟦ B' ⟧ sh ρ ∈tm⟦ U ⟧
           → (∀{a w} → a ∈⟦ A ⟧ (ρ · w) → ⟦ B ⟧≃⟦ B' ⟧ (ρ · w , a) ∈tm⟦ U ⟧)
           → ⟦ Π A B ⟧≃⟦ Π A' B' ⟧ ρ ∈tm⟦ U ⟧
