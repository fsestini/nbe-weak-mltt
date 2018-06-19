module Semantics.Completeness.Type.Properties.LambdaLemma where

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
open import Semantics.Completeness.Type.UniverseProperties
open import Semantics.Completeness.Type.Properties.PiLemma
open import Data.Sum
open import Function

open SemTy
open _∈_
open _[_,_]
open _[_,_]∈_
open _●_∈ap_
open ⟦_⟧≃⟦_⟧_∈tm_
open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒰
open ⟦_⟧≃⟦_⟧_∈𝒯

open import Semantics.Completeness.Type.Lemmata

uhm' : ∀{A B d A'}
     → Nf A → (nfB : Nf B) → Nf d
     → (Ah : (w : Wk) → wk A w ∈𝒰)
     → (Bh : ∀{a w} → P (El𝒰 (Ah w)) a → B [ w , a ]∈𝒰)
     → (th : ∀{a w} → (pa : P (El𝒰 (Ah w)) a) → d [ w , a ]∈ El𝒰 (∈t (Bh pa)))
     → A ≡ A'
     → P (El𝒰 (uPi nfB Ah Bh)) (Lam A' d)
uhm' {A} {B} {d} nfA nfB nfd Ah Bh th refl = nfLam nfA nfd ,, aux
  where
    aux : ∀{a w} (p : P (El𝒰 (Ah w)) a)
        → Lam (wk A w) (wk d (Skip w)) ● a ∈ap El𝒰 (∈t (Bh p))
    aux {a} {w} pa = ppp
      where
        sbj : β-Redex-Subj (Lam (wk A w) (wk d (Skip w)))
        sbj = brsLam (nfWkLemma nfA) (nfWkLemma nfd)
        ppp : _
        ppp with decβ-Redex sbj (isNf (El𝒰 (Ah w)) pa)
        ppp | inj₁ x =
          record { ∈tm = ∈tm (th pa)
                 ; ↘ap = ●β x (≡Eval (sym (subst-wk d)) refl (↘s (th pa))) }
        ppp | inj₂ y =
          record { ∈tm = ∈in (hasNe (El𝒰 (∈t (Bh pa))) y) ; ↘ap = ●Ne y }

uhm'' : ∀{A B d A'}
      → Nf A → (nfB : Nf B) → Nf d
      → (Ah : (w : Wk) → wk A w ∈𝒯)
      → (Bh : ∀{a w} → P (El𝒯 (Ah w)) a → B [ w , a ]∈𝒯)
      → (th : ∀{a w} → (pa : P (El𝒯 (Ah w)) a) → d [ w , a ]∈ El𝒯 (∈t (Bh pa)))
      → A ≡ A'
      → P (El𝒯 (tPi nfB Ah Bh)) (Lam A' d)
uhm'' {A} {B} {d} nfA nfB nfd Ah Bh th refl = nfLam nfA nfd ,, aux
  where
    aux : ∀{a w} (p : P (El𝒯 (Ah w)) a)
        → Lam (wk A w) (wk d (Skip w)) ● a ∈ap El𝒯 (∈t (Bh p))
    aux {a} {w} pa = ppp
      where
        sbj : β-Redex-Subj (Lam (wk A w) (wk d (Skip w)))
        sbj = brsLam (nfWkLemma nfA) (nfWkLemma nfd)
        ppp : _
        ppp with decβ-Redex sbj (isNf (El𝒯 (Ah w)) pa)
        ppp | inj₁ x =
          record { ∈tm = ∈tm (th pa)
                 ; ↘ap = ●β x (≡Eval (sym (subst-wk d)) refl (↘s (th pa))) }
        ppp | inj₂ y =
          record { ∈tm = ∈in (hasNe (El𝒯 (∈t (Bh pa))) y) ; ↘ap = ●Ne y }


lamLemma : ∀{A A' B ρ t t'}
         → ⟦ A ⟧≃⟦ A' ⟧ ρ ∈𝒯
         → (∀{a w} → a ∈⟦ A ⟧ (ρ · w) → ⟦ t ⟧≃⟦ t' ⟧ (ρ · w , a) ∈tm⟦ B ⟧)
         → ⟦ Lam A t ⟧≃⟦ Lam A' t' ⟧ ρ ∈tm⟦ Π A B ⟧
lamLemma {A} {A'} {B} {ρ} {t} {t'} Ah th' = goal
  where
    bee = (beeh (↘t1 Ah) (∈ty Ah) (hasNe (El𝒯 (wk𝒯 (∈ty Ah) (Up Id))) neBound))
    th = th' bee ; ih = invert-ty th ; ih' = argty th' ; pi = piLemma Ah ih'
    goal : _
    goal with pi
    goal | ⟨ ty ∣ ePi e1 e2 ∣ ePi e1' _ ⟩ =
      record
        { ∈ty = ty ; ↘ty = ePi e1 e2
        ; ∈tm = ∈in (sameT (Eval-fun (↘t1 pi) (ePi e1 e2)) (∈ty pi) ty
            (nfLam (nfEval e1) (nfEval (↘tm1 th)) ,, goul))
        ; ↘tm1 = eLam e1 (↘tm1 th) ; ↘tm2 = eLam e1' (↘tm2 th) }
      where
        goul : ∀{a w} (p : P (El𝒯 (wk𝒯 (∈ty Ah) w)) a) → _ ● a ∈ap _
        goul {a} {w'} pa = ppp
          where
            nfB = nfWkLemma {_} {Skip w'} (nfEval (↘tm1 th))
            sbj : β-Redex-Subj (wk (Lam _ (res th)) w')
            sbj = brsLam (nfWkLemma (nfEval e1)) (nfWkLemma (nfEval (↘tm1 th)))
            nfa = isNf (El𝒯 (wk𝒯 (∈ty Ah) w')) pa
            tmtm = (th' (beeh (↘t1 Ah) (∈ty Ah) pa))
            ppp : _
            ppp with decβ-Redex sbj nfa
            ppp | inj₁ x =
              ⟨ ∈in (wit (∈tm tmtm))
              ∣ ●β x (≡Eval (sym (subst-wk (res th))) refl
                (sub-comm {t} (↘tm1 th) (≡Eval (≈ˢsub (≈ˢcons (eq-dot
                  (≈ˢsym sub-id-R))) t) refl (↘tm1 tmtm)))) ⟩
            ppp | inj₂ y = ⟨ ∈in (hasNe (El𝒯 (∈ty tmtm)) y) ∣ ●Ne y ⟩
