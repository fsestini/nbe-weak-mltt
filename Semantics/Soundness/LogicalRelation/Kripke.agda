module Semantics.Soundness.LogicalRelation.Kripke where

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
open import Semantics.Soundness.LogicalRelation.Preservation
open import Semantics.Soundness.LogicalRelation.Irrelevance

open import Size
open import Syntax.Typed.Inversion

open _[_,_]
open _[_,_]∈_
open SemTy
open _●_∈ap_
open _∈_


kripke-𝒰 : ∀{w Θ Γ Δ A X} {ty : X ∈𝒰} → Θ ∷ Δ ⊢ᵣ w ∶ Γ
         → Θ ∷ Γ ⊢ A ®𝒰 ty → Θ ∷ Δ  ⊢ wk A w ®𝒰 wk𝒰 ty w
kripke-𝒰 {ty = uNe _} wp rel = ⊢wk-ty-∼ rel wp
kripke-𝒰 {w} {ty = uPi {A = A} _ Ah _} wp (®𝒰Π {S = S} {T} conv rel h) =
  ®𝒰Π (⊢wk-ty-∼ conv wp) (ty-irrel𝒰 refl (trans (wk-comp _) (sym (trans (wk-comp _)
      (≈ʷwk (≈ʷsym idw-L) _)))) (wk𝒰 (Ah Id) _) (wk𝒰 (Ah w) _) (kripke-𝒰 wp rel))
      λ {w'} wp' p ss →
        let p' = sameTerm≃ (wk-comp _) (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) _ p
        in ≡preserv𝒰 (sym (trans (subst-wk T) (≈ˢsub (≈ˢcons w-accum) T)))
                     (h (⊢·ʷ wp wp') p' (≡preserv𝒰-tm (wk-comp S) refl
                       (tm-irrel𝒰 refl refl (wk-comp A) (wk𝒰 (Ah w) w')
                         (Ah (w ·ʷ w')) p p' ss)))

kripke-𝒯 : ∀{w Θ Γ Δ A X} {ty : X ∈𝒯} → Θ ∷ Δ ⊢ᵣ w ∶ Γ
          → Θ ∷ Γ ⊢ A ® ty → Θ ∷ Δ  ⊢ wk A w ® wk𝒯 ty w
kripke-𝒯 {w} {ty = 𝒰⊆𝒯 x} wp rel = kripke-𝒰 wp rel
kripke-𝒯 {w} {ty = tU} wp rel = ⊢wk-ty-∼ rel wp
kripke-𝒯 {w} {Θ} {Γ} {Δ} {ty = tPi {A = A} nfB Ah Bh} wp (®𝒯Π {S = S} {T} conv rel h) =
  ®𝒯Π (⊢wk-ty-∼ conv wp)
       (ty-irrel𝒯 refl (trans (wk-comp A) (trans (≈ʷwk idw-L A)
         (sym (wk-comp A)))) (wk𝒯 (Ah Id) w) (wk𝒯 (Ah w) Id)
         (kripke-𝒯 {ty = Ah Id} wp rel)) λ {w'} {_} {s} wp' p ss →
         let p' = sameTerm𝒯≃ (wk-comp A) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) p
             aux = h (⊢·ʷ wp wp') p' (tm-irrel𝒯 refl refl (wk-comp S)
               (wk-comp A) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) p p' ss)
         in ≡preserv {ty = ∈t (Bh _)}
           (sym (trans (subst-wk T) (≈ˢsub (≈ˢcons w-accum) T))) aux

kripke-tm𝒰 : ∀{Θ Γ Δ A t a X w}
           → (ty : X ∈𝒰) {p : P (El𝒰 ty) a}
           → Θ ∷ Δ ⊢ᵣ w ∶ Γ
           → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ p
           → Θ ∷ Δ  ⊢ wk t w ∶ wk A w ®𝒰 wk𝒰 ty w ∋ wk-tm-𝒰 w ty p
kripke-tm𝒰 {Θ} {Γ} {Δ} {w = w} ty@(uPi {A = A} {B} nfB Ah Bh) wp
  (®𝒰λ {r = r} {t = t} {d} {R} {S} {T} qh ty pf tyconv relA tmconv h) =
  ®𝒰λ qh' (wk𝒰 ty w) (wk-tm-𝒰 w ty pf) (⊢wk-ty-∼ tyconv wp) relA' (⊢wk-tm-∼ tmconv wp) h'
  where
    relA' = ty-irrel𝒰 refl (trans (wk-comp _) (sym (trans (wk-comp _)
      (sym (≈ʷwk idw-L _))))) (wk𝒰 (Ah Id) w) (wk𝒰 (Ah w) Id) (kripke-𝒰 wp relA)
    Bh' : {a : Term} {w' : Wk} → P (El𝒰 (wk𝒰 (Ah w) w')) a → wk B (Skip w) [ w' , a ]∈𝒰
    Bh' {a} {w'} p with Bh {a} {w ·ʷ w'} (sameTerm≃ (wk-comp _) (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) _ p)
    Bh' {a} {w'} p | []ctor ss tm = []ctor (≡Eval (sym
      (trans (subst-wk B) (≈ˢsub (≈ˢcons w-accum) B))) refl ss) tm
    qh' : ∀{a w'} (pa : P (El𝒰 (wk𝒰 (Ah w) w')) a)
        → wk d (Skip w) [ w' , a ]∈ El𝒰 (∈t (Bh' pa))
    qh' {a} {w'} pa with qh {a} {w ·ʷ w'} (sameTerm≃ (wk-comp _) (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) _ pa)
    qh' {a} {w'} pa | record { ↘s = ↘s ; ∈tm = ∈tm } =
      record { ↘s = ≡Eval (sym (trans (subst-wk d) (≈ˢsub (≈ˢcons w-accum) d))) refl ↘s ; ∈tm = ∈tm }
    h' : ∀{w' Γ' s a} → Θ ∷ Γ' ⊢ᵣ w' ∶ Δ → (p : P (El𝒰 (wk𝒰 (Ah w) w')) a)
       → Θ ∷ Γ' ⊢ s ∶ wk (wk S w) w' ®𝒰 wk𝒰 (Ah w) w' ∋ p
       → Θ ∷ Γ' ⊢ wk t (Skip w) [ w' , s ]ₛ ∶ wk T (Skip w) [ w' , s ]ₛ
                ®𝒰 ∈t (Bh' p) ∋ wit (∈tm (qh' p))
    h' {w'} {Γ'} {s} {a} wp' p relsa =
      let aux = h {w ·ʷ w'} {Γ'} {s} {a} (⊢·ʷ wp wp')
                 (sameTerm≃ (wk-comp _) (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) _ p)
                 (tm-irrel𝒰 refl (wk-comp S) (wk-comp _)
                   (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) _ _ relsa)
      in tm-irrel𝒰 (sym (trans (subst-wk t) (≈ˢsub (≈ˢcons w-accum) t)))
        (sym (trans (subst-wk T) (≈ˢsub (≈ˢcons w-accum) T))) refl
        (∈t (Bh (sameTerm≃ (wk-comp A) (wk𝒰 (Ah w) w') (Ah (w ·ʷ w')) a p))) _ _ _ aux
kripke-tm𝒰 (uPi nfB Ah Bh) wp (®𝒰Ne x x₁ x₂) =
  ®𝒰Ne (neWkLemma x) (⊢wk-tm-∼ x₁ wp) (⊢wk-ty-∼ x₂ wp)
kripke-tm𝒰 (uNe x) wp (p ,, q) = ⊢wk-ty-∼ p wp ,, ⊢wk-tm-∼ q wp

kripke-tm : ∀{Θ Γ Δ A t a X w} {ty : X ∈𝒯} {p : P (El𝒯 ty) a}
          → Θ ∷ Δ ⊢ᵣ w ∶ Γ
          → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ p
          → Θ ∷ Δ  ⊢ wk t w ∶ wk A w ® wk𝒯 ty w ∋ wk-tm-𝒯 w ty p
kripke-tm {ty = 𝒰⊆𝒯 x} wp rel = kripke-tm𝒰 x wp rel
kripke-tm {ty = tU} wp (p ,, q ,, r) =
  ⊢wk-ty-∼ p wp ,, kripke-𝒰 wp q ,, ⊢wk-tm-∼ r wp
kripke-tm {Θ} {Γ} {Δ} {w = w} {ty = tPi {A = A} {B} nfB Ah Bh} wp
  (®𝒯λ {t = t} {d = d} {S = S} {T} qh ty pf conv relA convt h) =
  ®𝒯λ qh' (wk𝒯 ty w) (wk-tm-𝒯 w ty pf) (⊢wk-ty-∼ conv wp)
    (ty-irrel𝒯 refl (trans (wk-comp _) (sym (trans (wk-comp _) (sym
      (≈ʷwk idw-L _))))) (wk𝒯 (Ah Id) w) (wk𝒯 (Ah w) Id)
      (kripke-𝒯 {ty = Ah Id} wp relA))
    (⊢wk-tm-∼ convt wp) h'
  where
    qh' : ∀{a w'} (pa : P (El𝒯 (wk𝒯 (Ah w) w')) a)
        → wk d (Skip w) [ w' , a ]∈
            El𝒯 (∈t (Bh (sameTerm𝒯≃ (wk-comp A) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) pa)))
    qh' {a} {w'} pa with qh {a} {w ·ʷ w'} (sameTerm𝒯≃ (wk-comp _) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) pa)
    qh' {a} {w'} pa | record { ↘s = sb ; ∈tm = p } =
      record { ↘s = ≡Eval (sym (trans (subst-wk d) (≈ˢsub (≈ˢcons w-accum) d))) refl sb ; ∈tm = p }
    h' : ∀{w' Γ' s a} → Θ ∷ Γ' ⊢ᵣ w' ∶ Δ → (p : P (El𝒯 (wk𝒯 (Ah w) w')) a)
       → Θ ∷ Γ' ⊢ s ∶ wk (wk _ w) w' ® wk𝒯 (Ah w) w' ∋ p
       → Θ ∷ Γ' ⊢ wk t (Skip w) [ w' , s ]ₛ ∶ wk T (Skip w) [ w' , s ]ₛ
                ® ∈t (Bh (sameTerm𝒯≃ (wk-comp A) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) p))
                ∋ wit (∈tm (qh' p))
    h' {w'} wp' p relsa =
      tm-irrel𝒯 (sym (trans (subst-wk t) (≈ˢsub (≈ˢcons w-accum) t)))
        (Eval-fun (↘s (qh pp)) (≡Eval (trans (subst-wk d)
        (≈ˢsub (≈ˢcons w-accum) d)) refl (↘s (qh' p))))
        (sym (trans (subst-wk T) (≈ˢsub (≈ˢcons w-accum) T))) refl (∈t (Bh pp))
        (∈t (Bh pp)) (wit (∈tm (qh pp))) _ aux
      where
        pp = (sameTerm𝒯≃ (wk-comp _) (wk𝒯 (Ah w) w') (Ah (w ·ʷ w')) p)
        aux = h {w ·ʷ w'} (⊢·ʷ wp wp')
                pp (tm-irrel𝒯 refl refl (wk-comp _) (wk-comp _) (wk𝒯 (Ah w) w')
                  (Ah (w ·ʷ w')) _ _ relsa)
kripke-tm {ty = tPi nfB Ah Bh} wp (®𝒯Ne x x₁ x₂) =
  ®𝒯Ne (neWkLemma x) (⊢wk-tm-∼ x₁ wp) (⊢wk-ty-∼ x₂ wp)
