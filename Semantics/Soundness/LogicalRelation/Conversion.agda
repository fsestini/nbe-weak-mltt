module Semantics.Soundness.LogicalRelation.Conversion where

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
open import Semantics.Soundness.LogicalRelation.Preservation

open import Size
open import Syntax.Typed.Inversion

open _[_,_]
open _[_,_]∈_
open SemTy
open _●_∈ap_
open _∈_

convert-®𝒰 : ∀{Θ Γ A X} {ty : X ∈𝒰} → Θ ∷ Γ ⊢ A ®𝒰 ty → Θ ∷ Γ ⊢ A ∼ X
convert-®𝒰 {ty = uNe x} rel = rel
convert-®𝒰 {Γ = Γ} {ty = uPi {_} {B} nfB Ah Bh} (®𝒰Π {S = S} {T} conv rel h) =
  ∼trans conv (∼Pi (≡ty∼ refl (id-wk 0 _) (convert-®𝒰 rel))
    (≡ty∼ (id-sub' T 1) aux (convert-®𝒰 (h {Up Id} {Γ # S} (⊢Up ⊢Id Sd)
      (hasNe (El𝒰 (Ah (Up Id))) (neBound {0})) (allNe𝒰 (Ah (Up Id))
        neBound eqq (∼refl (bound (⊢# (invert-ctx-ty∼ conv) Sd) here)))))))
  where
    Sd : _ ∷ Γ ⊢ S
    Sd = der-ty𝒰ₜ rel
    eqq : _ ∷ Γ # S ⊢ S ↑ ∼ wk _ (Up Id)
    eqq = ⊢wk-ty-∼ (≡ty∼ refl (id-wk 0 _) (convert-®𝒰 rel)) (⊢Up ⊢Id Sd)
    aux = Eval-fun
      (≡Eval (id-sub' B 1) refl (↘s $ Bh (hasNe (El𝒰 (Ah (Up Id))) neBound)))
      (nfSelf nfB)

convert-® : ∀{Θ Γ A X} {ty : X ∈𝒯} → Θ ∷ Γ ⊢ A ® ty → Θ ∷ Γ ⊢ A ∼ X
convert-® {ty = 𝒰⊆𝒯 _} = convert-®𝒰
convert-® {ty = tU} rel = rel
convert-® {Γ = Γ} {ty = tPi {B = B} nfB Ah Bh} (®𝒯Π {S = S} {T} conv rel h) =
  ∼trans conv (∼Pi (≡ty∼ refl (id-wk 0 _) (convert-® {ty = Ah Id} rel))
    (≡ty∼ (id-sub' T 1) aux (convert-®
      {ty = ∈t (Bh (hasNe (El𝒯 (Ah (Up Id))) neBound))} (h {Up Id} {Γ # S} (⊢Up ⊢Id Sd)
      (hasNe (El𝒯 (Ah (Up Id))) (neBound {0})) (allNe𝒯 (Ah (Up Id))
        neBound eqq (∼refl (bound (⊢# (invert-ctx-ty∼ conv) Sd) here)))))))
  where
    Sd : _ ∷ Γ ⊢ S
    Sd = der-tyₜ {ty = Ah Id} rel
    eqq : _ ∷ Γ # S ⊢ S ↑ ∼ wk _ (Up Id)
    eqq = ⊢wk-ty-∼ (≡ty∼ refl (id-wk 0 _) (convert-® {ty = Ah Id} rel)) (⊢Up ⊢Id Sd)
    aux = Eval-fun
      (≡Eval (id-sub' B 1) refl (↘s $ Bh (hasNe (El𝒯 (Ah (Up Id))) neBound)))
      (nfSelf nfB)

open import Syntax.Typed.EqLemma

convert-®𝒰-tm : ∀{Θ Γ A X t a} {ty : X ∈𝒰} {p : P (El𝒰 ty) a}
              → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ p
              → Θ ∷ Γ ⊢ t ∼ a ∶ A
convert-®𝒰-tm {Θ} {Γ} {ty = uPi _ Ah Bh} {p}
  (®𝒰λ {t = t} {d} {S = S} {T} qh ty pf x₂ relS lam-conv h) =
  ∼trans lam-conv (∼coe (∼ξ (≡ty∼ refl (id-wk 0 _) (convert-®𝒰 relS))
    (≡tm∼ (id-sub' t 1) deq (id-sub' T 1) aux')) (∼symm x₂))
  where
    Sd : _ ∷ Γ ⊢ S
    Sd = der-ty𝒰ₜ relS
    eqq : _ ∷ Γ # S ⊢ S ↑ ∼ wk _ (Up Id)
    eqq = ⊢wk-ty-∼ (≡ty∼ refl (id-wk 0 _) (convert-®𝒰 relS)) (⊢Up ⊢Id Sd)
    ctx = ⊢# (invert-ctx-ty∼ x₂) Sd
    deq : da (qh (hasNe (El𝒰 (Ah (Up Id))) (neBound {0}))) ≡ d
    deq = Eval-fun
      (≡Eval (id-sub' d 1) refl (↘s (qh (hasNe (El𝒰 (Ah (Up Id))) (neBound {0})))))
      (nfSelf (proj-lam (proj₁ pf)))
    aux = h (⊢Up ⊢Id Sd) (hasNe (El𝒰 (Ah (Up Id))) (neBound {0}))
      (allNe𝒰 (Ah (Up Id)) neBound eqq (∼refl (bound ctx here)))
    aux' = convert-®𝒰-tm aux
convert-®𝒰-tm {ty = uPi _ _ _} (®𝒰Ne x₂ x₃ _) = x₃
convert-®𝒰-tm {ty = uNe x} (_ ,, y) = y


convert-®𝒰-tm-ty : ∀{Θ Γ A X t a} (ty : X ∈𝒰) {p : P (El𝒰 ty) a}
                 → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ p
                 → Θ ∷ Γ ⊢ A ∼ X
convert-®𝒰-tm-ty (uPi {A} {B} nf Ah Bh) (®𝒰λ {T = T} qh _ _ convT relS conv h) =
  ∼trans convT
  (∼Pi (≡ty∼ refl (id-wk 0 _) (convert-®𝒰 {ty = Ah Id} relS))
    (≡ty∼ (id-sub' T 1) (Eval-fun (≡Eval (id-sub' B 1) refl (↘s (Bh b0)))
      (nfSelf nf)) (convert-®𝒰-tm-ty (∈t (Bh b0)) aux)))
  where
    SS = der-ty𝒰ₜ {ty = Ah Id} relS
    b0 = hasNe (El𝒰 (Ah (Up Id))) neBound
    aux = h (⊢Up ⊢Id SS) b0 (allNe𝒰 (Ah (Up Id)) neBound (⊢wk-ty-∼ (≡ty∼ refl
      (id-wk 0 _) (convert-®𝒰 relS)) (⊢Up ⊢Id SS))
        (∼refl (bound (⊢# (invert-ctx-ty SS) SS) here)))
convert-®𝒰-tm-ty (uPi _ Ah Bh) (®𝒰Ne x₁ x₂ x₃) = x₃
convert-®𝒰-tm-ty (uNe x) rel = proj₁ rel

convert-®𝒯-tm : ∀{Θ Γ A X t a} {ty : X ∈𝒯} {p : P (El𝒯 ty) a}
              → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ p
              → Θ ∷ Γ ⊢ t ∼ a ∶ A
convert-®𝒯-tm {ty = 𝒰⊆𝒯 x} = convert-®𝒰-tm
convert-®𝒯-tm {ty = tU} (p ,, _ ,, q) = ∼coe q (∼symm p)
convert-®𝒯-tm {Γ = Γ} {ty = tPi _ Ah Bh}
  (®𝒯λ {t = t} {d} {S = S} {T} qh ty pf x₂ relS lamconv h) =
  ∼trans lamconv (∼coe (∼ξ (≡ty∼ refl (id-wk 0 _) (convert-® {ty = Ah Id} relS))
    (≡tm∼ (id-sub' t 1) deq (id-sub' T 1) aux')) (∼symm x₂))
  where
    Sd : _ ∷ Γ ⊢ S
    Sd = der-tyₜ {ty = Ah Id} relS
    eqq : _ ∷ Γ # S ⊢ S ↑ ∼ wk _ (Up Id)
    eqq = ⊢wk-ty-∼ (≡ty∼ refl (id-wk 0 _) (convert-® {ty = Ah Id} relS)) (⊢Up ⊢Id Sd)
    ctx = ⊢# (invert-ctx-ty∼ x₂) Sd
    deq : da (qh (hasNe (El𝒯 (Ah (Up Id))) (neBound {0}))) ≡ d
    deq = Eval-fun
      (≡Eval (id-sub' d 1) refl (↘s (qh (hasNe (El𝒯 (Ah (Up Id))) (neBound {0})))))
      (nfSelf (proj-lam (proj₁ pf)))
    aux = h (⊢Up ⊢Id Sd) (hasNe (El𝒯 (Ah (Up Id))) (neBound {0}))
      (allNe𝒯 (Ah (Up Id)) neBound eqq (∼refl (bound ctx here)))
    aux' = convert-®𝒯-tm {ty = ∈t (Bh (hasNe (El𝒯 (Ah (Up Id))) neBound))} aux
convert-®𝒯-tm {ty = tPi _ _ _} (®𝒯Ne _ x _) = x

convert-®𝒯-tm-ty : ∀{Θ Γ A X t a} (ty : X ∈𝒯) {p : P (El𝒯 ty) a}
                 → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ p
                 → Θ ∷ Γ ⊢ A ∼ X
convert-®𝒯-tm-ty (𝒰⊆𝒯 x) rel = convert-®𝒰-tm-ty x rel
convert-®𝒯-tm-ty tU rel = proj₁ rel
convert-®𝒯-tm-ty (tPi {A} {B} nf Ah Bh) (®𝒯λ {T = T} qh _ _ convT relS conv h) =
  ∼trans convT
  (∼Pi (≡ty∼ refl (id-wk 0 _) (convert-® {ty = Ah Id} relS))
    (≡ty∼ (id-sub' T 1) (Eval-fun (≡Eval (id-sub' B 1) refl (↘s (Bh b0)))
      (nfSelf nf)) (convert-®𝒯-tm-ty (∈t (Bh b0)) aux)))
  where
    SS = der-tyₜ {ty = Ah Id} relS
    b0 = hasNe (El𝒯 (Ah (Up Id))) neBound
    aux = h (⊢Up ⊢Id SS) b0 (allNe𝒯 (Ah (Up Id)) neBound (⊢wk-ty-∼ (≡ty∼ refl
      (id-wk 0 _) (convert-® {ty = Ah Id} relS)) (⊢Up ⊢Id SS))
        (∼refl (bound (⊢# (invert-ctx-ty SS) SS) here)))
convert-®𝒯-tm-ty (tPi nf Ah Bh) (®𝒯Ne x x₁ x₂) = x₂
