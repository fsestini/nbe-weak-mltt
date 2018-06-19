module Semantics.Completeness.Rule2Temp where

open import Function
open import Data.Nat
open import Data.Maybe
open import Syntax
open import Semantics.Domain.Domain
open import Semantics.Completeness.Type.Type
open import Semantics.Completeness.Type.UniverseProperties
open import Semantics.Completeness.Type.Lemmata
open import Semantics.Completeness.Type.BetaReductionLemma
open import Semantics.Completeness.Type.Properties.PiLemma
open import Semantics.Completeness.Type.Properties.LambdaLemma
open import Semantics.Completeness.Type.Properties.AppLemma
open import Data.Unit hiding (_≤_ ; _≟_)
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Data.Sum hiding ([_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Syntax.Typed.Inversion
open import Syntax.Typed.Model
open import Syntax.Typed.MetaSizeLemma
open import Size

open import Semantics.Completeness.Rule2

open SemTy
open ⟦_⟧≃⟦_⟧_,_∈𝒯
open ⟦_⟧≃⟦_⟧_,_∈tm⟦_⟧
open _∈⟦_⟧_,_
open _∈_

-- wkwk : ∀{A B C δ ρ} {tm : Tm 0 C}
--      → MTm (msLen (p1 (env-to-sub δ))) A
--      → MTm (msLen (p1 (env-to-sub δ))) B
--      → ⟦ A ⟧≃⟦ B ⟧ δ , ρ ∈𝒯 → ⟦ A ⟧≃⟦ B ⟧ ex δ tm , ρ ∈𝒯
-- wkwk mtA mtB record { ∈ty = ∈ty ; ↘t1 = ↘t1 ; ↘t2 = ↘t2 ; ↘s = ↘s } =
--   record { ∈ty = ∈ty ; ↘t1 = ≡Eval (mtm-ext _ mtA) refl ↘t1
--                      ; ↘t2 = ≡Eval (mtm-ext _ mtB) refl ↘t2 ; ↘s = ↘s }

-- env-len : ∀{δ Θ} → δ ∈⟦ Θ ⟧ₘ → msLen (p1 (env-to-sub δ)) ≡ clen Θ
-- env-len cEmpty = refl
-- env-len (cExt δ x tm) = cong suc (env-len δ)

-- models-free1 : ∀{Θ Γ A n} → ⊢ Θ → ⊧ Θ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ A
-- models-free1 _ _ () cEmpty _
-- models-free1 c (_ ,, a) xx@(here x) (cExt δ y tm) ρ =
--   wkwk aux'' aux'' (a δ (cEmpty δ))
--   where aux = mtm-var-lemma c xx ; aux' = env-len δ
--         aux'' = (subst (flip MTm _) (trans x (sym aux')) aux)
-- models-free1 (⊢# c x₁) (cc ,, _) (there x) (cExt δ y tm) ρ =
--   wkwk aux' aux' (models-free1 c cc x δ (cEmpty δ))
--   where aux = mtm-var-lemma c x
--         aux' = (liftMTm≤ (≤-≡L (uhm (↦ₗlemma x)) (env-len δ)) aux)

-- lemmino : ∀{n δ a} → n ≡ msLen δ → msub-var n (δ , a) ≡ a
-- lemmino {n} {δ} p with (n ≟ msLen δ)
-- lemmino p | yes p₁ = refl
-- lemmino p | no ¬p = ⊥-elim (¬p p)

-- models-free2 : ∀{Θ A n} → ⊢ Θ → ⊧ Θ → Θ [ n ]ₗ↦ A
--              → ∀{δ ρ} → δ ∈⟦ Θ ⟧ₘ
--              → ⟦ Free n ⟧≃⟦ Free n ⟧ δ , ρ ∈tm⟦ A ⟧
-- models-free2 (⊢# c Ad) (ch ,, _) (here {A = A} x) (cExt {δ = δ} {a = a} δp z tm) =
--   record
--     { ∈ty = inT z ; ↘ty = azd ; ∈tm = nn z
--     ; ↘s = ≡Eval (trans (id-sub _) (sym (null-sub (Eval-Tm qwe (ev z))))) refl (sb z)
--     ; ↘tm1 = lawl ; ↘tm2 = lawl ; ↘sb = ≡Eval (sym (null-sub tm)) refl e }
--   where e = (nfSelf (isNf (El𝒯 (inT z)) (wit (nn z))))
--         lawl = ≡Eval (sym (lemmino (trans x (sym (env-len δp))))) refl e
--         azd = ≡Eval (mtm-ext A (subst (flip MTm A) (sym (env-len δp))
--                     (tyMLen Ad))) refl (ev z)
--         qwe = tm-msub (p2 (env-to-sub δ)) (tyLen Ad)
-- models-free2 (⊢# cd Ad) (ch ,, a) (there {n = n} x) (cExt δp z tm) =
--   record
--     { ∈ty = ∈ty h ; ↘s = ↘s h ; ∈tm = ∈tm h ; ↘sb = ↘sb h
--     ; ↘ty = ≡Eval (mtm-ext _ (liftMTm≤ (≤-≡L (uhm (↦ₗlemma x))
--                   (env-len δp)) (mtm-var-lemma cd x))) refl (↘ty h)
--     ; ↘tm1 = ≡Eval eq refl (↘tm1 h) ; ↘tm2 = ≡Eval eq refl (↘tm2 h) }
--   where h = models-free2 cd ch x δp
--         eq = mtm-ext (Free n) (inj-mtmFree (≤-≡L (↦ₗlemma x) (env-len δp)))

-- models-free : ∀{Θ Γ A n} → ⊢ Θ → ⊧ Θ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ Free n ∶ A
-- models-free c ctx x = models-free1 c ctx x ,, λ d _ → models-free2 c ctx x d

-- -- (ctx ,, models-free2 ctx x) ,, models-free1 ctx x

-- ------------------------------------

-- -- mctx-map : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ A
-- -- mctx-map ch (here x) δ ρ = {!!}
-- -- mctx-map ch (there x) δ ρ = {!!}

-- -- mmm : ∀{Θ Γ A n δ ρ} → ⊧ Θ → Θ [ n ]ₗ↦ A
-- --     → δ ∈⟦ Θ ⟧ₘ → ρ ∈⟦ Θ ∷ Γ ⟧ δ → ⟦ Free n ⟧≃⟦ Free n ⟧ δ , ρ ∈tm⟦ A ⟧
-- -- mmm (p ,, q) (here x) (cExt δ x₁ tm) ρ = {!!}
-- -- mmm ch (there x) δ ρ = {!!}

-- -- M-free : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ Free n ∶ A
-- -- M-free ch x = {!!} ,, {!!}

-- --------------------------------------------------------------------------------
