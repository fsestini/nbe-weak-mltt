module Semantics.Soundness.TermSoundness.Variable where

open import Semantics.Soundness.LogicalRelation
open import Semantics.Soundness.SubLogicalRelation.Definition
open import Syntax
open import Semantics.Completeness
open import Data.Product renaming (_,_ to _,,_)
open import Syntax.Typed.Inversion
open import Relation.Binary.PropositionalEquality
open import Syntax.Typed.MetaRenaming

open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open _∈_
open _∈⟦_⟧_

varFundamental : ∀{Θ Γ Δ A n σ ρ}
               → (c : ⊢ Θ ∷ Γ)
               → (x : Γ [ n ]↦ A)
               → (ρp : ρ ∈⟦ Γ ⟧)
               → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
               → let aux = proj₂ (models (bound c x)) ρp
                 in Θ ∷ Δ ⊢ sub-var n σ ∶ sub A σ ® ∈ty aux ∋ wit (∈tm aux)
varFundamental c () ρp (◇® _)
varFundamental c here _ (#® {A = A} {p = p} rel tmrel) =
   ≡preserv-tm {ty = inT p} (trans (subst-wk A) (≈ˢsub id-wk-sub-L A)) refl tmrel
varFundamental (⊢# c x₁) (there {A = A} x) _ (#® {ρp = ρp} rel tmrel) =
  ≡preserv-tm {ty = ∈ty k} {wit (∈tm k)} (trans (subst-wk A)
    (≈ˢsub id-wk-sub-L A)) refl aux
  where k = proj₂ (models (bound c x)) ρp ; aux = varFundamental c x _ rel
varFundamental {A = A} c x _ (·® {w = w} {ρp} rel wp) =
  ≡preserv-tm {ty = wk𝒯 (∈ty k) w} {wk-tm-𝒯 w (∈ty k) (wit (∈tm k))}
    (sym (wk-subst A)) refl aux'
  where k = proj₂ (models (bound c x)) ρp
        aux = varFundamental c x _ rel
        aux' = kripke-tm {ty = ∈ty k} {wit (∈tm k)} wp aux


kkuu : ∀{A B C D E} → Eval A ↘ C → Eval B ↘ C → Eval A ↘ D → Eval B ↘ E → D ≡ E
kkuu e1 e2 e3 e4 = trans (Eval-fun e3 e1) (Eval-fun e2 e4)

kkk : ∀{Θ A A' n} → ⊢ₘₛ Θ → Θ [ n ]ₗ↦ A → Eval A ↘ A' → Θ ∷ ◇ ⊢ A ∼ A'
kkk (m#® p h rel) (here x) e =
  ≡ty∼ refl (Eval-fun (≡Eval (id-sub _) refl (ev p)) e)
    (extend-ty∼ (convert-® {ty = inT p} rel) (der-tyₜ {ty = inT p} rel))
kkk (m#® p h rel) (there x) e = extend-ty∼ (kkk h x e) (der-tyₜ {ty = inT p} rel)

free-fund : ∀{Θ Γ Δ A n σ ρ i}
          → (ρp : ρ ∈⟦ Γ ⟧) → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
          → ⊢ₘₛ Θ → (c : ⊢⟨ i ⟩ Θ ∷ Γ) → (x : Θ [ n ]ₗ↦ A)
          → let aux = proj₂ (models (free c x)) ρp
            in Θ ∷ Δ ⊢ Free n ∶ sub A σ ® ∈ty aux ∋ wit (∈tm aux)
free-fund {A = A} ρp rels msc c x =
  allNe𝒯 (∈ty aux) neFree (≡ty∼ (trans (null-wk sz) (sym (null-sub sz)))
    (null-wk (tySameSzLemmaL h sz)) (⊢wk-ty-∼ h (⊢up c')))
      (∼refl (≡tm (sym (null-sub sz)) refl (free c' x)))
  where
    sz = ₗ↦Len (invert-ctx-ctx c) x ; aux = proj₂ (models (free c x)) ρp
    h = kkk msc x (≡Eval (null-sub sz) refl (↘ty aux))
    c' = ⊢sub-ctx c (derₛ rels)
