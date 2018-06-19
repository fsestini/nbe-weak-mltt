module Semantics.Soundness.Soundness where

open import Semantics.Soundness.LogicalRelation
open import Semantics.Soundness.TypeSoundness
open import Semantics.Soundness.TermSoundness
open import Semantics.Soundness.SubLogicalRelation.Definition
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness hiding (lamLemma)
open import Data.Product renaming (_,_ to _,,_)
open import Syntax.Typed.Inversion
open import Size
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Typed.Model
open import Data.Nat
open import Syntax.Typed.MetaRenaming

open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒯
open _∈_
open _∈⟦_⟧_
open SemTy

guuu : ∀{Θ Δ Γ A σ ρ i} → (x : ⟨ i ⟩ Θ ∷ Γ ⊢ A ∶ U) → (ρp : ρ ∈⟦ Γ ⟧)
     → Θ ∷ Δ ⊢ sub A σ ∶ U ® ∈ty (proj₂ (models x) ρp) ∋
         wit (∈tm (proj₂ (models x) ρp))
     → Θ ∷ Δ ⊢ sub A σ ® ∈ty (models-ty (El x) ρp)
guuu x ρp rel = h''
  where
    aux = (proj₂ (models x) ρp)
    pa = sameT (Eval-fun (↘ty aux) eU) (∈ty aux) tU (wit (∈tm aux))
    h = tm-irrel𝒯 refl refl refl (Eval-fun (↘ty aux) eU) (∈ty aux) tU (wit (∈tm aux)) pa rel
    h' = proj₁ (proj₂ h)
    h'' = ty-irrel𝒯 refl (Eval-fun (↘tm1 aux) (↘t1 (models-ty (El x) ρp)))
            (𝒰⊆𝒯 pa) (∈ty (models-ty (El x) ρp)) h'

open _[_,_]

mutual

  fundamental-ty : ∀{Θ Γ A i} → (ty : ⟨ i ⟩ Θ ∷ Γ ⊢ A) → ⊧Ty ty
  fundamental-ty (U x) ρp _ rels = ∼refl (U (⊢sub-ctx x (derₛ rels)))
  fundamental-ty (El x) ρp mc rels = guuu x ρp (fundamental x ρp mc rels)
  fundamental-ty ty@(Π tyA tyB) ρp mc rels =
    fundPi tyA tyB ρp mc rels (fundamental-ty tyA ρp mc rels) (fundamental-ty tyB)

  fundamental : ∀{Θ Γ A t i} → (td : ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A) → ⊧Tm td
  fundamental (free c x) ρp mc rels = free-fund ρp rels mc c x
  fundamental (bound c x) ρp mc rels = varFundamental c x ρp rels
  fundamental (lam td) = lamLemma td (fundamental td)
      (fundamental-ty (proj₂ (invert-ctx-aux (invert-ctx-tm td))))
  fundamental (app td sd x) ρp mc rels =
    appLemmy' td ht sd hs x (fundamental-ty Ad) (fundamental-ty x) ρp mc rels
    where
      Ad = (proj₂ (invert-ctx-aux (invert-ctx-ty x)))
      ht = fundamental td ; hs = fundamental sd
  fundamental (U-Π Ad Bd) ρp mc rels =
    upi Ad Bd (fundamental Ad) (fundamental Bd) ρp mc rels
  fundamental (coe td eq) ρp mc rels =
    ∼preservation-tm {ty = ∈ty aux'} (⊢sub-ty∼ eq ss) (∼refl (⊢sub-tm td ss)) h'
    where h = fundamental td ρp mc rels
          ss = derₛ rels
          aux = proj₂ (models td) ρp ; aux' = proj₂ (models (coe td eq)) ρp
          eqq = kkuu (↘t1 axx) (↘t2 axx) (↘ty aux) (↘ty aux')
            where axx = models-ty-eq eq ρp
          h' = tm-irrel𝒯 refl refl refl eqq (∈ty aux) (∈ty aux')
                 (wit (∈tm aux)) (wit (∈tm aux')) h

idmrel : ∀{Θ} → ⊢ Θ → ⊢ₘₛ Θ
idmrel ⊢◇ = m◇®
idmrel {Θ # A} (⊢# {A = A} c x) =
  m#® ⟨ ↘t1 aux ∣ ∈ty aux ∣ ∈in (hasNe (El𝒯 (∈ty aux)) neFree) ⟩ (idmrel c) h'
  where
    aux = models-ty x cEmpty
    h = fundamental-ty x cEmpty (idmrel c) (◇® ⊢Id)
    h' = ≡preserv {ty = ∈ty aux} (id-sub A) h

idrel : ∀{Θ Γ} (c : ⊢ Θ ∷ Γ) → Θ ∷ Γ ⊢ₛ Γ ∶ idsub Γ ® idid c
idrel (⊢◇ x) = ◇® ⊢Id
idrel {Θ} {Γ # A} cc@(⊢# c x) = #® (·® (idrel c) (⊢Up ⊢Id x))
  (allNe𝒯 {Θ} {Γ # A} {sub A (idsub Γ · Up Id)} (wk𝒯 (∈ty aux) (Up Id))
    (neBound {0}) eq (∼refl (bound cc (≡↦ (sym (trans (sym (wk-subst A))
      (cong (λ x₁ → wk x₁ (Up Id)) (id-sub' A (clen Γ))))) here))))
  where
    h = idid c ; aux = models-ty x h
    h' = fundamental-ty x h (idmrel (invert-ctx-ctx c)) (idrel c)
    eq'' : Θ ∷ Γ ⊢ sub A (idsub Γ) ∼ resT aux
    eq'' = ≡ty∼ refl (Eval-fun (↘t1 (models-ty x h)) (↘t1 aux))
      (convert-® {ty = ∈ty (models-ty x h)} h')
    eq : Θ ∷ Γ # A ⊢ sub A (idsub Γ · Up Id) ∼ wk (resT aux) (Up Id)
    eq = ≡ty∼ (wk-subst A) refl (⊢wk-ty-∼ eq'' (⊢Up ⊢Id x))

soundness-ty : ∀{Θ Γ A} → (Ad : Θ ∷ Γ ⊢ A) → Θ ∷ Γ ⊢ A ∼ nf-ty Ad
soundness-ty {Γ = Γ} Ad = ≡ty∼ (id-sub' _ (clen Γ)) refl conv
  where
    ctx = invert-ctx-ty Ad
    aux = fundamental-ty Ad (idid ctx) (idmrel (invert-ctx-ctx ctx)) (idrel ctx)
    conv = convert-® {ty = ∈ty (models-ty Ad (idid ctx))} aux

soundness-tm : ∀{Θ Γ A t} → (td : Θ ∷ Γ ⊢ t ∶ A) → Θ ∷ Γ ⊢ t ∼ nf td ∶ A
soundness-tm {Γ = Γ} td = ≡tm∼ (id-sub' _ (clen Γ)) refl (id-sub' _ (clen Γ)) conv
  where
    ctx = invert-ctx-tm td
    aux = fundamental td (idid ctx) (idmrel (invert-ctx-ctx ctx)) (idrel ctx)
    conv = convert-®𝒯-tm {ty = ∈ty (proj₂ (models td) (idid ctx))} aux
