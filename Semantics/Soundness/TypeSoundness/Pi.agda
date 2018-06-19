module Semantics.Soundness.TypeSoundness.Pi where

open import Semantics.Soundness.TypeSoundness.Definition

open import Semantics.Soundness.LogicalRelation
open import Syntax
open import Semantics.Completeness
open import Semantics.Soundness.SubLogicalRelation.Definition
open import Size
open import Relation.Binary.PropositionalEquality
open import Data.Product

open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒯
open _[_,_]
open _∈_
open _∈⟦_⟧_
open SemTy

fundPi : ∀{Θ Δ Γ A B σ ρ i} {j k : Size< i}
       → (Ad : ⟨ j ⟩ Θ ∷ Γ ⊢ A) → (Bd : ⟨ k ⟩ Θ ∷ Γ # A ⊢ B)
       → (ρp : ρ ∈⟦ Γ ⟧) → ⊢ₘₛ Θ → Θ ∷ Δ ⊢ₛ Γ ∶ σ ® ρp
       → Θ ∷ Δ ⊢ sub A σ ® ∈ty (models-ty Ad ρp) → ⊧Ty Bd
       → let aux = models-ty (Π Ad Bd) ρp
         in Θ ∷ Δ ⊢ sub (Π A B) σ ® ∈ty aux
fundPi {Θ} {Δ} {Γ} {A} {B} {σ} {ρ} Ad Bd ρp mc rels Ah Bh =
  ®𝒯Π (∼refl (⊢sub-ty (Π Ad Bd) (derₛ rels))) h1 goal
  where
    auxA = models-ty Ad ρp ; auxB = models-ty Bd
    h1 : Θ ∷ Δ ⊢ sub A σ ® wk𝒯 (∈ty auxA) Id
    h1 = ty-irrel𝒯 refl (sym (id-wk 0 _)) (∈ty auxA) (wk𝒯 (∈ty auxA) Id) Ah
    aucs = piLemma auxA (⊧sub Θ auxB ρp)
    goal : ∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Δ
         → (p : P (El𝒯 (wk𝒯 (∈ty auxA) w)) a)
         → Θ ∷ Γ' ⊢ s ∶ wk (sub A σ) w ® wk𝒯 (∈ty auxA) w ∋ p
         → Θ ∷ Γ' ⊢ sub B (sh σ) [ w , s ]ₛ ® ∈t (proj₂ (asder2 (∈ty aucs)) p)
    goal {w} {Γ'} {s} {a} wp p relsa =
      ty-irrel𝒯 refl (Eval-fun (↘t1 (models-ty Bd (cExt (cWk ρp) bbb))) e'')
        (∈ty (models-ty Bd (cExt (cWk ρp) bbb)))
          (∈t (proj₂ (asder2 (∈ty aucs)) p)) bar
      where
        bbb = beeh {A} (↘t1 auxA) (∈ty auxA) p
        auxBee = (models-ty Bd (cExt (cWk ρp) bbb))
        foo = tm-irrel𝒯 refl refl (wk-subst A) (Eval-fun
          (≡Eval (wk-subst A) refl (wkEval (↘t1 auxA))) (ev bbb))
            (wk𝒯 (∈ty auxA) w) (inT bbb) p (wit (nn bbb)) relsa
        bar = ≡preserv {ty = ∈ty (models-ty Bd (cExt (cWk ρp) bbb))}
          (sym (trans (sub-comp B) (≈ˢsub (≈ˢcons (eq-dot sub-id-R)) B)))
            (Bh (cExt (cWk {w = w} ρp) bbb) mc (#® (·® rels wp) foo))
        e = ↘t1 (⊧sub Θ auxB ρp (bound0 (↘t1 auxA) (∈ty auxA)))
        e' = ↘s (proj₂ (asder2 (∈ty aucs)) p)
        eqq = ≈ˢsub (≈ˢcons (eq-dot sub-id-R)) B
        e'' = ≡Eval eqq refl (sub-uncomm {B} e e')
