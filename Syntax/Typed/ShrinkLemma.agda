module Syntax.Typed.ShrinkLemma where

open import Function
open import Syntax.Raw
open import Syntax.Typed.Context
open import Syntax.Typed.Typed
open import Syntax.Typed.Inversion
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Data.Unit
open import Size
open import Relation.Binary.PropositionalEquality
open import Syntax.Typed.SizeLemma
open import Syntax.Typed.EqLemma

mutual

  shrink-ctx : ∀{Θ Γ Δ i} → ⊢⟨ i ⟩ Θ ∷ (Γ ++ Δ) → TmC Δ → ⊢ Θ ∷ Δ
  shrink-ctx {Δ = ◇} ctx tmc = ⊢◇ (invert-ctx-ctx ctx)
  shrink-ctx {Δ = Δ # x} (⊢# ctx ty) (tmC ,, tmA) =
    ⊢# (shrink-ctx ctx tmC) (shrink-ty ty tmC tmA)

  shrink-ty : ∀{Θ Γ Δ A i} → ⟨ i ⟩ Θ ∷ Γ ++ Δ ⊢ A
            → TmC Δ
            → Tm (clen Δ) A → Θ ∷ Δ ⊢ A
  shrink-ty (U x) tmC tm = U (shrink-ctx x tmC)
  shrink-ty (El x) tmC tm = El (shrink-tm x tmC tmU tm)
  shrink-ty (Π Ad Bd) tmC (tmPi tmA tmB) =
    Π (shrink-ty Ad tmC tmA) (shrink-ty Bd (tmC ,, tmA) tmB)

  shrink-tm : ∀{Θ Γ Δ A t i}
            → ⟨ i ⟩ Θ ∷ Γ ++ Δ ⊢ t ∶ A
            → TmC Δ
            → Tm (clen Δ) A → Tm (clen Δ) t
            → Θ ∷ Δ ⊢ t ∶ A
  shrink-tm (free x x₁) tmC tmA tmt = free (shrink-ctx x tmC) x₁
  shrink-tm (bound c x) tmC tmA tmt = bound (shrink-ctx c tmC)
    (cut-lemma _ _ _ x (pj-tm-var tmt))
  shrink-tm (lam td) tmC (tmPi tmA tmB) (tmLam _ tmt) =
    lam (shrink-tm td (tmC ,, tmA) tmB tmt)
  shrink-tm (app {B = B} td sd x) tmC tmA (tmApp tmt tms) =
    app (shrink-tm td tmC (tmPi hA hB) tmt)
      (shrink-tm sd tmC hA tms) (shrink-ty x (tmC ,, hA) hB)
    where hA = (tyCloLemma _ sd tmC tms) ; hB = sub-uncover 0 B tms tmA
  shrink-tm (U-Π Ad Bd) tmC tmU (tmPi tmA tmB) =
    U-Π (shrink-tm Ad tmC tmU tmA) (shrink-tm Bd (tmC ,, tmA) tmU tmB)
  shrink-tm (coe td x) tmC tmA tmt =
    coe (shrink-tm td tmC other tmt) (shrink-ty∼ x tmC other tmA )
    where other = tySameSzLemmaR x tmA

  shrink-ty∼ : ∀{Θ Γ Δ A B i}
             → ⟨ i ⟩ Θ ∷ Γ ++ Δ ⊢ A ∼ B
             → TmC Δ
             → Tm (clen Δ) A → Tm (clen Δ) B
             → Θ ∷ Δ ⊢ A ∼ B
  shrink-ty∼ (∼refl x) tmC tmA tmB = ∼refl (shrink-ty x tmC tmA)
  shrink-ty∼ (∼symm eq) tmC tmA tmB = ∼symm ((shrink-ty∼ eq tmC tmB tmA))
  shrink-ty∼ (∼trans eq eq') tmC tmA tmB =
    ∼trans (shrink-ty∼ eq tmC tmA (tySameSzLemmaL eq tmA))
           (shrink-ty∼ eq' tmC (tySameSzLemmaR eq' tmB) tmB)
  shrink-ty∼ (∼Pi eq eq') tmC (tmPi tmA tmA₁) (tmPi tmB tmB₁) =
    ∼Pi (shrink-ty∼ eq tmC tmA tmB) (shrink-ty∼ eq' (tmC ,, tmA) tmA₁ tmB₁)
  shrink-ty∼ (∼El x) tmC tmA tmB = ∼El (shrink-tm∼ x tmC tmU tmA tmB)

  shrink-tm∼ : ∀{Θ Γ Δ A t s i}
             → ⟨ i ⟩ Θ ∷ Γ ++ Δ ⊢ t ∼ s ∶ A
             → TmC Δ
             → Tm (clen Δ) A → Tm (clen Δ) t → Tm (clen Δ) s
             → Θ ∷ Δ ⊢ t ∼ s ∶ A
  shrink-tm∼ (∼refl x) tmC tmA tmt tms = ∼refl (shrink-tm x tmC tmA tmt)
  shrink-tm∼ (∼symm eq) tmC tmA tmt tms = ∼symm (shrink-tm∼ eq tmC tmA tms tmt)
  shrink-tm∼ (∼trans eq eq') tmC tmA tmt tms =
    ∼trans (shrink-tm∼ eq tmC tmA tmt (tmSameSzLemmaL eq tmt))
           (shrink-tm∼ eq' tmC tmA (tmSameSzLemmaR eq' tms) tms)
  shrink-tm∼ (∼coe eq x) tmC tmA tmt tms =
    ∼coe (shrink-tm∼ eq tmC (tySameSzLemmaR x tmA) tmt tms)
         (shrink-ty∼ x tmC (tySameSzLemmaR x tmA) tmA)
  shrink-tm∼ (∼β cd td sd) tmC tmA tmt tms = ∼β (shrink-ctx cd tmC) td sd
  shrink-tm∼ (∼ξ x eq) tmC (tmPi tmA tmA₁) (tmLam tmt tmt₁) (tmLam tms tms₁) =
    ∼ξ (shrink-ty∼ x tmC tmt tms) (shrink-tm∼ eq (tmC ,, tmt) tmA₁ tmt₁ tms₁)
  shrink-tm∼ (∼compPi eq eq') tmC tmA (tmPi tmt tmt₁) (tmPi tms tms₁) =
    ∼compPi (shrink-tm∼ eq tmC tmA tmt tms)
            (shrink-tm∼ eq' (tmC ,, tmt) tmU tmt₁ tms₁)
  shrink-tm∼ (∼compApp eq eq' x) tmC tmA (tmApp tmt tmt₁) (tmApp tms tms₁) =
    ∼compApp (shrink-tm∼ eq tmC (tmPi hA hB) tmt tms)
             (shrink-tm∼ eq' tmC hA tmt₁ tms₁)
             (shrink-ty x (tmC ,, hA) hB)
    where hA = tyCloLemma _ (eq-lemma-tm1 eq') tmC tmt₁
          hB = sub-uncover 0 _ tmt₁ tmA
