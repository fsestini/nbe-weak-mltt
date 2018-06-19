module Syntax.Typed.Renaming where

open import Function
open import Data.Nat
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p₁ ; proj₂ to p₂)
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming
open import Syntax.Raw.Substitution
open import Syntax.Typed.Context
open import Syntax.Typed.Inversion
open import Syntax.Typed.Typed
open import Syntax.Typed.SizeLemma
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size

open import Syntax.Typed.Model

infix 4 ⟨_⟩_∷_⊢ᵣ_∶_
data ⟨_⟩_∷_⊢ᵣ_∶_ (i : Size) : Ctxt → Ctxt → Wk → Ctxt → Set where
  ⊢Id   : ∀{Θ Γ} → ⟨ i ⟩ Θ ∷ Γ ⊢ᵣ Id ∶ Γ
  ⊢Up   : ∀{Θ Γ Δ A w} {j k : Size< i}
        → ⟨ j ⟩ Θ ∷ Δ ⊢ᵣ w ∶ Γ → ⟨ k ⟩ Θ ∷ Δ ⊢ A
        → ⟨ i ⟩ Θ ∷ Δ # A ⊢ᵣ Up w ∶ Γ
  ⊢Skip : ∀{Θ Γ Δ A w} {j : Size< i} → ⟨ j ⟩ Θ ∷ Δ ⊢ᵣ w ∶ Γ
        → ⟨ i ⟩ Θ ∷ Δ # (wk A w) ⊢ᵣ Skip w ∶ Γ # A

_∷_⊢ᵣ_∶_ : Ctxt → Ctxt → Wk → Ctxt → Set
Θ ∷ Δ ⊢ᵣ w ∶ Γ = ⟨ ∞ ⟩ Θ ∷ Δ ⊢ᵣ w ∶ Γ

⊢up : ∀{Θ Γ} → ⊢ Θ ∷ Γ → Θ ∷ Γ ⊢ᵣ up (clen Γ) Id ∶ ◇
⊢up (⊢◇ x) = ⊢Id
⊢up (⊢# ctx x) = ⊢Up (⊢up ctx) x

⊢wk-↦ : ∀{Θ Δ Γ A w n} → Θ ∷ Δ ⊢ᵣ w ∶ Γ → Γ [ n ]↦ A → Δ [ wk-var n w ]↦ wk A w
⊢wk-↦ {A = A} (⊢Id) x rewrite id-wk 0 A = x
⊢wk-↦ {A = A} (⊢Up {w = w} wp x₁) x
  rewrite sym (wk-comp {w} {Up Id} A) = there (⊢wk-↦ wp x)
⊢wk-↦ (⊢Skip {A = A} {w = w} wp) here =
  ≡↦ (trans (wk-comp A) (sym (trans (wk-comp A) (≈ʷwk (eq-up idw-L) A)))) here
⊢wk-↦ (⊢Skip wp) (there {A = A} x) =
  ≡↦ (wk-comp A ∘≡ sym (wk-comp A ∘≡ ≈ʷwk (eq-up idw-L) A)) (there (⊢wk-↦ wp x))

private
  ⊧⊧_ = λ Θ → ⊢ Θ
  ⊧_∷_ = λ Θ Γ → ∀{Δ w} → Θ ∷ Δ ⊢ᵣ w ∶ Γ → ⊢ Θ ∷ Δ
  _∷_⊧_ = λ Θ Γ A → ∀{Δ w} → Θ ∷ Δ ⊢ᵣ w ∶ Γ → Θ ∷ Δ ⊢ wk A w
  _∷_⊧_∶_ = λ Θ Γ t A → ∀{Δ w} → Θ ∷ Δ ⊢ᵣ w ∶ Γ → Θ ∷ Δ ⊢ wk t w ∶ wk A w
  _∷_⊧_∼_ = λ Θ Γ A B → ∀{Δ w} → Θ ∷ Δ ⊢ᵣ w ∶ Γ → Θ ∷ Δ ⊢ wk A w ∼ wk B w
  _∷_⊧_∼_∶_ = λ Θ Γ t s A → ∀{Δ w} → Θ ∷ Δ ⊢ᵣ w ∶ Γ → Θ ∷ Δ ⊢ wk t w ∼ wk s w ∶ wk A w

ccc : ∀{Θ Γ A} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A → ⊧ Θ ∷ (Γ # A)
ccc ch Ah ⊢Id = ⊢# (ch ⊢Id) (≡ty (id-wk 0 _) $ Ah ⊢Id)
ccc ch Ah (⊢Up w x) = ⊢# (ccc ch Ah w) x
ccc ch Ah (⊢Skip w) = ⊢# (ch w) (Ah w)

wkModel : Model
wkModel = record
  { ⊧⊧_ = ⊧⊧_ ; ⊧_∷_ = ⊧_∷_ ; _∷_⊧_ = _∷_⊧_ ; _∷_⊧_∶_ = _∷_⊧_∶_
  ; _∷_⊧_∼_ = _∷_⊧_∼_ ; _∷_⊧_∼_∶_ = _∷_⊧_∼_∶_
  ; M-⊢ₘ◇ = ⊢◇ ; M-⊢ₘ# = λ x y → ⊢# x (≡ty (id-wk 0 _) (y ⊢Id))
  ; M-⊢◇ = λ { x ⊢Id → ⊢◇ x ; x (⊢Up w A) → ⊢# (invert-ctx-ty A) A } ; M-⊢# = ccc
  ; M-U = λ x x₁ → U (x x₁) ; M-El = λ x w → El (x w)
  ; M-Π = λ h1 h2 h3 w → Π (h2 w) (h3 (⊢Skip w))
  ; M-free = λ _ ch x w →
      ≡tm (sym ((null-wk (ₗ↦Len (invert-ctx-ctx (ch w)) x)))) refl (free (ch w) x)
  ; M-bound = λ ch x w → bound (ch w) (⊢wk-↦ w x)
  ; M-lam = λ x y z w → lam (z (⊢Skip w))
  ; M-app = λ { {B = B} ch Ah th sh Bh w →
      ≡tm (trans (subst-wk B) (sym (trans (wk-subst B)
        (sym (≈ˢsub sub-wk-comp B))))) refl (app (th w) (sh w) (Bh (⊢Skip w))) }
  ; M-U-Π = λ x y z w → U-Π (y w) (z (⊢Skip w))
  ; M-coe = λ x y w → coe (x w) (y w) ; M-∼refl = λ x x₁ → ∼refl (x x₁)
  ; M-∼symm = λ x x₁ → ∼symm (x x₁) ; M-∼trans = λ x y w → ∼trans (x w) (y w)
  ; M-∼Pi = λ _ _ Ah Bh w → ∼Pi (Ah w) (Bh (⊢Skip w)) ; M-∼El = λ x w → ∼El (x w)
  ; M-∼refl' = λ x w → ∼refl (x w) ; M-∼symm' = λ x w → ∼symm (x w)
  ; M-∼trans' = λ x y w → ∼trans (x w) (y w) ; M-∼coe = λ x y w → ∼coe (x w) (y w)
  ; M-∼β = λ { _ _ c th sh w →
      let td = ≡tm' (cong₂ _#_ refl (id-wk 0 _)) (id-wk 1 _) (id-wk 1 _) (th (⊢Skip ⊢Id))
          sd = ≡tm (id-wk 0 _) (id-wk 0 _) (sh ⊢Id)
          tmA = p₁ (tmLen sd) ; tmB = p₁ $ tmLen td
          tmt = p₂ $ tmLen td ; tms = p₂ $ tmLen sd
          eq1 = sym (null-wk (tmApp (tmLam tmA tmt) tms))
          eq2 = sym (null-wk (sub-cover-lemma 0 0 tmt tms))
          eq3 = sym (null-wk (sub-cover-lemma 0 0 tmB tms))
      in ≡∼ eq1 eq2 eq3 (∼β (c w) td sd) }
  ; M-∼ξ = λ _ Ah th w → ∼ξ (Ah w) (th (⊢Skip w))
  ; M-∼compPi = λ _ Ah Bh w → ∼compPi (Ah w) (Bh (⊢Skip w))
  ; M-∼compApp = λ { {B = B} _ rh sh Bh w →
      ≡∼ refl refl (trans (subst-wk B) (sym (trans (wk-subst B)
        (sym (≈ˢsub sub-wk-comp B))))) (∼compApp (rh w) (sh w) (Bh (⊢Skip w))) }
  }

open Modeling wkModel

⊢wk-ctx = model-ctx ; ⊢wk-ty = model-ty ; ⊢wk-tm = model-tm
⊢wk-ty-∼ = model-ty∼ ; ⊢wk-tm-∼ = model-tm∼

⊢·ʷ : ∀{Θ ∇ Δ Γ w w'}
    → Θ ∷ Δ ⊢ᵣ w ∶ Γ → Θ ∷ ∇ ⊢ᵣ w' ∶ Δ → Θ ∷ ∇ ⊢ᵣ w ·ʷ w' ∶ Γ
⊢·ʷ wp (⊢Id) = wp
⊢·ʷ wp (⊢Up wp' x) = ⊢Up (⊢·ʷ wp wp') x
⊢·ʷ (⊢Id) (⊢Skip wp') = ⊢Skip wp'
⊢·ʷ (⊢Up wp x) (⊢Skip wp') = ⊢Up (⊢·ʷ wp wp') (⊢wk-ty x wp')
⊢·ʷ (⊢Skip {A = A} {w = w} wp) (⊢Skip {w = w'} wp')
  rewrite wk-comp {w} {w'} A = ⊢Skip (⊢·ʷ wp wp')
