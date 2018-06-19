module Syntax.Raw.Substitution.Equality where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Raw.Substitution.Substitution
open import Data.Nat
open import Syntax.Raw.Term

--------------------------------------------------------------------------------

private
  infix 4 _≈_
  _≈_ : Subst → Subst → Set
  σ ≈ τ = (x : ℕ) → sub-var x σ ≡ sub-var x τ

  eq-shift : ∀{σ τ} → σ ≈ τ → ∀ n → shift n σ ≈ shift n τ
  eq-shift eq zero x = eq x
  eq-shift eq (suc n) zero = refl
  eq-shift eq (suc n) (suc x) = cong (λ x₁ → wk x₁ (Up Id)) (eq-shift eq n x)

  eq-sub : ∀{σ τ} → σ ≈ τ → ∀ t → sub t σ ≡ sub t τ
  eq-sub eq (Free x) = refl
  eq-sub eq (Bound x) = eq x
  eq-sub eq (Lam A t) = cong₂ Lam (eq-sub eq A) (eq-sub (eq-shift eq 1) t)
  eq-sub eq (App t s) = cong₂ App (eq-sub eq t) (eq-sub eq s)
  eq-sub eq (Π A B) = cong₂ Π (eq-sub eq A) (eq-sub (eq-shift eq 1) B)
  eq-sub eq U = refl

infix 4 _≈ˢ_
data _≈ˢ_ : Subst → Subst → Set where
  ≈ˢin : ∀{σ τ} → σ ≈ τ → σ ≈ˢ τ

≈ˢ-meaning : ∀{σ τ} → σ ≈ˢ τ → (x : ℕ) → sub-var x σ ≡ sub-var x τ
≈ˢ-meaning (≈ˢin x) = x

≈ˢrefl : ∀{σ} → σ ≈ˢ σ
≈ˢrefl = ≈ˢin (λ x → refl)

≈ˢsym : ∀{σ τ} → σ ≈ˢ τ → τ ≈ˢ σ
≈ˢsym (≈ˢin x) = ≈ˢin (λ x₁ → sym (x x₁))

≈ˢtrans : ∀{σ τ ρ} → σ ≈ˢ τ → τ ≈ˢ ρ → σ ≈ˢ ρ
≈ˢtrans (≈ˢin x) (≈ˢin x₁) = ≈ˢin (λ x₂ → trans (x x₂) (x₁ x₂))

≈ˢshift : ∀{σ τ} → σ ≈ˢ τ → ∀ n → shift n σ ≈ˢ shift n τ
≈ˢshift (≈ˢin x) n = ≈ˢin (eq-shift x n)

≈ˢcons : ∀{σ τ s} → σ ≈ˢ τ → (σ , s) ≈ˢ (τ , s)
≈ˢcons (≈ˢin eq) = ≈ˢin λ { zero → refl ; (suc x) → eq x }

≈ˢsub : ∀{σ τ} → σ ≈ˢ τ → ∀ t → sub t σ ≡ sub t τ
≈ˢsub (≈ˢin eq) t = eq-sub eq t

--------------------------------------------------------------------------------

open import Relation.Binary

≈ˢ-is-equiv : IsEquivalence _≈ˢ_
≈ˢ-is-equiv = record { refl = ≈ˢrefl ; sym = ≈ˢsym ; trans = ≈ˢtrans }

≈ˢ-is-pre : IsPreorder {A = Subst} _≈ˢ_ _≈ˢ_
≈ˢ-is-pre = record { isEquivalence = ≈ˢ-is-equiv ; reflexive = λ x → x
                   ; trans = λ x y → ≈ˢtrans x y }

≈ˢ-pre : Preorder _ _ _
≈ˢ-pre =
  record { Carrier = Subst ; _≈_ = _≈ˢ_ ; _∼_ = _≈ˢ_ ; isPreorder = ≈ˢ-is-pre }

infixr 6 _∘≡_
_∘≡_ : {A : Set} → {i j k : A} → i ≡ j → j ≡ k → i ≡ k
eq ∘≡ eq' = trans eq eq'

infixr 6 _∘≈ˢ_
_∘≈ˢ_ : ∀{i j k} → i ≈ˢ j → j ≈ˢ k → i ≈ˢ k
eq ∘≈ˢ eq' = ≈ˢtrans eq eq'

-- import Relation.Binary.PreorderReasoning as Pre -- ≈ˢ-pre

-- asder : ∀ σ → σ · Id ≈ˢ σ
-- asder σ = begin σ · Id ∼⟨ sub-id-L {σ} ⟩ σ ∎
--   where open Pre ≈ˢ-pre
