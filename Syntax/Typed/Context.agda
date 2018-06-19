module Syntax.Typed.Context where

open import Utils
open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Syntax.Raw.Term
open import Syntax.Raw.Substitution

infix 4 _[_]ₗ↦_
data _[_]ₗ↦_ : Ctxtₗ → ℕ → Term → Set where
  here : ∀{Γ A n} → n ≡ clen Γ → Γ # A [ n ]ₗ↦ A
  there : ∀{Γ A B n} → Γ [ n ]ₗ↦ A → Γ # B [ n ]ₗ↦ A

infix 4 _[_]↦_
data _[_]↦_ : Ctxt → ℕ → Term → Set where
  here : ∀{Γ A} → Γ # A [ zero ]↦ A ↑
  there : ∀{Γ A B n} → Γ [ n ]↦ A → Γ # B [ suc n ]↦ A ↑

≡ₗ↦ : ∀{Γ A B n} → A ≡ B → Γ [ n ]ₗ↦ A → Γ [ n ]ₗ↦ B
≡ₗ↦ refl x = x

≡↦ : ∀{Γ A B n} → A ≡ B → Γ [ n ]↦ A → Γ [ n ]↦ B
≡↦ refl x = x


infixl 6 _++_
_++_ : Ctxt → Ctxt → Ctxt
Γ ++ ◇ = Γ
Γ ++ (Γ' # A) = (Γ ++ Γ') # A

infix 6 _+c_
_+c_ : Term → Ctxt → Ctxt
A +c ◇ = ◇ # A
A +c Γ # B = (A +c Γ) # B

-- infixl 6 _+ₗ_
-- _+ₗ_ : Ctxtₗ → Ty → Ctxtₗ
-- ◇ +ₗ A = A ♭ ◇
-- B ♭ Γ +ₗ A = B ♭ (Γ +ₗ A)

-- ◇++ : ∀ Γ → ◇ ++ Γ ≡ Γ
-- ◇++ ◇ = refl
-- ◇++ (Γ # x) = cong (_# x) (◇++ Γ)

-- data _≡ᶜ_++_ : Ctxt → Ctxt → Ctxt → Set where
--   c++ : ∀ Γ Γ' → (Γ ++ Γ') ≡ᶜ Γ ++ Γ'

-- clen : Ctxt → ℕ
-- clen ◇ = 0
-- clen (Γ # x) = suc (clen Γ)

-- clenₗ : Ctxtₗ → ℕ
-- clenₗ ◇ = 0
-- clenₗ (_ ♭ Γ) = suc (clenₗ Γ)

-- +c-clen : ∀ Δ A → clen (A +c Δ) ≡ suc (clen Δ)
-- +c-clen ◇ A = refl
-- +c-clen (Δ # x) A = cong suc (+c-clen Δ A)

-- infix 4 _[_]↦_
-- data _[_]↦_ : Ctxt → ℕ → Ty → Set where
--   here : ∀{Γ A} → Γ # A [ zero ]↦ A
--   there : ∀{Γ A B n} → Γ [ n ]↦ A → Γ # B [ suc n ]↦ A

↦lemma : ∀{n Γ A} → Γ [ n ]↦ A → n < clen Γ
↦lemma here = s≤s z≤n
↦lemma (there x) = s≤s (↦lemma x)

postulate uhm : ∀{n m} → n < m → n ≤ m

≤-≡R : ∀{n m r} → n ≤ r → m ≡ r → n ≤ m
≤-≡R p refl = p

↦ₗlemma : ∀{Θ A n} → Θ [ n ]ₗ↦ A → n < clen Θ
↦ₗlemma (here x) rewrite x = s≤s (≤refl (clen _))
↦ₗlemma (there x) = s≤s (uhm (↦ₗlemma x))

-- tedious...
postulate ↦TmLemma : ∀{Γ A n} → Γ [ n ]↦ A → Tm (clen Γ) (Bound n)

-- infix 4 _[_]ₗ↦_
-- data _[_]ₗ↦_ : Ctxtₗ → ℕ → Ty → Set where
--   here : ∀{Γ A} → A ♭ Γ [ zero ]ₗ↦ A
--   there : ∀{Γ A B n} → Γ [ n ]ₗ↦ A → B ♭ Γ [ suc n ]ₗ↦ A

-- +ₗ-lemma : ∀{Γ n A B} → Γ [ n ]ₗ↦ A → Γ +ₗ B [ n ]ₗ↦ A
-- +ₗ-lemma here = here
-- +ₗ-lemma (there x) = there (+ₗ-lemma x)

-- +c-clen-lemma : ∀{A B} → ∀ Γ → A +c Γ [ clen Γ ]↦ B → A ≡ B
-- +c-clen-lemma ◇ here = refl
-- +c-clen-lemma (Γ # x₁) (there x) = +c-clen-lemma Γ x

-- +ₗ-clen-lemma2 : ∀{A B} → ∀ Θ → Θ +ₗ A [ clenₗ Θ ]ₗ↦ B → A ≡ B
-- +ₗ-clen-lemma2 ◇ here = refl
-- +ₗ-clen-lemma2 (x₁ ♭ Θ) (there x) = +ₗ-clen-lemma2 Θ x

-- +ₗ-clen-lemma : ∀{A} → ∀ Θ → Θ +ₗ A [ clenₗ Θ ]ₗ↦ A
-- +ₗ-clen-lemma ◇ = here
-- +ₗ-clen-lemma (x ♭ Θ) = there (+ₗ-clen-lemma Θ)

-- ¬clen-lemma : ∀{A B n} → ∀ Γ → A +c Γ [ n ]↦ B → ¬ clen Γ ≡ n → Γ [ n ]↦ B
-- ¬clen-lemma ◇ here p = ⊥-elim (p refl)
-- ¬clen-lemma ◇ (there ()) p
-- ¬clen-lemma (Γ # _) here p = here
-- ¬clen-lemma (Γ # _) (there x) p = there (¬clen-lemma Γ x λ x₁ → p (cong suc x₁))

-- ¬clenₗ-lemma : ∀{A B n} → ∀ Γ → Γ +ₗ A [ n ]ₗ↦ B → ¬ clenₗ Γ ≡ n → Γ [ n ]ₗ↦ B
-- ¬clenₗ-lemma ◇ here p = ⊥-elim (p refl)
-- ¬clenₗ-lemma ◇ (there ()) p
-- ¬clenₗ-lemma (x₁ ♭ Γ) here p = here
-- ¬clenₗ-lemma (x₁ ♭ Γ) (there x) p = there (¬clenₗ-lemma Γ x λ x₂ → p (cong suc x₂))

-- _-_ : ℕ → ℕ → ℕ
-- zero - m = zero
-- suc n - zero = suc n
-- suc n - suc m = n - m

-- minus-0 : ∀ x → x - 0 ≡ x
-- minus-0 zero = refl
-- minus-0 (suc x) = refl

-- asder : ∀{Γ A n} → ∀ Γ' → clen Γ' ≤ n → Γ ++ Γ' [ n ]↦ A → Γ [ n - clen Γ' ]↦ A
-- asder {n = n} ◇ p x rewrite minus-0 n = x
-- asder (Γ' # B) () here
-- asder (Γ' # B) (s≤s p) (there x) = asder Γ' p x

-- plus-0 : ∀ n → n + 0 ≡ n
-- plus-0 zero = refl
-- plus-0 (suc n) = cong suc (plus-0 n)

-- plus-succ : ∀ n m → n + suc m ≡ suc (n + m)
-- plus-succ zero m = refl
-- plus-succ (suc n) m = cong suc (plus-succ n m)

-- expand-dong : ∀{Γ A n} → ∀ Γ' → Γ [ n ]↦ A → (Γ ++ Γ') [ n + clen Γ' ]↦ A
-- expand-dong {n = n} ◇ x rewrite plus-0 n = x
-- expand-dong {n = n} (Γ' # x₁) x
--   rewrite plus-succ n (clen Γ') = there (expand-dong Γ' x)

-- expand-dong2 : ∀{Γ A n} → ∀ Γ' → Γ' [ n ]↦ A → (Γ ++ Γ') [ n ]↦ A
-- expand-dong2 ◇ ()
-- expand-dong2 (Γ' # x₁) here = here
-- expand-dong2 (Γ' # x₁) (there x) = there (expand-dong2 Γ' x)

-- boh? : ∀ n m → n ≥ m → suc (n - m) ≡ suc n - m
-- boh? n zero p rewrite minus-0 n = refl
-- boh? zero (suc m) ()
-- boh? (suc n) (suc m) (s≤s p) = boh? n m p

-- ++clen : ∀ Γ Γ' → clen (Γ ++ Γ') ≡ clen Γ + clen Γ'
-- ++clen Γ ◇ = sym (plus-0 (clen Γ))
-- ++clen Γ (Γ' # x) = trans (cong suc (++clen Γ Γ'))
--                           (sym (plus-succ (clen Γ) (clen Γ')))

-- ≤refl : ∀ x → x ≤ x
-- ≤refl zero = z≤n
-- ≤refl (suc x) = s≤s (≤refl x)

-- ≤+' : ∀ {x y} z → x ≤ y → x ≤ (z + y)
-- ≤+' z z≤n = z≤n
-- ≤+' {suc x} {suc y} z (s≤s p) rewrite plus-succ z y = s≤s (≤+' z p)

-- ≤+ : ∀ {x y} z → x ≤ y → x ≤ (y + z)
-- ≤+ z z≤n = z≤n
-- ≤+ z (s≤s p) = s≤s (≤+ z p)

-- ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
-- ≤trans z≤n q = z≤n
-- ≤trans (s≤s p) (s≤s q) = s≤s (≤trans p q)

-- same≤ : ∀{x y} → (p q : x ≤ y) → p ≡ q
-- same≤ z≤n z≤n = refl
-- same≤ (s≤s p) (s≤s q) = cong s≤s (same≤ p q)

-- qqee : ∀ x y n → x + y ≤ n → x ≤ n
-- qqee zero y n p = z≤n
-- qqee (suc x) y zero ()
-- qqee (suc x) y (suc n) (s≤s p) = s≤s (qqee x y n p)

-- asdgh : ∀{Γ ∇ B n} → ∀ Δ
--       → Γ ++ Δ [ n ]↦ B → clen Δ ≤ n → Γ ++ ∇ ++ Δ [ n + clen ∇ ]↦ B
-- asdgh ◇ x p = expand-dong _ x
-- asdgh (Δ # A) here ()
-- asdgh (Δ # A) (there x) (s≤s p) = there (asdgh Δ x p)

-- qwerty : ∀ m n → ¬ m ≤ n → m > n
-- qwerty zero zero p = ⊥-elim (p z≤n)
-- qwerty zero (suc n) p = ⊥-elim (p z≤n)
-- qwerty (suc m) zero p = s≤s z≤n
-- qwerty (suc m) (suc n) p = s≤s (qwerty m n (λ z → p (s≤s z)))

-- clen-lemma : ∀ Γ Γ' n
--            → clen (Γ ++ Γ') ≤ n
--            → (n - clen (Γ ++ Γ')) + clen Γ' ≡ n - clen Γ
-- clen-lemma Γ ◇ n p = plus-0 (n - clen Γ)
-- clen-lemma Γ (Γ' # x) zero ()
-- clen-lemma Γ (Γ' # x) (suc n) (s≤s p)
--   rewrite plus-succ (n - clen (Γ ++ Γ')) (clen Γ')
--         | clen-lemma Γ Γ' n p
--         | ++clen Γ Γ' = boh? n (clen Γ) (qqee _ _ _ p)

cut-lemma : ∀{A} → ∀ Γ Δ n → Γ ++ Δ [ n ]↦ A → clen Δ > n → Δ [ n ]↦ A
cut-lemma Γ ◇ n x ()
cut-lemma Γ (Δ # x₁) .0 here p = here
cut-lemma Γ (Δ # x₁) .(suc _) (there x) (s≤s p) = there (cut-lemma Γ Δ _ x p)

-- ++assoc : ∀ Γ Γ' Γ'' → Γ ++ Γ' ++ Γ'' ≡ Γ ++ (Γ' ++ Γ'')
-- ++assoc Γ Γ' ◇ = refl
-- ++assoc Γ Γ' (Γ'' # x) = cong (_# x) (++assoc Γ Γ' Γ'')

-- absurde : ∀ n m → suc n ≤ m → m ≤ n → ⊥
-- absurde zero zero () q
-- absurde zero (suc m) p ()
-- absurde (suc n) zero () q
-- absurde (suc n) (suc m) (s≤s p) (s≤s q) = absurde n m p q

-- plus-swap : ∀ x y → x + suc y ≡ suc x + y
-- plus-swap zero zero = refl
-- plus-swap zero (suc y) = refl
-- plus-swap (suc x) zero = cong suc (plus-succ x 0)
-- plus-swap (suc x) (suc y) = cong suc (plus-swap x (suc y))

-- absurde2 : ∀ x y → x + suc y ≤ y → ⊥
-- absurde2 zero y p = absurde y y p (≤refl y)
-- absurde2 (suc x) zero ()
-- absurde2 (suc x) (suc y) (s≤s p)
--   rewrite plus-swap x (suc y) = absurde2 (suc x) y p

-- +clen : ∀ Γ A → clen (A +c Γ) ≡ suc (clen Γ)
-- +clen ◇ A = refl
-- +clen (Γ # x) A = cong suc (+clen Γ A)

-- +c/++ : ∀ Γ B Δ → Γ # B ++ Δ ≡ Γ ++ (B +c Δ)
-- +c/++ Γ B ◇ = refl
-- +c/++ Γ B (Δ # x) = cong (_# x) (+c/++ Γ B Δ)

-- ≤suc> : ∀ x y → x ≤ y → suc y > x
-- ≤suc> .0 y z≤n = s≤s z≤n
-- ≤suc> .(suc _) .(suc _) (s≤s p) = s≤s (≤suc> _ _ p)

-- ≤suc : ∀ {x y} → x ≤ y → x ≤ suc y
-- ≤suc z≤n = z≤n
-- ≤suc (s≤s p) = s≤s (≤suc p)

-- ≤+suc : ∀ {z} x y → x + suc y ≤ z → x + y ≤ z
-- ≤+suc zero y (s≤s p) = ≤suc p
-- ≤+suc {zero} (suc x) y ()
-- ≤+suc {suc z} (suc x) y (s≤s p) = s≤s (≤+suc x y p)
