module Syntax.Raw.Renaming where

open import Data.Sum
open import Utils
open import Function
open import Syntax.Raw.Term
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat

data Wk : Set where
  Id : Wk
  Up : Wk → Wk
  Skip : Wk → Wk

wk-var : ℕ → Wk → ℕ
wk-var x Id = x
wk-var x (Up w) = suc (wk-var x w)
wk-var zero (Skip w) = zero
wk-var (suc x) (Skip w) = suc (wk-var x w)

wk : Term → Wk → Term
wk (Free x) w = Free x
wk (Bound x) w = Bound (wk-var x w)
wk (Lam A t) w = Lam (wk A w) (wk t (Skip w))
wk (App t s) w = App (wk t w) (wk s w)
wk (Π A B) w = Π (wk A w) (wk B (Skip w))
wk U w = U

wk1 : Term → Term
wk1 t = wk t (Up Id)

up : ℕ → Wk → Wk
up zero w = w
up (suc n) w = Up (up n w)

skip : ℕ → Wk → Wk
skip zero w = w
skip (suc n) w = Skip (skip n w)

null-wk-var : ∀ {w} n x → x ≤ n → wk-var x (skip (suc n) w) ≡ x
null-wk-var zero .0 z≤n = refl
null-wk-var (suc n) zero p = refl
null-wk-var (suc n) (suc x) (s≤s p) = cong suc (null-wk-var n x p)

null-wk : ∀ {w n t} → Tm n t → wk t (skip n w) ≡ t
null-wk tmFree = refl
null-wk tmU = refl
null-wk (tmVar x) = cong Bound (null-wk-var _ _ x)
null-wk (tmLam tm tm₁) = cong₂ Lam (null-wk tm) (null-wk tm₁)
null-wk (tmApp tm₁ tm₂) = cong₂ App (null-wk tm₁) (null-wk tm₂)
null-wk (tmPi tm tm₁) = cong₂ Π (null-wk tm) (null-wk tm₁)

id-wk-var : ∀ n x → wk-var x (skip n Id) ≡ x
id-wk-var zero x = refl
id-wk-var (suc n) zero = refl
id-wk-var (suc n) (suc x) = cong suc (id-wk-var n x)

id-wk : ∀ n t → wk t (skip n Id) ≡ t
id-wk n (Free x) = refl
id-wk n (Bound x) = cong Bound (id-wk-var n x)
id-wk n (Lam A t) = cong₂ Lam (id-wk n A) (id-wk (suc n) t)
id-wk n (App t s) = cong₂ App (id-wk n t) (id-wk n s)
id-wk n U = refl
id-wk n (Π A B) = cong₂ Π (id-wk n A) (id-wk (suc n) B)

-- composition of weakenings
_·ʷ_ : Wk → Wk → Wk
w ·ʷ Id = w
w ·ʷ Up w' = Up (w ·ʷ w')
Id ·ʷ Skip w' = Skip w'
Up w ·ʷ Skip w' = Up (w ·ʷ w')
Skip w ·ʷ Skip w' = Skip (w ·ʷ w')

wk-var-comp : ∀ w w' x → wk-var (wk-var x w) w' ≡ wk-var x (w ·ʷ w')
wk-var-comp w Id x = refl
wk-var-comp w (Up w') x = cong suc (wk-var-comp w w' x)
wk-var-comp Id (Skip w') x = refl
wk-var-comp (Up w) (Skip w') x = cong suc (wk-var-comp w w' x)
wk-var-comp (Skip w) (Skip w') zero = refl
wk-var-comp (Skip w) (Skip w') (suc x) = cong suc (wk-var-comp w w' x)

wk-comp : ∀ {w w'} t → wk (wk t w) w' ≡ wk t (w ·ʷ w')
wk-comp (Free x) = refl
wk-comp {w} {w'} (Bound x) = cong Bound (wk-var-comp w w' x)
wk-comp (Lam A t) = cong₂ Lam (wk-comp A) (wk-comp t)
wk-comp (App t s) = cong₂ App (wk-comp t) (wk-comp s)
wk-comp U = refl
wk-comp (Π A B) = cong₂ Π (wk-comp A) (wk-comp B)

infix 4 _≈ʷ_
data _≈ʷ_ : Wk → Wk → Set where
  ≈ʷin : ∀{w w'} → ((x : ℕ) → wk-var x w ≡ wk-var x w') → w ≈ʷ w'

≈ʷ-meaning : ∀{w w'} → w ≈ʷ w' → (x : ℕ) → wk-var x w ≡ wk-var x w'
≈ʷ-meaning (≈ʷin x) = x

idw-L : ∀ {w} → (Id ·ʷ w) ≈ʷ w
idw-L {w} = ≈ʷin λ x → sym (wk-var-comp Id w x)

≈ʷrefl : ∀{w} → w ≈ʷ w
≈ʷrefl = ≈ʷin (λ x → refl)

≈ʷsym : ∀{w w'} → w ≈ʷ w' → w' ≈ʷ w
≈ʷsym (≈ʷin x) = ≈ʷin λ x₁ → sym (x x₁)

≈ʷtrans : ∀{w w' w''} → w ≈ʷ w' → w' ≈ʷ w'' → w ≈ʷ w''
≈ʷtrans (≈ʷin x) (≈ʷin x₁) = ≈ʷin (λ x₂ → trans (x x₂) (x₁ x₂))

eq-up : ∀{w w'} → w ≈ʷ w' → Up w ≈ʷ Up w'
eq-up (≈ʷin eq) = ≈ʷin λ x → cong suc (eq x)

eq-skip : ∀{w w'} → w ≈ʷ w' → Skip w ≈ʷ Skip w'
eq-skip (≈ʷin eq) = ≈ʷin λ { zero → refl ; (suc x) → cong suc (eq x) }

wk-assoc : ∀ w w' w'' → ((w ·ʷ w') ·ʷ w'') ≈ʷ  (w ·ʷ (w' ·ʷ w''))
wk-assoc w w' w'' = ≈ʷin λ x →
  trans (sym (wk-var-comp (w ·ʷ w') w'' x))
 (trans (trans (cong (flip wk-var w'') (sym (wk-var-comp w w' x)))
        (wk-var-comp w' w'' (wk-var x w))) (wk-var-comp w (w' ·ʷ w'') x))

wk-comp-L : ∀{w w'} w'' → w ≈ʷ w' → (w ·ʷ w'') ≈ʷ (w' ·ʷ w'')
wk-comp-L {w} {w'} w'' (≈ʷin eq) =
  ≈ʷin λ x →
    trans (sym (wk-var-comp w w'' x))
          (trans (cong (flip wk-var w'') (eq x)) (wk-var-comp w' w'' x))

≈ʷwk : ∀{w w'} → w ≈ʷ w' → ∀ t → wk t w ≡ wk t w'
≈ʷwk eq (Free x) = refl
≈ʷwk eq (Bound x) = cong Bound (≈ʷ-meaning eq _)
≈ʷwk eq (Lam A t) = cong₂ Lam (≈ʷwk eq A) (≈ʷwk (eq-skip eq) t)
≈ʷwk eq (App t s) =
  cong₂ App (≈ʷwk eq t) (≈ʷwk eq s)
≈ʷwk eq U = refl
≈ʷwk eq (Π A B) = cong₂ Π (≈ʷwk eq A) (≈ʷwk (eq-skip eq) B)

ups-comp : ∀ n m → (up n Id ·ʷ up m Id) ≈ʷ up (n + m) Id
ups-comp n zero rewrite plus-0 n = ≈ʷrefl
ups-comp n (suc m) rewrite plus-succ n m = eq-up (ups-comp n m)

wk-var≤ : ∀ k m x n → x ≤ n → wk-var x (skip k (up m Id)) ≤ m + n
wk-var≤ zero zero x n p = p
wk-var≤ zero (suc m) x n p = s≤s (wk-var≤ 0 m x n p)
wk-var≤ (suc k) m zero n p = z≤n
wk-var≤ (suc k) m (suc x) zero ()
wk-var≤ (suc k) m (suc x) (suc n) (s≤s p)
  rewrite plus-succ m n = s≤s (wk-var≤ k m x n p)

tm-wk-lemma : ∀{t} n k m → Tm n t → Tm (m + n) (wk t (skip k (up m Id)))
tm-wk-lemma n k m tmFree = tmFree
tm-wk-lemma n k m tmU = tmU
tm-wk-lemma .(suc _) k m (tmVar {n = n} x₁) rewrite plus-succ m n =
  tmVar (wk-var≤ k m _ n x₁)
tm-wk-lemma n k m (tmLam tm tm₁) =
  tmLam (tm-wk-lemma n k m tm)
        (Tm≡ (plus-succ m n) (tm-wk-lemma (suc n) (suc k) m tm₁))
tm-wk-lemma n k m (tmApp tm₁ tm₂) =
  tmApp (tm-wk-lemma n k m tm₁) (tm-wk-lemma n k m tm₂)
tm-wk-lemma n k m (tmPi tm tm₁) =
  tmPi (tm-wk-lemma n k m tm)
       (Tm≡ (plus-succ m n) (tm-wk-lemma (suc n) (suc k) m tm₁))

wk≤ : ∀ w x → x ≤ wk-var x w
wk≤ Id x = ≤refl x
wk≤ (Up w) x = ≤succ (wk≤ w x)
wk≤ (Skip w) zero = z≤n
wk≤ (Skip w) (suc x) = s≤s (wk≤ w x)

sub¬Tm-lemma : ∀{n w t} → ¬Tm n t → ¬Tm n (wk t w)
sub¬Tm-lemma {w = w} (¬tmVar {x = x} p) = ¬tmVar (≤trans p (wk≤ w x))
sub¬Tm-lemma (¬tmLam₁ tm) = ¬tmLam₁ (sub¬Tm-lemma tm)
sub¬Tm-lemma (¬tmLam₂ x tm) = inj¬tmLam₂ (sub¬Tm-lemma tm)
sub¬Tm-lemma (¬tmPi₁ tm) = ¬tmPi₁ (sub¬Tm-lemma tm)
sub¬Tm-lemma (¬tmPi₂ x tm) = inj¬tmPi₂ (sub¬Tm-lemma tm)
sub¬Tm-lemma (¬tmApp₁ t) = ¬tmApp₁ (sub¬Tm-lemma t)
sub¬Tm-lemma (¬tmApp₂ x t) = inj¬tmApp₂ (sub¬Tm-lemma t)

wk-var-ups : ∀ x m → wk-var x (up m Id) ≡ x + m
wk-var-ups x zero = sym (plus-0 x)
wk-var-ups x (suc m) = trans (cong suc (wk-var-ups x m)) (sym (plus-succ x m))

wkMTm : ∀{t n w} → MTm n t → MTm n (wk t w)
wkMTm mtmVar = mtmVar
wkMTm mtmU = mtmU
wkMTm (mtmFree x₁) = mtmFree x₁
wkMTm (mtmLam tm tm₁) = mtmLam (wkMTm tm) (wkMTm tm₁)
wkMTm (mtmApp tm tm₁) = mtmApp (wkMTm tm) (wkMTm tm₁)
wkMTm (mtmPi tm tm₁) = mtmPi (wkMTm tm) (wkMTm tm₁)
