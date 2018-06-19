module Syntax.Raw.Term where

open import Utils
open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

cong₃ : {A B C D : Set} {x x' : A} {y y' : B} {z z' : C}
      → (f : A → B → C → D)
      → x ≡ x' → y ≡ y' → z ≡ z'
      → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

cong₄ : {A B C D E : Set} {x x' : A} {y y' : B} {z z' : C} {w w' : D}
      → (f : A → B → C → D → E)
      → x ≡ x' → y ≡ y' → z ≡ z' → w ≡ w'
      → f x y z w ≡ f x' y' z' w'
cong₄ f refl refl refl refl = refl

data Term : Set where
  Free : ℕ → Term
  Bound : ℕ → Term
  Lam : Term → Term → Term
  App : Term → Term → Term
  U   : Term
  Π   : Term → Term → Term

data Tm : ℕ → Term → Set where
  tmFree : ∀{n x} → Tm n (Free x)
  tmU    : ∀{n} → Tm n U
  tmVar  : ∀{n x} → x ≤ n → Tm (suc n) (Bound x)
  tmLam  : ∀{A t n} → Tm n A → Tm (suc n) t → Tm n (Lam A t)
  tmApp  : ∀{t s n} → Tm n t → Tm n s → Tm n (App t s)
  tmPi   : ∀{n t s} → Tm n t → Tm (suc n) s → Tm n (Π t s)

pj-tm-var : ∀{n x} → Tm n (Bound x) → x < n
pj-tm-var (tmVar x₁) = s≤s x₁

pj-tm-Π₁ : ∀{A B n} → Tm n (Π A B) → Tm n A
pj-tm-Π₁ (tmPi tm tm₁) = tm

pj-tm-Π₂ : ∀{A B n} → Tm n (Π A B) → Tm (suc n) B
pj-tm-Π₂ (tmPi tm tm₁) = tm₁

data MTm : ℕ → Term → Set where
  mtmVar  : ∀{n x} → MTm n (Bound x)
  mtmU    : ∀{n} → MTm n U
  mtmFree : ∀{n x} → x ≤ n → MTm (suc n) (Free x)
  mtmLam  : ∀{A t n} → MTm n A → MTm n t → MTm n (Lam A t)
  mtmApp  : ∀{t s n} → MTm n t → MTm n s → MTm n (App t s)
  mtmPi   : ∀{n t s} → MTm n t → MTm n s → MTm n (Π t s)

inj-mtmFree : ∀{n x} → x < n → MTm n (Free x)
inj-mtmFree (s≤s p) = mtmFree p

inv-mtm-free : ∀{n x} → MTm n (Free x) → x < n
inv-mtm-free {zero} {x} ()
inv-mtm-free {suc n} {x} (mtmFree x₁) = s≤s x₁

inv-mtm-Π : ∀{A B n} → MTm n (Π A B) → MTm n A × MTm n B
inv-mtm-Π (mtmPi mtm mtm₁) = mtm , mtm₁

inv-tm-Π : ∀{A B n} → Tm n (Π A B) → Tm n A × Tm (suc n) B
inv-tm-Π (tmPi tm tm₁) = tm , tm₁

MTm≡ : ∀{n m t s} → n ≡ m → t ≡ s → MTm n t → MTm m s
MTm≡ refl refl tm = tm

Tm≡ : ∀{n m t} → n ≡ m → Tm n t → Tm m t
Tm≡ refl tm = tm

Tm≡' : ∀{n t s} → t ≡ s → Tm n t → Tm n s
Tm≡' refl tm = tm

Tm≡'' : ∀{n m t s} → m ≡ n → s ≡ t → Tm n t → Tm m s
Tm≡'' refl refl tm = tm


data Ctxt : Set where
  ◇ : Ctxt
  _#_ : Ctxt → Term → Ctxt
infixl 7 _#_

Ctxtₗ = Ctxt

clen : Ctxt → ℕ
clen ◇ = 0
clen (Γ # _) = suc (clen Γ)

postulate liftTm : ∀{t n} m → Tm n t → Tm (n + m) t
-- liftTm m tmFree = tmFree
-- liftTm m (tmVar x) = tmVar (≤+ _ x)
-- liftTm m (tmLam {n = n} tm) rewrite sym (plus-succ n m) = tmLam (liftTm m tm)
-- liftTm m (tmApp tm tm') = tmApp (liftTm m tm) (liftTm m tm')

postulate liftMTm : ∀{t n} m → MTm n t → MTm (m + n) t
postulate liftMTm' : ∀{t n} m → MTm n t → MTm (n + m) t
postulate liftMTm≤ : ∀{t n m} → n ≤ m → MTm n t → MTm m t

data ¬Tm : ℕ → Term → Set where
  ¬tmVar : ∀{n x} → x ≥ n → ¬Tm n (Bound x)
  ¬tmLam₁ : ∀{A t n} → ¬Tm n A → ¬Tm n (Lam A t)
  ¬tmLam₂ : ∀{A t n} → Tm n A → ¬Tm (suc n) t → ¬Tm n (Lam A t)
  ¬tmApp₁ : ∀{t s n} → ¬Tm n t → ¬Tm n (App t s)
  ¬tmApp₂ : ∀{t s n} → Tm n t → ¬Tm n s → ¬Tm n (App t s)
  ¬tmPi₁  : ∀{t s n} → ¬Tm n t → ¬Tm n (Π t s)
  ¬tmPi₂  : ∀{t s n} → Tm n t → ¬Tm (suc n) s → ¬Tm n (Π t s)

¬Tm≡ : ∀{t s n m} → t ≡ s → n ≡ m → ¬Tm n t → ¬Tm m s
¬Tm≡ refl refl tm = tm

postulate ¬Tm-lemma : ∀{n t} → ¬Tm n t → Tm n t → ⊥
-- ¬Tm-lemma (¬tmVar p) (tmVar q) = absurde _ _ p q
-- ¬Tm-lemma (¬tmLam ¬tm) (tmLam tm) = ¬Tm-lemma ¬tm tm
-- ¬Tm-lemma (¬tmApp₁ ¬tm) (tmApp tm _) = ¬Tm-lemma ¬tm tm
-- ¬Tm-lemma (¬tmApp₂ x ¬tm) (tmApp _ tm) = ¬Tm-lemma ¬tm tm

decTm : ∀ n (t : Term) → Tm n t ⊎ ¬Tm n t
decTm n (Free x) = inj₁ tmFree
decTm n (Bound x) with suc x ≤? n
decTm .(suc _) (Bound x) | yes (s≤s p) = inj₁ (tmVar p)
decTm n (Bound x) | no ¬p with qwerty _ _ ¬p
decTm n (Bound x) | no ¬p | s≤s w = inj₂ (¬tmVar w)
decTm n (Lam A t) with decTm n A | decTm (suc n) t
decTm n (Lam A t) | inj₁ x | inj₁ x₁ = inj₁ (tmLam x x₁)
decTm n (Lam A t) | inj₁ x | inj₂ y = inj₂ (¬tmLam₂ x y)
decTm n (Lam A t) | inj₂ y | _ = inj₂ (¬tmLam₁ y)
decTm n (App t s) with decTm n t | decTm n s
decTm n (App t s) | inj₁ x | inj₁ x₁ = inj₁ (tmApp x x₁)
decTm n (App t s) | inj₁ x | inj₂ y = inj₂ (¬tmApp₂ x y)
decTm n (App t s) | inj₂ y | _ = inj₂ (¬tmApp₁ y)
decTm n U = inj₁ tmU
decTm n (Π A B) with decTm n A | decTm (suc n) B
decTm n (Π A B) | inj₁ x | inj₁ x₁ = inj₁ (tmPi x x₁)
decTm n (Π A B) | inj₁ x | inj₂ y = inj₂ (¬tmPi₂ x y)
decTm n (Π A B) | inj₂ y | _ = inj₂ (¬tmPi₁ y)

¬Tm-lemma' : ∀{n t} → (Tm n t → ⊥) → ¬Tm n t
¬Tm-lemma' {t = Free x} h = ⊥-elim (h tmFree)
¬Tm-lemma' {n} {Bound x} h with n ≤? x
¬Tm-lemma' {n} {Bound x} h | yes p = ¬tmVar p
¬Tm-lemma' {zero} {Bound x} h | no ¬p = ⊥-elim (¬p z≤n)
¬Tm-lemma' {suc n} {Bound x} h | no ¬p with qwerty _ _ ¬p
¬Tm-lemma' {suc n} {Bound x} h | no ¬p | s≤s w = ⊥-elim (h (tmVar w))
¬Tm-lemma' {n} {Lam A t} h with decTm n A | decTm (suc n) t
¬Tm-lemma' h | inj₁ x | inj₁ y = ⊥-elim (h (tmLam x y))
¬Tm-lemma' h | inj₁ x | inj₂ y = ¬tmLam₂ x y
¬Tm-lemma' h | inj₂ y | _ = ¬tmLam₁ y
¬Tm-lemma' {n} {App t s} h with decTm n t | decTm n s
¬Tm-lemma' h | inj₁ x₁ | inj₁ x₂ = ⊥-elim (h (tmApp x₁ x₂))
¬Tm-lemma' h | inj₁ x₁ | inj₂ y = ¬tmApp₂ x₁ y
¬Tm-lemma' h | inj₂ y | _ = ¬tmApp₁ y
¬Tm-lemma' {t = U} h = ⊥-elim (h tmU)
¬Tm-lemma' {n} {Π A B} h with decTm n A | decTm (suc n) B
¬Tm-lemma' h | inj₁ x | inj₁ x₁ = ⊥-elim (h (tmPi x x₁))
¬Tm-lemma' h | inj₁ x | inj₂ y = ¬tmPi₂ x y
¬Tm-lemma' h | inj₂ y | _ = ¬tmPi₁ y

inj¬tmLam₂ : ∀{n A t} → ¬Tm (suc n) t → ¬Tm n (Lam A t)
inj¬tmLam₂ {n} {A} {t} tm with decTm n A
inj¬tmLam₂ {n} {A} {t} tm | inj₁ x = ¬tmLam₂ x tm
inj¬tmLam₂ {n} {A} {t} tm | inj₂ y = ¬tmLam₁ y

inj¬tmApp₂ : ∀{n t s} → ¬Tm n s → ¬Tm n (App t s)
inj¬tmApp₂ {n} {t} tm with decTm n t
inj¬tmApp₂ {n} {t} tm | inj₁ x₁ = ¬tmApp₂ x₁ tm
inj¬tmApp₂ {n} {t} tm | inj₂ y = ¬tmApp₁ y

inj¬tmPi₂ : ∀{n A B} → ¬Tm (suc n) B → ¬Tm n (Π A B)
inj¬tmPi₂ {n} {A} tm with decTm n A
inj¬tmPi₂ {n} {A} tm | inj₁ x = ¬tmPi₂ x tm
inj¬tmPi₂ {n} {A} tm | inj₂ y = ¬tmPi₁ y

--------------------------------------------------------------------------------

-- wkTerm : ∀{Θ Γ Δ A t} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Δ ++ Γ ⊢ t ∶ A
-- wkTerm (free x) = free x
-- wkTerm (var x) = var (expand-dong2 _ x)
-- wkTerm (lam t) = lam (wkTerm t)
-- wkTerm (t ● s) = wkTerm t ● wkTerm s

-- ♭sub : Term → ℕ → Term → Term
-- ♭sub (Free x) l a with l ≟ x
-- ♭sub (Free x) .x a | yes refl = a
-- ♭sub (Free x) l a | no ¬p = Free x
-- ♭sub (Bound x) l a = Bound x
-- ♭sub (Lam t) l a = Lam (♭sub t l a)
-- ♭sub (t · s) l a = ♭sub t l a · ♭sub s l a

-- ⊢♭sub : ∀{Θ Γ A t s B} → Θ +ₗ A ∷ Γ ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
--      → Θ ∷ Γ ⊢ ♭sub t (clenₗ Θ) s ∶ B
-- ⊢♭sub {Θ} (free {n = n} x) s with clenₗ Θ ≟ n
-- ⊢♭sub {Θ} {Γ} (free {n = .(clenₗ Θ)} x) s | yes refl with +ₗ-clen-lemma2 _ x
-- ⊢♭sub {Θ} {Γ} (free {_} {_} {_} {.(clenₗ Θ)} x) s | yes refl | refl =
--   wkTerm {Θ} {◇} {Γ} s
-- ⊢♭sub {Θ} (free {n = n} x) s | no ¬p = free (¬clenₗ-lemma _ x ¬p)
-- ⊢♭sub (var x) s = var x
-- ⊢♭sub (lam t) s = lam (⊢♭sub t s)
-- ⊢♭sub (t ● s) a = ⊢♭sub t a ● ⊢♭sub s a
