module Syntax.Raw.MetaSubstitution where

open import Function
open import Utils
open import Data.Nat
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming
open import Syntax.Raw.Substitution
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

data MetaSubst : Set where
  ⟨⟩  : MetaSubst
  _,_ : MetaSubst → Term → MetaSubst

msLen : MetaSubst → ℕ
msLen ⟨⟩ = 0
msLen (σ , x) = suc (msLen σ)

data ClosedMS : MetaSubst → Set where
  cId   : ClosedMS ⟨⟩
  cCons : ∀{σ t} → ClosedMS σ → Tm 0 t → ClosedMS (σ , t)

msub-var : ℕ → MetaSubst → Term
msub-var x ⟨⟩ = Free x
msub-var x (σ , t) with x ≟ msLen σ
msub-var x (σ , t) | yes p = t
msub-var x (σ , t) | no ¬p = msub-var x σ

msub : Term → MetaSubst → Term
msub (Free x) σ = msub-var x σ
msub (Bound x) σ = Bound x
msub (Lam A t) σ = Lam (msub A σ) (msub t σ)
msub (App t s) σ = App (msub t σ) (msub s σ)
msub (Π A B) σ = Π (msub A σ) (msub B σ)
msub U σ = U

msubc : Ctxt → MetaSubst → Ctxt
msubc ◇ σ = ◇
msubc (Γ # x) σ = msubc Γ σ # msub x σ

mtm-msub-lemma : ∀{σ t s n} → n ≡ msLen σ → MTm n t → msub t (σ , s) ≡ msub t σ
mtm-msub-lemma eq mtmVar = refl
mtm-msub-lemma eq mtmU = refl
mtm-msub-lemma {σ} eq (mtmFree {x = x} y) with x ≟ msLen σ
mtm-msub-lemma {σ} eq (mtmFree {x = x} y) | yes p
  rewrite trans p (sym eq) = ⊥-elim (absurd-suc y)
mtm-msub-lemma {σ} eq (mtmFree {x = x} y) | no ¬p = refl
mtm-msub-lemma eq (mtmLam mtm mtm₁) =
  cong₂ Lam (mtm-msub-lemma eq mtm) (mtm-msub-lemma eq mtm₁)
mtm-msub-lemma eq (mtmApp mtm₁ mtm₂) =
  cong₂ App  (mtm-msub-lemma eq mtm₁)
    (mtm-msub-lemma eq mtm₂)
mtm-msub-lemma eq (mtmPi mtm mtm₁) =
  cong₂ Π (mtm-msub-lemma eq mtm) (mtm-msub-lemma eq mtm₁)

-- cms-cons : ∀{σ t} → ClosedMS (t ∷: σ) → Tm 0 t × ClosedMS σ
-- cms-cons {⟨⟩} (cCons cl x) = x ,, cl
-- cms-cons {σ , x} (cCons cl x₁) =
--   proj₁ (cms-cons {σ} cl) ,, cCons (proj₂ (cms-cons cl)) x₁

cmsub-var : ∀{σ} x → ClosedMS σ → Tm 0 (msub-var x σ)
cmsub-var x cId = tmFree
cmsub-var x (cCons {σ} σp x₁) with x ≟ msLen σ
cmsub-var x (cCons {σ} σp x₁) | yes p = x₁
cmsub-var x (cCons {σ} σp x₁) | no ¬p = cmsub-var x σp

msub-wk : ∀{σ w} t → ClosedMS σ → msub (wk t w) σ ≡ wk (msub t σ) w
msub-wk {w = w} (Free x) σ = sym (null-wk (cmsub-var x σ))
msub-wk (Bound x) σ = refl
msub-wk (Lam t t₁) σ = cong₂ Lam (msub-wk t σ) (msub-wk t₁ σ)
msub-wk (App t₁ t₂) σ = cong₂ App (msub-wk t₁ σ) (msub-wk t₂ σ)
msub-wk U σ = refl
msub-wk (Π t t₁) σ = cong₂ Π (msub-wk t σ) (msub-wk t₁ σ)

sub-var-msub : ∀{s σ} n x → ClosedMS σ
  → msub (sub-var x (shift n (Id , s))) σ ≡ sub-var x (shift n (Id , msub s σ))
sub-var-msub zero zero σ = refl
sub-var-msub zero (suc x) σ = refl
sub-var-msub (suc n) zero σ = refl
sub-var-msub {s} {σ} (suc n) (suc x) σp =
  trans (msub-wk {σ} {Up Id} (sub-var x (shift n (Id , s))) σp)
        (cong (flip wk (Up Id)) (sub-var-msub n x σp))

sub-msub : ∀{s σ} n t
         → ClosedMS σ
         → msub (sub t (shift n (Id , s))) σ
         ≡ sub (msub t σ) (shift n (Id , msub s σ))
sub-msub n (Free x) σ = sym (null-sub (cmsub-var x σ))
sub-msub n (Bound x) σ = sub-var-msub n x σ
sub-msub n (Lam A t) σ = cong₂ Lam (sub-msub n A σ) (sub-msub (suc n) t σ)
sub-msub n (App t₁ t₂) σ = cong₂ App (sub-msub n t₁ σ) (sub-msub n t₂ σ)
sub-msub n U σ = refl
sub-msub n (Π t t₁) σ = cong₂ Π (sub-msub n t σ) (sub-msub (suc n) t₁ σ)

sub-var-msub' : ∀{s σ u} n x → ClosedMS σ
  → msub (sub-var x (shift n (Id · up u Id , s))) σ
  ≡ sub-var x (shift n (Id · up u Id , msub s σ))
sub-var-msub' zero zero σ = refl
sub-var-msub' zero (suc x) σ = refl
sub-var-msub' (suc n) zero σ = refl
sub-var-msub' {s} {σ} {u} (suc n) (suc x) σp =
  trans (msub-wk {σ} {Up Id} (sub-var x (shift n (Id · up u Id , s))) σp)
        (cong (flip wk (Up Id)) (sub-var-msub' {s} {σ} {u} n x σp))

sub-msub' : ∀{s σ} u n t
         → ClosedMS σ
         → msub (sub t (shift n (Id · up u Id , s))) σ
         ≡ sub (msub t σ) (shift n (Id · up u Id , msub s σ))
sub-msub' u n (Free x) σ = sym (null-sub (cmsub-var x σ))
sub-msub' u n (Bound x) σ = sub-var-msub' {u = u} n x σ
sub-msub' u n (Lam A t) σ = cong₂ Lam (sub-msub' u n A σ) (sub-msub' u (suc n) t σ)
sub-msub' u n (App t₁ t₂) σ = cong₂ App (sub-msub' u n t₁ σ) (sub-msub' u n t₂ σ)
sub-msub' u n U σ = refl
sub-msub' u n (Π t t₁) σ = cong₂ Π (sub-msub' u n t σ) (sub-msub' u (suc n) t₁ σ)

-- -- easy but boring
-- postulate sub-msub : ∀{s σ} n t
--                    → ClosedMS σ
--                    → msub (sub t (shift n (Id , s))) σ
--                    ≡ sub (msub t σ) (shift n (Id , msub s σ))
-- -- sub-msub {s} {σ} n t σp =
-- --   trans {!!} (trans (sub-msub' 0 n t σp) {!!})

tm-msub : ∀{σ n t} → ClosedMS σ → Tm n t → Tm n (msub t σ)
tm-msub cms tmFree = liftTm _ (cmsub-var _ cms)
tm-msub cms tmU = tmU
tm-msub cms (tmVar x₁) = tmVar x₁
tm-msub cms (tmLam tm tm₁) = tmLam (tm-msub cms tm) (tm-msub cms tm₁)
tm-msub cms (tmApp tm₁ tm₂) = tmApp (tm-msub cms tm₁) (tm-msub cms tm₂)
tm-msub cms (tmPi tm tm₁) = tmPi (tm-msub cms tm) (tm-msub cms tm₁)

mtm-sub-var : ∀{s n} x m → MTm n s → MTm n (sub-var x (shift m (Id , s)))
mtm-sub-var zero zero mtm = mtm
mtm-sub-var (suc x) zero mtm = mtmVar
mtm-sub-var zero (suc m) mtm = mtmVar
mtm-sub-var (suc x) (suc m) mtm = wkMTm $ mtm-sub-var x m mtm

mtm-sub : ∀{B s n} m → MTm n B → MTm n s → MTm n (sub B (shift m (Id , s)))
mtm-sub m (mtmVar {x = x}) mtms = mtm-sub-var x m mtms
mtm-sub _ mtmU mtms = mtmU
mtm-sub _ (mtmFree x₁) mtms = mtmFree x₁
mtm-sub m (mtmLam mtmB mtmB₁) mtms =
  mtmLam (mtm-sub m mtmB mtms) (mtm-sub (suc m) mtmB₁ mtms)
mtm-sub m (mtmApp mtmB mtmB₁) mtms =
  mtmApp (mtm-sub m mtmB mtms) (mtm-sub m mtmB₁ mtms)
mtm-sub m (mtmPi mtmB mtmB₁) mtms =
  mtmPi (mtm-sub m mtmB mtms) (mtm-sub (suc m) mtmB₁ mtms)

mtm-ext : ∀{δ a} t → MTm (msLen δ) t → msub t δ ≡ msub t (δ , a)
mtm-ext {δ} (Free x) tm with x ≟ msLen δ
mtm-ext (Free x) tm | yes p rewrite p = ⊥-elim (absurd-suc (inv-mtm-free tm))
mtm-ext (Free x) tm | no ¬p = refl
mtm-ext (Bound x) tm = refl
mtm-ext (Lam t t₁) (mtmLam tm tm₁) = cong₂ Lam (mtm-ext t tm) (mtm-ext t₁ tm₁)
mtm-ext (App t t₁) (mtmApp tm tm₁) = cong₂ App (mtm-ext t tm) (mtm-ext t₁ tm₁)
mtm-ext (Π t t₁) (mtmPi tm tm₁) = cong₂ Π (mtm-ext t tm) (mtm-ext t₁ tm₁)
mtm-ext U tm = refl

postulate _↦_ : ℕ → Term → MetaSubst

_[_]ₘ : Term → MetaSubst → Term
_[_]ₘ = msub
