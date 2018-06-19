module Syntax.Raw.Evaluation.EvaluationProperties where

open import Data.Sum
open import Utils
open import Data.Nat
open import Syntax.Raw.Evaluation.Evaluation
open import Syntax.Raw.Evaluation.Redex
open import Syntax.Raw.Term
open import Syntax.Raw.NormalForm
open import Syntax.Raw.Substitution
open import Data.Empty
open import Relation.Binary.PropositionalEquality

mutual
  ●-fun : ∀{t s a b} → t ● s ↘ a → t ● s ↘ b → a ≡ b
  ●-fun (●β x e1) (●β y e2) = Eval-fun e1 e2
  ●-fun (●β x x₁) (●Ne y) = ⊥-elim (NeApp¬β y x)
  ●-fun (●Ne x) (●β y x₂) = ⊥-elim (NeApp¬β x y)
  ●-fun (●Ne x) (●Ne x₁) = refl

  Eval-fun : ∀{t a b} → Eval t ↘ a → Eval t ↘ b → a ≡ b
  Eval-fun eBound eBound = refl
  Eval-fun eFree eFree = refl
  Eval-fun eU eU = refl
  Eval-fun (eLam e1 e2) (eLam e3 e4) = cong₂ Lam (Eval-fun e1 e3) (Eval-fun e2 e4)
  Eval-fun (ePi e1 e2) (ePi e3 e4) = cong₂ Π (Eval-fun e1 e3) (Eval-fun e2 e4)
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 x₁) with Eval-fun e1 e3 | Eval-fun e2 e4
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 y) | refl | refl = ●-fun x y

Eval-fun' : ∀{t s a b} → Eval t ↘ a → Eval s ↘ b → t ≡ s → a ≡ b
Eval-fun' e1 e2 refl = Eval-fun e1 e2

mutual

  nfApp : ∀{t s a} → Nf t → Nf s → t ● s ↘ a → Nf a
  nfApp nft nfs (●β x y) = nfEval y
  nfApp nft nfs (●Ne x) = nfNe x

  nfEval : ∀{t s} → Eval t ↘ s → Nf s
  nfEval eBound = nfNe neBound
  nfEval eFree = nfNe neFree
  nfEval eU = nfU
  nfEval (eLam evA evt) = nfLam (nfEval evA) (nfEval evt)
  nfEval (ePi e e₁) = nfPi (nfEval e) (nfEval e₁)
  nfEval (eApp e e' x) = nfApp (nfEval e) (nfEval e') x

mutual
  ●-Tm : ∀{t s a n} → Tm n t → Tm n s → t ● s ↘ a → Tm n a
  ●-Tm (tmLam {n = n} tmt tmt₁) tms (●β (βrdx x x₂ x₃) x₁) =
    liftTm n (Eval-Tm (sub-cover-lemma 0 0 x₂ x₃) x₁)
  ●-Tm tmt tms (●Ne x) = tmApp tmt tms

  Eval-Tm : ∀{t s n} → Tm n t → Eval t ↘ s → Tm n s
  Eval-Tm (tmVar x₁) eBound = tmVar x₁
  Eval-Tm tmFree eFree = tmFree
  Eval-Tm tmU eU = tmU
  Eval-Tm (tmLam tm tm₁) (eLam e e₁) = tmLam (Eval-Tm tm e) (Eval-Tm tm₁ e₁)
  Eval-Tm (tmPi tm tm₁) (ePi e e₁) = tmPi (Eval-Tm tm e) (Eval-Tm tm₁ e₁)
  Eval-Tm (tmApp tm₁ tm₂) (eApp e e' x) = ●-Tm (Eval-Tm tm₁ e) (Eval-Tm tm₂ e') x

mutual

  ●wk : ∀{w t s a} → t ● s ↘ a → wk t w ● wk s w ↘ wk a w
  ●wk {w} (●β (βrdx tmA tmt tms) y) =
    ≡App' (sym (null-wk {w} (tmLam tmA tmt))) (sym (null-wk {w} tms))
      (sym (null-wk {w} (Eval-Tm (sub-cover-lemma 0 0 tmt tms) y)))
        (●β (βrdx tmA tmt tms) y)
  ●wk {w} (●Ne x) = ●Ne (neWkLemma x)

  wkEval : ∀{t s w} → Eval t ↘ s → Eval wk t w ↘ wk s w
  wkEval eBound = eBound
  wkEval eFree = eFree
  wkEval eU = eU
  wkEval (eLam e e₁) = eLam (wkEval e) (wkEval e₁)
  wkEval (ePi e e₁) = ePi (wkEval e) (wkEval e₁)
  wkEval (eApp e e' x) =
    eApp (wkEval e) (wkEval e') (●wk x)

≡Eval : ∀{t s a b} → t ≡ s → a ≡ b → Eval t ↘ a → Eval s ↘ b
≡Eval refl refl e = e

wkEval' : ∀{a σ w} t → Eval sub t σ ↘ a → Eval sub t (σ · w) ↘ wk a w
wkEval' t e = ≡Eval (wk-subst t) refl (wkEval e)

nfSelf : ∀{t} → Nf t → Eval t ↘ t
nfSelf (nfLam nf nf₁) = eLam (nfSelf nf) (nfSelf nf₁)
nfSelf nfU = eU
nfSelf (nfPi nf nf₁) = ePi (nfSelf nf) (nfSelf nf₁)
nfSelf (nfNe x) with neView x
nfSelf (nfNe x) | NVApp x₁ x₂ x₃ =
  eApp (nfSelf x₂) (nfSelf x₃) (●Ne x)
nfSelf (nfNe x) | NVFree = eFree
nfSelf (nfNe x) | NVBound = eBound


mutual
  ●-¬Tm : ∀{t s a n} → t ● s ↘ a → ¬Tm n (App t s) → ¬Tm n a
  ●-¬Tm (●β (βrdx x x₂ x₃) x₁) (¬tmApp₁ tm) =
    ⊥-elim (¬Tm-lemma tm (liftTm _ (tmLam x x₂)))
  ●-¬Tm (●β (βrdx x x₃ x₄) x₁) (¬tmApp₂ x₂ tm) =
    ⊥-elim (¬Tm-lemma tm (liftTm _ x₄))
  ●-¬Tm (●Ne x) tm = tm

  Eval-¬Tm : ∀{t a n} → Eval t ↘ a → ¬Tm n t → ¬Tm n a
  Eval-¬Tm eBound tm = tm
  Eval-¬Tm eFree tm = tm
  Eval-¬Tm eU tm = tm
  Eval-¬Tm (eLam e e₁) (¬tmLam₁ tm) = ¬tmLam₁ (Eval-¬Tm e tm)
  Eval-¬Tm (eLam e e₁) (¬tmLam₂ x tm) = ¬tmLam₂ (Eval-Tm x e) (Eval-¬Tm e₁ tm)
  Eval-¬Tm (ePi e e₁) (¬tmPi₁ tm) = ¬tmPi₁ (Eval-¬Tm e tm)
  Eval-¬Tm (ePi e e₁) (¬tmPi₂ x tm) = ¬tmPi₂ (Eval-Tm x e) (Eval-¬Tm e₁ tm)
  Eval-¬Tm (eApp e e' x) (¬tmApp₁ tm) = ●-¬Tm x (¬tmApp₁ (Eval-¬Tm e tm))
  Eval-¬Tm (eApp e e' x) (¬tmApp₂ x₁ tm) =
    ●-¬Tm x (¬tmApp₂ (Eval-Tm x₁ e) (Eval-¬Tm e' tm))

Eval-Tm' : ∀{t n a} → Eval t ↘ a → Tm n a → Tm n t
Eval-Tm' {t} {n} e tm with decTm n t
Eval-Tm' e tm | inj₁ x = x
Eval-Tm' e tm | inj₂ y = ⊥-elim (¬Tm-lemma (Eval-¬Tm e y) tm)

Eval-¬Tm' : ∀{t a n} → Eval t ↘ a → ¬Tm n a → ¬Tm n t
Eval-¬Tm' e ¬tm = ¬Tm-lemma' λ x → ¬Tm-lemma ¬tm (Eval-Tm x e)

sub-var-comm2 : ∀{s a b} → ∀ w n x
  → Eval wk (sub-var x (shift n (Id , a))) w ↘ b → Eval s ↘ a
  → Eval wk (sub-var x (shift n (Id , s))) w ↘ b
sub-var-comm2 w zero zero ex es
  with sym (Eval-fun (wkEval {w = w} (nfSelf (nfEval es))) ex)
sub-var-comm2 w zero zero ex es | refl = wkEval {w = w} es
sub-var-comm2 w zero (suc x) ex es = ex
sub-var-comm2 w (suc n) zero ex es = ex
sub-var-comm2 w (suc n) (suc x) ex es =
  ≡Eval (sym (wk-comp _)) refl
        (sub-var-comm2 (Up Id ·ʷ w) n x
          (≡Eval (wk-comp _) refl ex) es)

sub-comm2 : ∀{t s a b} → ∀ n
          → Eval sub t (shift n (Id , a)) ↘ b → Eval s ↘ a
          → Eval sub t (shift n (Id , s)) ↘ b
sub-comm2 {Free x} n et es = et
sub-comm2 {Bound x} n et es =
  ≡Eval (id-wk 0 _) refl (sub-var-comm2 Id n x
    (≡Eval (sym (id-wk 0 _)) refl et) es)
sub-comm2 {Lam A t} n (eLam et et₁) es =
  eLam (sub-comm2 {A} n et es) (sub-comm2 {t} (suc n) et₁ es)
sub-comm2 {App t s} n (eApp x₁ x₂ x₃) es =
  eApp (sub-comm2 {t} n x₁ es) (sub-comm2 {s} n x₂ es) x₃
sub-comm2 {U} n et es = et
sub-comm2 {Π A B} n (ePi x x₁) es =
  ePi (sub-comm2 {A} n x es) (sub-comm2 {B} (suc n) x₁ es)

sub-var-comm3 : ∀{s a b} → ∀ w n x
  → Eval wk (sub-var x (shift n (Id , s))) w ↘ b → Eval s ↘ a
  → Eval wk (sub-var x (shift n (Id , a))) w ↘ b
sub-var-comm3 w zero zero ex es =
  ≡Eval (sym (Eval-fun (wkEval {w = w} es) ex)) refl (nfSelf (nfEval ex))
sub-var-comm3 w zero (suc x) ex es = ex
sub-var-comm3 w (suc n) zero ex es = ex
sub-var-comm3 w (suc n) (suc x) ex es =
  ≡Eval (sym (wk-comp _)) refl (sub-var-comm3 (Up Id ·ʷ w) n x
    (≡Eval (wk-comp _) refl ex) es)

sub-comm3 : ∀{t s a b} → ∀ n
          → Eval sub t (shift n (Id , s)) ↘ b → Eval s ↘ a
          → Eval sub t (shift n (Id , a)) ↘ b
sub-comm3 {Free x} n et es = et
sub-comm3 {Bound x} n et es =
  ≡Eval (id-wk 0 _) refl (sub-var-comm3 Id n x
    (≡Eval (sym (id-wk 0 _)) refl et) es)
sub-comm3 {Lam A t} n (eLam et et₁) es =
  eLam (sub-comm3 {A} n et es) (sub-comm3 {t} (suc n) et₁ es)
sub-comm3 {App t s} n (eApp x₁ x₂ x₃) es =
  eApp (sub-comm3 {t} n x₁ es) (sub-comm3 {s} n x₂ es) x₃
sub-comm3 {U} n et es = et
sub-comm3 {Π A B} n (ePi x x₁) es =
  ePi (sub-comm3 {A} n x es) (sub-comm3 {B} (suc n) x₁ es)

invert-eval-Π1 : ∀{A B A' B'} → Eval Π A B ↘ Π A' B' → Eval A ↘ A'
invert-eval-Π1 (ePi e e₁) = e

invert-eval-Π2 : ∀{A B A' B'} → Eval Π A B ↘ Π A' B' → Eval B ↘ B'
invert-eval-Π2 (ePi e e₁) = e₁
