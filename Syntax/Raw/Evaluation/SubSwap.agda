module Syntax.Raw.Evaluation.SubSwap where

open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Utils
open import Data.Nat
open import Syntax.Raw.Evaluation.Evaluation
open import Syntax.Raw.Evaluation.EvaluationProperties
open import Syntax.Raw.Evaluation.Redex
open import Syntax.Raw.Term
open import Syntax.Raw.NormalForm
open import Syntax.Raw.Substitution
open import Data.Empty
open import Relation.Binary.PropositionalEquality

record SubComp (t b : Term) (σ : Subst) : Set where
  field
    {tm} : Term
    ev1 : Eval t ↘ tm
    ev2 : Eval sub tm σ ↘ b
open SubComp

mutual
  sub-swap' : ∀{t a b σ} → Eval t ↘ a → Eval sub t σ ↘ b → Eval sub a σ ↘ b
  sub-swap' {t} e1 e2 with sub-swap t e2
  sub-swap' e1 e2 | record { tm = tm ; ev1 = ev1 ; ev2 = ev2 } =
    ≡Eval (cong₂ sub (Eval-fun ev1 e1) refl) refl ev2

  NeTransport : ∀{t σ a b} → Eval sub t σ ↘ a → Eval t ↘ b → Ne a → Ne b
  NeTransport ea eb ne = aux (nfEval eb) (sub-swap' eb ea) ne
      where
        aux : ∀{b σ a} → Nf b → Eval sub b σ ↘ a → Ne a → Ne b
        aux (nfLam nf nf₁) (eLam e e₁) ()
        aux nfU eU ()
        aux (nfPi nf nf₁) (ePi e e₁) ()
        aux (nfNe x) e ne = x

  NeAppTransferLemma : ∀{t t' t'' s s' s'' σ}
                     → Eval sub t σ ↘ t' → Eval sub s σ ↘ s'
                     → Eval t ↘ t'' → Eval s ↘ s''
                     → Ne (App t' s') → Ne (App t'' s'')
  NeAppTransferLemma et es et' es' (neApp ne x x₁ x₂) =
    inj-neApp (NeTransport et et' ne) (nfEval es')
  NeAppTransferLemma et es et' es' (neApp₁ x x₁ x₂) =
    neApp₁ (nfEval et') (nfEval es')
      (Eval-¬Tm et' (¬Tm-sub-lemma 0 (Eval-¬Tm' et x₂)))
  NeAppTransferLemma et es et' es' (neApp₂ x x₁ x₂ x₃) =
    inj-neApp₂ (nfEval et') (nfEval es')
      (Eval-¬Tm es' (¬Tm-sub-lemma 0 (Eval-¬Tm' es x₃)))

  sub-swap : ∀{σ b} t → Eval sub t σ ↘ b → SubComp t b σ
  sub-swap (Free x) eFree = record { ev1 = eFree ; ev2 = eFree }
  sub-swap (Bound x) e = record { ev1 = eBound ; ev2 = e }
  sub-swap (Lam A t) (eLam e e₁) =
    record { ev1 = eLam (ev1 ih) (ev1 ih') ; ev2 = eLam (ev2 ih) (ev2 ih') }
    where ih = sub-swap A e ; ih' = sub-swap t e₁
  sub-swap (App t s) (eApp e₁ e₂ x) = ●-sub-swap t s e₁ e₂ x
  sub-swap U e = record { ev1 = eU ; ev2 = e }
  sub-swap (Π A B) (ePi e e₁) =
    record { ev1 = ePi (ev1 ih) (ev1 ih') ; ev2 = ePi (ev2 ih) (ev2 ih') }
    where ih = sub-swap A e ; ih' = sub-swap B e₁

  ●-sub-swap : ∀{t' s' b σ} t s
    → Eval sub t σ ↘ t' → Eval sub s σ ↘ s' → t' ● s' ↘ b
    → SubComp (App t s) b σ
  ●-sub-swap {t'} {s'} {b} {σ} t s et es ap@(●β rdx ev) = goal
    where
      ih' = sub-swap t et ; ih'' = sub-swap s es
      rdx? = decβ-Redex
               (EvLamSubj (nfEval (ev1 ih')) (ev2 ih'))
                 (nfEval (ev1 ih''))
      goal : SubComp (App t s) b σ
      goal with rdx?
      goal | inj₁ x with sub-swap t et
      goal | inj₁ rr@(βrdx {t = t''} x x₁ x₂) | record { ev1 = tev1 ; ev2 = tev2 } =
        record { ev1 = eApp tev1 (ev1 ih'') (●β (βrdx x x₁ x₂)
                         (≡Eval (cong₂ sub teq (cong₂ _,_ refl seq)) refl ev))
               ; ev2 = ≡Eval (sym (null-sub (Eval-Tm (sub-cover-lemma 0 0
                   (β-Redex-Tm-Lam-t rdx) (β-Redex-Tm-s rdx)) ev)))
                     refl (nfSelf (nfEval ev)) }
        where
          tm0 = Eval-Tm' tev1 (tmLam x x₁)
          teq = Lam-inj (Eval-fun (≡Eval (null-sub tm0) refl et) tev1)
          seq = Eval-fun (ev2 ih'') (≡Eval (sym (null-sub x₂)) refl
                         (nfSelf (nfEval (ev1 ih''))))
      goal | inj₂ y =
        record { ev1 = eApp (ev1 ih') (ev1 ih'') (●Ne y)
               ; ev2 = eApp (ev2 ih') (ev2 ih'') ap }
  ●-sub-swap t s et es (●Ne x) =
    record { ev1 = eApp (ev1 ih') (ev1 ih'')
                     (●Ne (NeAppTransferLemma et es (ev1 ih') (ev1 ih'') x))
           ; ev2 = eApp (ev2 ih') (ev2 ih'') (●Ne x) }
    where ih' = sub-swap t et ; ih'' = sub-swap s es

sub-comm : ∀{t a b σ σ'}
         → Eval sub t σ ↘ b → Eval sub t (σ ·ˢ σ') ↘ a → Eval sub b σ' ↘ a
sub-comm {t} {σ = σ} {σ'} e1 e2
  rewrite sym (sub-comp {σ} {σ'} t) = sub-swap' e1 e2

●-sub-swap' : ∀{B B' t t' s s' b σ}
             → Nf B → Nf t → Nf s
             → Eval sub B (sh σ) ↘ B' → Eval sub t σ ↘ t' → Eval sub s σ ↘ s'
             → t' ● s' ↘ b
             → Σ Term λ a → t ● s ↘ a × Eval sub a σ ↘ b
●-sub-swap' {B} {_} {t} {_} {s} nfB nft ns eB et es ap
  with ●-sub-swap t s et es ap
●-sub-swap' nfB nft ns eB et es ap |
  record { ev1 = eApp ev4 ev5 x ; ev2 = ev2 }
  rewrite Eval-fun (nfSelf nft) ev4
        | Eval-fun (nfSelf ns) ev5 = _ ,, x ,, ev2

sub-unswap : ∀{t a b σ} → Eval t ↘ a → Eval sub a σ ↘ b → Eval sub t σ ↘ b
sub-unswap eBound e2 = e2
sub-unswap eFree e2 = e2
sub-unswap eU e2 = e2
sub-unswap (eLam e1 e3) (eLam e2 e4) = eLam (sub-unswap e1 e2) (sub-unswap e3 e4)
sub-unswap (ePi e1 e3) (ePi e2 e4) = ePi (sub-unswap e1 e2) (sub-unswap e3 e4)
sub-unswap e@(eApp e1 e3 (●β r@(βrdx x x₂ x₃) x₁)) e2 =
  ≡Eval (sym (null-sub (tmApp (Eval-Tm' e1 (tmLam x x₂)) (Eval-Tm' e3 x₃))))
    (Eval-fun (≡Eval (sym (null-sub (Eval-Tm (sub-cover-lemma 0 0 x₂ x₃) x₁)))
      refl (nfSelf (nfEval x₁))) e2) e
sub-unswap (eApp e1 e3 (●Ne x)) (eApp e2 e4 x₁) =
  eApp (sub-unswap e1 e2) (sub-unswap e3 e4) x₁

sub-uncomm : ∀{t a b σ σ'}
           → Eval sub t σ ↘ a → Eval sub a σ' ↘ b → Eval sub t (σ ·ˢ σ') ↘ b
sub-uncomm {t} e1 e2 = ≡Eval (sub-comp t) refl (sub-unswap e1 e2)
