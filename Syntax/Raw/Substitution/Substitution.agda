module Syntax.Raw.Substitution.Substitution where

open import Utils
open import Function
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming public
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat

data Subst : Set where
  Id  : Subst
  _·_ : Subst → Wk → Subst
  _,_ : Subst → Term → Subst
infixl 7 _,_

sub-var : ℕ → Subst → Term
sub-var x Id = Bound x
sub-var x (σ · w) = wk (sub-var x σ) w
sub-var zero (σ , t) = t
sub-var (suc x) (σ , t) = sub-var x σ

shift : ℕ → Subst → Subst
shift zero σ = σ
shift (suc n) σ = shift n σ · Up Id , Bound 0

sh : Subst → Subst
sh σ = shift 1 σ

sub : Term → Subst → Term
sub (Free x) σ = Free x
sub (Bound x) σ = sub-var x σ
sub (Lam A t) σ = Lam (sub A σ) (sub t (sh σ))
sub (App t s) σ = App (sub t σ) (sub s σ)
sub (Π A B) σ = Π (sub A σ) (sub B (sh σ))
sub U σ = U

_[_] : Term → Term → Term
t [ s ] = sub t (Id , s)

_↑ : Term → Term
t ↑ = wk t (Up Id)

-- Non-dependent function space
infix 5 _=>_
_=>_ : Term → Term → Term
A => B = Π A (wk B (Up Id))

_[_]↑ : Term → Term → Term
t [ s ]↑ = sub t ((Id · Up Id) , s)

_ʷ·_ : Wk → Subst → Subst
w ʷ· Id = Id · w
w ʷ· (σ · w') = (w ʷ· σ) · w'
Id ʷ· (σ , t) = σ , t
Up w ʷ· (σ , t) = w ʷ· σ
Skip w ʷ· (σ , t) = w ʷ· σ , t

_·ˢ_ : Subst → Subst → Subst
σ ·ˢ Id = σ
σ ·ˢ (τ · w) = (σ ·ˢ τ) · w
Id ·ˢ (τ , x) = τ , x
(σ · w) ·ˢ (τ , t) = σ ·ˢ (w ʷ· (τ , t))
(σ , t) ·ˢ (τ , s) = (σ ·ˢ (τ , s)) , sub t (τ , s)

idsub : (Γ : Ctxt) → Subst
idsub Γ = shift (clen Γ) Id

-- idsub ◇ = Id
-- idsub (Γ # x) = sh (idsub Γ)
