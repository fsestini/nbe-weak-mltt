module Semantics.Domain.Domain where

open import Syntax
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_)
open import Data.List

D = Term

Rnf : D → Term
Rnf x = x

_[_]↘_ : Term → Subst → Term → Set
t [ σ ]↘ a = Eval sub t σ ↘ a
