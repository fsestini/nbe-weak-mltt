module Semantics.Soundness.LogicalRelation.Temp where

open import Data.Nat
open import Function
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness -- .Type.Type
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Semantics.Soundness.LogicalRelation.Definition
open import Semantics.Soundness.LogicalRelation.Preservation
open import Semantics.Soundness.LogicalRelation.Irrelevance
open import Semantics.Soundness.LogicalRelation.Kripke

open import Size
open import Syntax.Typed.Inversion

open _[_,_]
open _[_,_]∈_
open SemTy
open _●_∈ap_
open _∈_
