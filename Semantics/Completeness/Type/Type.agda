module Semantics.Completeness.Type.Type where

open import Syntax hiding (_,_)
open import Semantics.Domain.Domain
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])

record SemTy : Set₁ where
  field
    P : Term → Set
    isNf  : ∀{t} → P t → Nf t
    hasNe : ∀{t} → Ne t → P t
open SemTy

_≃_ : SemTy → SemTy → Set
A ≃ B = (a : Term) → (P A a → P B a) × (P B a → P A a)

infix 4 _∈_
record _∈_ (a : Term) (A : SemTy) : Set where
  no-eta-equality
  constructor ∈in
  field
    wit : P A a
open _∈_

hasFree : ∀{A x} → Free x ∈ A
hasFree {A} = ∈in (hasNe A neFree)

hasBound : ∀{A x} → Bound x ∈ A
hasBound {A} = ∈in (hasNe A neBound)

infix 4 ⟦_⟧≃⟦_⟧_∈tm_
record ⟦_⟧≃⟦_⟧_∈tm_ (t t' : Term) (ρ : Subst) (T : SemTy) : Set where
  constructor ⟨_∣_⟩
  field
    {res} : D
    ∈tm : res ∈ T
    ↘tm  : t [ ρ ]↘ res
open ⟦_⟧≃⟦_⟧_∈tm_

record _●_∈ap_ (f a : Term) (B : SemTy) : Set where
  constructor ⟨_∣_⟩
  field
    {res} : Term
    ∈tm   : res ∈ B
    ↘ap  : f ● a ↘ res
open _●_∈ap_

--------------------------------------------------------------------------------

infix 4 _[_,_]
record _[_,_] (F : Term) (w : Wk) (a : Term) (_∈U : D → Set) : Set where
  constructor []ctor
  field
    {Fa} : Term
    ↘s : Eval sub F (Syntax._,_ (Id · w) a) ↘ Fa
    ∈t : Fa ∈U
open _[_,_]

infix 4 _[_,_]∈_
record _[_,_]∈_ (d : D) (w : Wk) (a : D) (T : SemTy) : Set where
  field
    {da} : Term
    ↘s : Eval sub d (Syntax._,_ (Id · w) a) ↘ da
    ∈tm : da ∈ T
open _[_,_]∈_

SemPi : (A : Wk → SemTy) → (∀{a w} → P (A w) a → SemTy) → SemTy
SemPi Aty Bty =
  record { P =
    λ f → Nf f × (∀{a w} → (p : P (Aty w) a) → wk f w ● a ∈ap Bty p)
         ; isNf = proj₁ ; hasNe =
    λ ne → (nfNe ne) ,, λ {_} {w} aa →
      let apne = inj-neApp (neWkLemma ne) (isNf (Aty w) aa)
      in record { ∈tm = ∈in (hasNe (Bty aa) apne) ; ↘ap = ●Ne apne } }

wkSemTy : (A B : Wk → SemTy) → ∀{a w} → P (A w) a → SemTy
wkSemTy A B {a} {w} _ = B w -- (Up Id ·ʷ w)

--------------------------------------------------------------------------------
-- Semantic universe of small types

mutual

  _[_,_]∈𝒰 : Term → Wk → Term → Set
  F [ w , a ]∈𝒰 = _[_,_] F w a _∈𝒰

  data _∈𝒰 : Term → Set where
    uPi  : ∀{A B} → Nf B
         → (pA : ∀ w → wk A w ∈𝒰)
         → (∀{a w} → P (El𝒰 (pA w)) a → B [ w , a ]∈𝒰)
         → Π A B ∈𝒰
    uNe  : ∀{t} → Ne t → t ∈𝒰

  El𝒰 : ∀{T} → T ∈𝒰 → SemTy
  El𝒰 (uPi _ Ah Bh) = SemPi (λ w → El𝒰 (Ah w)) λ x → El𝒰 (∈t (Bh x))
  El𝒰 (uNe x) = record { P = Ne ; isNf = nfNe ; hasNe = λ e → e }

≡𝒰 : ∀{A B} → A ∈𝒰 → A ≡ B → B ∈𝒰
≡𝒰 p refl = p

data Ne𝒰View : ∀{d} → d ∈𝒰 → Set where
  neV : ∀{t} → (ne : Ne t) → Ne𝒰View (uNe ne)

ne𝒰View : ∀{d} → Ne d → (p : d ∈𝒰) → Ne𝒰View p
ne𝒰View () (uPi _ p x)
ne𝒰View ne (uNe x) = neV x

𝒰Nf : ∀{t} → t ∈𝒰 → Nf t
𝒰Nf (uPi {A} nfB p h) = nfPi (𝒰Nf (≡𝒰 (p Id) (id-wk 0 A))) nfB
𝒰Nf (uNe x) = nfNe x

--------------------------------------------------------------------------------
-- Semantic universe of types

mutual

  _[_,_]∈𝒯 : Term → Wk → Term → Set
  F [ w , a ]∈𝒯 = _[_,_] F w a _∈𝒯

  data _∈𝒯 : Term → Set where
    𝒰⊆𝒯 : ∀{T} → T ∈𝒰 → T ∈𝒯
    tU   : U ∈𝒯
    tPi  : {A B : Term} → Nf B
         → (pA : ∀ w → wk A w ∈𝒯)
         → (∀{a w} → P (El𝒯 (pA w)) a → B [ w , a ]∈𝒯)
         → Π A B ∈𝒯

  El𝒯 : ∀{T} → T ∈𝒯 →  SemTy
  El𝒯 (𝒰⊆𝒯 x) = El𝒰 x
  El𝒯 (tPi _ Ah Bh) = SemPi (λ w → El𝒯 (Ah w)) (λ x → El𝒯 (∈t (Bh x)))
  El𝒯 tU = record { P = _∈𝒰 ; isNf = 𝒰Nf ; hasNe = uNe }

≡𝒯 : ∀{A B} → A ∈𝒯 → A ≡ B → B ∈𝒯
≡𝒯 p refl = p

𝒯Nf : ∀{A} → A ∈𝒯 → Nf A
𝒯Nf (𝒰⊆𝒯 x) = 𝒰Nf x
𝒯Nf tU = nfU
𝒯Nf (tPi {A} nfB p h) = nfPi (𝒯Nf (≡𝒯 (p Id) (id-wk 0 A))) nfB

record _∈⟦_⟧_ (d : D) (A : Term) (ρ : Subst) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {T} : D
    ev : A [ ρ ]↘ T
    inT : T ∈𝒯
    nn : d ∈ El𝒯 inT

infix 4 ⟦_⟧≃⟦_⟧_∈𝒰
record ⟦_⟧≃⟦_⟧_∈𝒰 (A B : Term) (ρ : Subst) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {resT} : Term
    ∈ty : resT ∈𝒰
    ↘t1 : A [ ρ ]↘ resT
    ↘t2 : B [ ρ ]↘ resT

infix 4 ⟦_⟧≃⟦_⟧_∈𝒯
record ⟦_⟧≃⟦_⟧_∈𝒯 (A B : Term) (ρ : Subst) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {resT} : Term
    ∈ty : resT ∈𝒯
    ↘t1 : A [ ρ ]↘ resT
    ↘t2 : B [ ρ ]↘ resT

infix 4 ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
record ⟦_⟧≃⟦_⟧_∈tm⟦_⟧ (t t' : Term) (ρ : Subst) (T : Term) : Set where
  field
    {res resT} : D
    ∈ty : resT ∈𝒯
    ↘ty : T [ ρ ]↘ resT
    ∈tm : res ∈ El𝒯 ∈ty
    ↘tm1 : t [ ρ ]↘ res
    ↘tm2 : t' [ ρ ]↘ res
