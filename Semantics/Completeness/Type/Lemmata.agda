module Semantics.Completeness.Type.Lemmata where

open import Function
open import Syntax
open import Semantics.Domain.Domain
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Semantics.Completeness.Type.Type
open import Semantics.Completeness.Type.Extensional
open import Semantics.Completeness.Type.UniverseProperties
open import Data.Sum
open import Function

open SemTy
open _∈_
open _[_,_]
open _●_∈ap_
open ⟦_⟧≃⟦_⟧_∈tm_
open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒰
open ⟦_⟧≃⟦_⟧_∈𝒯

sameT : ∀{A B} → A ≡ B → (p : A ∈𝒯) → (q : B ∈𝒯)
      → ∀{a} → P (El𝒯 p) a → P (El𝒯 q) a
sameT eq p q x = sameTerm𝒯≃ eq p q x

same∈tm : ∀{A B t s ρ} → A ≡ B → (p : A ∈𝒯) (q : B ∈𝒯)
        → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm El𝒯 p → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm El𝒯 q
same∈tm refl p q ⟨ tm ∣ e ⟩ = ⟨ ∈in (sameTerm𝒯≃ refl p q (wit tm)) ∣ e ⟩

eq-sub' : ∀{σ τ t s} → t ≡ s → σ ≈ˢ τ → sub t σ ≡ sub s τ
eq-sub' {t = t} refl eq = ≈ˢsub eq t

beeh : ∀{A w A' ρ a} → A [ ρ ]↘ A'
     → (p : A' ∈𝒯) → P (El𝒯 (wk𝒯 p w)) a → a ∈⟦ A ⟧ (ρ · w)
beeh {A} {w} eA p pa = ⟨ ≡Eval (wk-subst A) refl (wkEval eA) ∣ wk𝒯 p w ∣ ∈in pa ⟩

∈𝒯Right : ∀{A B ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯 → ⟦ B ⟧≃⟦ B ⟧ ρ ∈𝒯
∈𝒯Right ⟨ ty ∣ e1 ∣ e2 ⟩ = ⟨ ty ∣ e2 ∣ e2 ⟩

∈𝒯Left : ∀{A B ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯 → ⟦ A ⟧≃⟦ A ⟧ ρ ∈𝒯
∈𝒯Left ⟨ ty ∣ t1 ∣ t2 ⟩ = ⟨ ty ∣ t1 ∣ t1 ⟩

∈tmLeft : ∀{A t s ρ} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ t ⟧≃⟦ t ⟧ ρ ∈tm⟦ A ⟧
∈tmLeft record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm ; ↘tm1 = e1 ; ↘tm2 = e2 } =
  record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm ; ↘tm1 = e1 ; ↘tm2 = e1 }

coerceLemma : ∀{ρ t s A B} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯
            → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ B ⟧
coerceLemma {ρ} ih1 ih2 =
  record
    { ∈ty = ∈ty ih2 ; ↘ty = ↘t2 ih2 ; ↘tm1 = ↘tm1 ih1 ; ↘tm2 = ↘tm2 ih1
    ; ∈tm = ∈in (sameT (Eval-fun (↘ty ih1) (↘t1 ih2))
                (∈ty ih1) (∈ty ih2) (wit (∈tm ih1)))
    }

tySymm : ∀{A B ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯 → ⟦ B ⟧≃⟦ A ⟧ ρ ∈𝒯
tySymm ⟨ ty ∣ t1 ∣ t2 ⟩ = ⟨ ty ∣ t2 ∣ t1 ⟩

tyTrans : ∀{A B C ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯 → ⟦ B ⟧≃⟦ C ⟧ ρ ∈𝒯 → ⟦ A ⟧≃⟦ C ⟧ ρ ∈𝒯
tyTrans ⟨ ty ∣ t1 ∣ t2 ⟩ ⟨ ty' ∣ t1' ∣ t2' ⟩ =
  ⟨ ty ∣ t1 ∣ ≡Eval refl (Eval-fun t1' t2) t2' ⟩

tmSymm : ∀{t s ρ A} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ s ⟧≃⟦ t ⟧ ρ ∈tm⟦ A ⟧
tmSymm record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm ; ↘tm1 = e1 ; ↘tm2 = e2 } =
  record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm ; ↘tm1 = e2 ; ↘tm2 = e1 }

tmTrans : ∀{t s r ρ A} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ s ⟧≃⟦ r ⟧ ρ ∈tm⟦ A ⟧
        → ⟦ t ⟧≃⟦ r ⟧ ρ ∈tm⟦ A ⟧
tmTrans ih ih' =
  record { ∈ty = ∈ty ih ; ↘ty = ↘ty ih ; ∈tm = ∈tm ih ; ↘tm1 = ↘tm1 ih
         ; ↘tm2 = ≡Eval refl (Eval-fun (↘tm1 ih') (↘tm2 ih)) (↘tm2 ih') }

invert-ty : ∀{t s A ρ} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ A ⟧≃⟦ A ⟧ ρ ∈𝒯
invert-ty record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm ; ↘tm1 = e1 ; ↘tm2 = e2 } =
  ⟨ ty ∣ ety ∣ ety ⟩

argty : ∀{ρ t s A B}
      → (∀{a w} → a ∈⟦ A ⟧ (ρ · w) → ⟦ t ⟧≃⟦ s ⟧ (ρ · w , a) ∈tm⟦ B ⟧)
      → ∀{a w} → a ∈⟦ A ⟧ (ρ · w) → ⟦ B ⟧≃⟦ B ⟧ (ρ · w , a) ∈𝒯
argty h aa = record { ∈ty = ∈ty (h aa) ; ↘t1 = ↘ty (h aa) ; ↘t2 = ↘ty (h aa) }

≡∈𝒯 : ∀{A B} → A ≡ B → A ∈𝒯 → B ∈𝒯
≡∈𝒯 refl x = x

UtoT : ∀{A B ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈tm⟦ U ⟧ → ⟦ A ⟧≃⟦ B ⟧ ρ ∈𝒯
UtoT record { ∈ty = (𝒰⊆𝒯 (uNe ())) ; ↘ty = eU }
UtoT record { ∈ty = tU ; ↘ty = eU ; ∈tm = tm ; ↘tm1 = e1 ; ↘tm2 = e2 } =
  ⟨ 𝒰⊆𝒯 (wit tm) ∣ e1 ∣ e2 ⟩

--------------------------------------------------------------------------------


record ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈_∣_ (A B A' B' : Term) (ρ : Subst)
    (_∈U : Term → Set) (El : ∀{A} → A ∈U → SemTy) : Set where
  field
    {resA resB} : D
    ev1 : Π A B [ ρ ]↘ Π resA resB
    ev2 : Π A' B' [ ρ ]↘ Π resA resB
    hypA : (w : Wk) → wk resA w ∈U
    hypB : ∀{a w} → P (El (hypA w)) a → _[_,_] resB w a _∈U
    nfresA : Nf resA
    nfresB : Nf resB

asdeur : ∀{ρ A B} → ⟦ Π A B ⟧≃⟦ Π A B ⟧ ρ ∈tm⟦ U ⟧
       → ⟦Π A ∣ B ⟧≃⟦Π A ∣ B ⟧ ρ ∈ _∈𝒰 ∣ El𝒰
asdeur record { ∈ty = (𝒰⊆𝒯 (uNe ())) ; ↘ty = eU }
asdeur record
         { ∈ty = tU ; ↘ty = eU ; ∈tm = (∈in (uPi nfB Ah Bh))
         ; ↘tm1 = (ePi tm1 tm2) ; ↘tm2 = (ePi tm3 tm4) } =
       record { ev1 = ePi tm1 tm2 ; ev2 = ePi tm3 tm4
         ; hypA = Ah ; hypB = Bh ; nfresA = nfEval tm1 ; nfresB = nfB }
asdeur record { ∈ty = tU ; ↘ty = eU ; ∈tm = (∈in (uNe ()))
       ; ↘tm1 = (ePi tm1 tm2) ; ↘tm2 = (ePi tm3 tm4) }

record ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯 (A B A' B' : Term) (ρ : Subst) : Set where
  field
    {resA resB} : D
    ev1 : Π A B [ ρ ]↘ Π resA resB
    ev2 : Π A' B' [ ρ ]↘ Π resA resB
    Ah : (w : Wk) → wk resA w ∈𝒯
    hyp : ∀{a w} → P (El𝒯 (Ah w)) a → resB [ w , a ]∈𝒯
    nfA : Nf resA
    nfB : Nf resB

asder : ∀{ρ A B} → ⟦ Π A B ⟧≃⟦ Π A B ⟧ ρ ∈𝒯 → ⟦Π A ∣ B ⟧≃⟦Π A ∣ B ⟧ ρ ∈𝒯
asder ⟨ tPi _ h1 h2 ∣ ePi e1 e2 ∣ ePi e3 e4 ⟩ =
  record { ev1 = ePi e1 e2 ; ev2 = ePi e3 e4 ; Ah = h1 ; hyp = h2
         ; nfA = nfEval e3 ; nfB = nfEval e4 }
asder ⟨ 𝒰⊆𝒯 (uPi _ h1 h2) ∣ ePi e1 e2 ∣ ePi e3 e4 ⟩ =
  record { ev1 = ePi e1 e2 ; ev2 = ePi e3 e4 ; Ah = 𝒰⊆𝒯 ∘ h1
    ; hyp = λ {a} {w} x → record { ↘s = ↘s (h2 x) ; ∈t = 𝒰⊆𝒯 (∈t (h2 x)) }
    ; nfA = nfEval e3 ; nfB = nfEval e4 }
asder ⟨ 𝒰⊆𝒯 (uNe ()) ∣ ePi e1 e2 ∣ ePi e3 e4 ⟩

Codom : ∀{A} → Term → ((w : Wk) → wk A w ∈𝒯) → Set
Codom B Ah = ∀{a w} → P (El𝒯 (Ah w)) a → B [ w , a ]∈𝒯

bound0 : ∀{A A' ρ} → A [ ρ ]↘ A' → A' ∈𝒯 → Bound 0 ∈⟦ A ⟧ (ρ · Up Id)
bound0 {A} e ty = beeh e ty (hasNe (El𝒯 (wk𝒯 ty _)) neBound)

asder2 : ∀{A B} → Π A B ∈𝒯 → Σ ((w : Wk) → wk A w ∈𝒯) (Codom B)
asder2 (𝒰⊆𝒯 (uNe ()))
asder2 (𝒰⊆𝒯 (uPi _ h1 h2)) = (𝒰⊆𝒯 ∘ h1) ,, λ x →
  record { ↘s = ↘s (h2 x) ; ∈t = 𝒰⊆𝒯 (∈t (h2 x)) }
asder2 (tPi _ h1 h2) = h1 ,, λ x → h2 x

tmSubLemma : ∀{t ρ t' s s' d}
           → t [ sh ρ ]↘ t' → s [ ρ ]↘ s' → t' [ Id , s' ]↘ d
           → sub t (Id , s) [ ρ ]↘ d
tmSubLemma {t} {ρ} {t'} {s} {s'} {d} e1 e3 sb =
  ≡Eval (trans (sub-comp t) (sym (trans (sub-comp t)
    (≈ˢsub (≈ˢtrans (sub-comp-R {s}) (≈ˢcons (≈ˢtrans sub-id-L
      (≈ˢsym sub-id-R)))) t)))) refl uhmm
  where uhmm = sub-comm2 {sub t (sh ρ)} 0 (sub-unswap e1 sb) e3

subTyLemma : ∀{ρ A B s}
           → ⟦ A ⟧≃⟦ A ⟧ ρ ∈𝒯
           → ⟦ Π A B ⟧≃⟦ Π A B ⟧ ρ ∈𝒯
           → ⟦ s ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧
           → ⟦ sub B (Id , s) ⟧≃⟦ sub B (Id , s) ⟧ ρ ∈𝒯
subTyLemma tyA pi ihs with asder pi
subTyLemma {ρ} {_} {B} tyA pi ihs |
  record { resB = Bd ; ev1 = ePi e1 e2 ; ev2 = ePi e3 e4 ; Ah = Ah ; hyp = Bh } =
    ⟨ ∈t h ∣ e ∣ e ⟩
  where
    h = Bh (sameT (trans (Eval-fun (↘ty ihs) e1) (sym (id-wk 0 _)))
          (∈ty ihs) (Ah Id) (wit (∈tm ihs)))
    e = tmSubLemma {B} e2 (↘tm1 ihs) (≡Eval (≈ˢsub (≈ˢcons sub-id-R) Bd) refl (↘s h))
