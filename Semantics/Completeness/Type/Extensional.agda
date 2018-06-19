module Semantics.Completeness.Type.Extensional where

open import Syntax hiding (_,_)
open import Semantics.Domain.Domain
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Semantics.Completeness.Type.Type

open _●_∈ap_
open _∈_
open SemTy
open _[_,_]

module _ where

  open import Relation.Binary.HeterogeneousEquality

  cong₃' : {A B C D : Set} {x x' : A} {y y' : B} {z z' : C}
         → (f : A → B → C → D)
         → x ≅ x' → y ≅ y' → z ≅ z'
         → f x y z ≅ f x' y' z'
  cong₃' f refl refl refl = refl

  postulate
    funext : {A : Set} {B C : A → Set} {f : (x : A) → B x} {g : (x : A) → C x}
           → ((x : A) → f x ≅ g x) → f ≅ g

    funext' : {A : Set} {B C : A → Set} {f : {x : A} → B x} {g : {x : A} → C x}
            → ((x : A) → f {x} ≅ g {x})
            → _≅_ {_} {∀{x} → B x} f {∀{x} → C x} g

    funext'' : {A B : Set} {C : A → Set} {D : B → Set}
               {f : (x : A) → C x} {g : (x : B) → D x}
             → (A ≅ B → (x : A) (y : B) → x ≅ y → f x ≅ g y) → f ≅ g

    sameEv : ∀{t a b} → a ≅ b → (p : Eval t ↘ a) → (q : Eval t ↘ b) → p ≅ q
    sameAp : ∀{t s a b} → (p : t ● s ↘ a) → (q : t ● s ↘ b) → p ≅ q

  ext-aux1 : ∀{Fa Fa' w a F} {_∈U : D → Set}
        → Fa ≅ Fa'
        → (p : Eval sub F ((Id · w) Subst., a) ↘ Fa)
        → (q : Eval sub F ((Id · w) Subst., a) ↘ Fa')
        → (i : Fa ∈U) → (j : Fa' ∈U)
        → i ≅ j
        → _≅_ {_} {(F [ w , a ]) _∈U} ([]ctor p i)
                  {(F [ w , a ]) _∈U} ([]ctor q j)
  ext-aux1 refl p q i j h = cong₂ []ctor (sameEv refl p q) h

  ext-aux2 : ∀{A B}
      → (nf nf' : Nf B)
      → (h1 h1' : (w : Wk) → wk A w ∈𝒰)
      → nf ≅ nf'
      → h1 ≅ h1'
      → (h2 : ∀{a w} → P (El𝒰 (h1 w)) a → B [ w , a ]∈𝒰)
      → (h2' : ∀{a w} → P (El𝒰 (h1' w)) a → B [ w , a ]∈𝒰)
      → (∀{a w} → (x : P (El𝒰 (h1 w)) a) (y : P (El𝒰 (h1' w)) a) → ∈t (h2 x) ≅ ∈t (h2' y))
      → uPi nf h1 h2 ≅ uPi nf' h1' h2'
  ext-aux2 nf nf' h1 h1' refl eq h2 h2' h = cong₂ (uPi nf) eq
    (funext' (λ a → funext' (λ w → funext'' (λ x x₁ y x₂ →
      ext-aux1 (≡-to-≅ (Eval-fun (↘s (h2 x₁)) (↘s (h2' y))))
        (↘s (h2 x₁)) (↘s (h2' y)) (∈t (h2 x₁)) (∈t (h2' y)) (h x₁ y)))))

  samey : ∀{A B} → A ≅ B → (p : A ∈𝒰) (q : B ∈𝒰) → p ≅ q
  samey refl (uPi {A} {B} nf h1 h2) (uPi nf' h1' h2') =
    ext-aux2 nf nf' h1 h1' eqnf eq h2 h2' λ x y →
      samey (≡-to-≅ (Eval-fun (↘s (h2 x)) (↘s (h2' y)))) (∈t (h2 x)) (∈t (h2' y))
    where
      eq : h1 ≅ h1'
      eq = funext (λ w → samey refl (h1 w) (h1' w))
      eqnf : nf ≅ nf'
      eqnf = ≡-to-≅ (sameNf nf nf')
  samey refl (uPi x pA x₁) (uNe ())
  samey refl (uNe ()) (uPi x₁ pA x₂)
  samey refl (uNe x) (uNe y) = cong uNe (≡-to-≅ (sameNe x y))

  kekek' : ∀{A B t res res' a}
         → res ≅ res'
         → A ≅ B
         → (tm : P A res) (tm' : P B res')
         → tm ≅ tm'
         → (e : t ● a ↘ res) (e' : t ● a ↘ res')
         → e ≅ e'
         → _≅_ {_} {t ● a ∈ap A} ⟨ ∈in tm ∣ e ⟩ {t ● a ∈ap B} ⟨ ∈in tm' ∣ e' ⟩
  kekek' refl refl tm tm' eq'' e e' eq''' = cong₂ _●_∈ap_.⟨_∣_⟩ (cong ∈in eq'') eq'''

  kekek : ∀{A B t a} → (p : t ● a ∈ap A) → (q : t ● a ∈ap B)
        → wit (∈tm p) ≅ wit (∈tm q) → A ≅ B → p ≅ q
  kekek ⟨ ∈in tm ∣ ap ⟩ ⟨ ∈in tm' ∣ ap' ⟩ h h' =
    kekek' (≡-to-≅ (●-fun ap ap')) h' tm tm' h ap ap' (sameAp ap ap')

  gaa : ∀{A B t a w}
      → (Ah : (w : Wk) → wk A w ∈𝒰)
      → (Bh : ∀{a} {w} → P (El𝒰 (Ah w)) a → B [ w , a ]∈𝒰)
      → (p : P (El𝒰 (Ah w)) a) (p' : P (El𝒰 (Ah w)) a)
      → (x : wk t w ● a ∈ap El𝒰 (∈t (Bh p)))
      → (y : wk t w ● a ∈ap El𝒰 (∈t (Bh p')))
      → wit (∈tm x) ≅ wit (∈tm y)
      → El𝒰 (∈t (Bh p)) ≅ El𝒰 (∈t (Bh p'))
      → x ≅ y
  gaa Ah Bh p p' x y h h' = kekek x y h h'

  ddd : ∀{A B} → A ≅ B → (p : A ∈𝒰) (q : B ∈𝒰) → p ≅ q → El𝒰 p ≅ El𝒰 q
  ddd refl p .p refl = refl

  samey' : ∀{A B a b} → A ≅ B → a ≅ b → (p : A ∈𝒰) (q : B ∈𝒰) → p ≅ q
         → (x : P (El𝒰 p) a) → (y : P (El𝒰 q) b) → x ≅ y
  samey' refl refl (uPi _ Ah Bh) _ refl (nf ,, h) (nf' ,, h') =
    cong₂ _,,_ (≡-to-≅ (sameNf nf nf')) (funext' (λ a → funext' (λ w →
      funext'' (λ peq p p' peq' →
        let eq = (≡-to-≅ (Eval-fun (↘s (Bh p)) (↘s (Bh p'))))
            sam = (samey eq (∈t (Bh p)) (∈t (Bh p')))
            ttt = ddd eq ((∈t (Bh p))) ((∈t (Bh p'))) sam
        in gaa Ah Bh p p' (h p) (h' p')
          (samey' {Fa (Bh p)} {Fa (Bh p')} {res (h p)} {res (h' p')}
            eq (≡-to-≅ (●-fun (↘ap (h p)) (↘ap (h' p')))) (∈t (Bh p)) (∈t (Bh p'))
            sam (wit (∈tm (h p))) (wit (∈tm (h' p')))) ttt))))
  samey' refl refl (uNe x₁) _ refl x y = ≡-to-≅ (sameNe x y)

  get≡ = ≅-to-≡
  refl≅ : {A : Set} → {a : A} → a ≅ a
  refl≅ = refl

open import Relation.Binary.PropositionalEquality

-- TEMPORARY
-- TO BE REPLACED WITH PROOFS IN LOCAL BRANCH THAT DO NOT USE FUNEXT

samey𝒰 : ∀{A} → (p q : A ∈𝒰) → p ≡ q
samey𝒰 p q = get≡ (samey refl≅ p q)

sameyP𝒰 : ∀{A a} → (ty ty' : A ∈𝒰) → ty ≡ ty'
        → (x y : P (El𝒰 ty) a) → x ≡ y
sameyP𝒰 ty .ty refl x y = get≡ (samey' refl≅ refl≅ ty ty refl≅ x y)

sameTerm≃ : ∀{A B} → A ≡ B → (p : A ∈𝒰) (q : B ∈𝒰) → ∀ a → P (El𝒰 p) a → P (El𝒰 q) a
sameTerm≃ refl p q a x = subst (λ x → P (El𝒰 x) a) (samey𝒰 p q) x

postulate
  sameTerm𝒯≃ : ∀{A B a} → A ≡ B → (p : A ∈𝒯) (q : B ∈𝒯) → P (El𝒯 p) a → P (El𝒯 q) a

  samey𝒯 : ∀{A} → (p q : A ∈𝒯) → p ≡ q
  sameyP𝒯 : ∀{A a} → (ty ty' : A ∈𝒯) → ty ≡ ty' → (x y : P (El𝒯 ty) a) → x ≡ y


sameTerm≃' : ∀{A B a b} → A ≡ B → a ≡ b
           → (p : A ∈𝒯) (q : B ∈𝒯) → P (El𝒯 p) a → P (El𝒯 q) b
sameTerm≃' refl refl p q h = sameTerm𝒯≃ refl p q h
