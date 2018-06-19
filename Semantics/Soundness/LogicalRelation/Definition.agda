module Semantics.Soundness.LogicalRelation.Definition where

open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Data.Product renaming (_,_ to _,,_)
open import Semantics.Completeness.Type.Properties.LambdaLemma
open import Relation.Binary.PropositionalEquality

_[_,_]ₛ : Term → Wk → Term → Term
t [ w , a ]ₛ = sub t (Id · w , a)

open _[_,_]
open SemTy
open _●_∈ap_
open _∈_
open _[_,_]∈_

el : ∀{a A} {ty : SemTy} → P ty a → Term
el {_} {a} _ = a

neEl : ∀{t} → Ne t → Term
neEl {t} _ = t

the𝒰 : ∀{A} → A ∈𝒰 → Term
the𝒰 {A} _ = A

data PiRel𝒰 (Θ : Ctxtₗ) (A B : D)
     (RA : Ctxt → Term → Set)
     (Ah : (w : Wk) → wk A w ∈𝒰)
     (RAt : ∀{a w} → Ctxt → Term → Term → P (El𝒰 (Ah w)) a → Set)
     (RB : ∀{a w} → Ctxt → Term → P (El𝒰 (Ah w)) a → Set)
     : Ctxt → Term → Set where
  ®𝒰Π : ∀{Γ R S T} → Θ ∷ Γ ⊢ R ∼ Π S T → RA Γ S
      → (∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Γ → (p : P (El𝒰 (Ah w)) a)
        → RAt Γ' s (wk S w) p
        → RB Γ' (T [ w , s ]ₛ) p)
      → PiRel𝒰 Θ A B RA Ah RAt RB Γ R

data PiRel (Θ : Ctxtₗ) (A B : D)
     (RA : Ctxt → Term → Set)
     (Ah : (w : Wk) → wk A w ∈𝒯)
     (RAt : ∀{a w} → Ctxt → Term → Term → P (El𝒯 (Ah w)) a → Set)
     (RB : ∀{a w} → Ctxt → Term → P (El𝒯 (Ah w)) a → Set)
     : Ctxt → Term → Set where
  ®𝒯Π : ∀{Γ R S T} → Θ ∷ Γ ⊢ R ∼ Π S T → RA Γ S
      → (∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Γ → (p : P (El𝒯 (Ah w)) a)
        → RAt Γ' s (wk S w) p
        → RB Γ' (T [ w , s ]ₛ) p)
      → PiRel Θ A B RA Ah RAt RB Γ R

data LamRel𝒰 (Θ : Ctxtₗ) (A B : D)
     (RA : Ctxt → Term → Set)
     (nfB : Nf B)
     (Ah : (w : Wk) → wk A w ∈𝒰)
     (RB : ∀{a w} → Ctxt → Term → P (El𝒰 (Ah w)) a → Set) -- new
     (Bh : ∀{a w} → P (El𝒰 (Ah w)) a → B [ w , a ]∈𝒰)
     (RAt : ∀{a w} → Ctxt → Term → Term → P (El𝒰 (Ah w)) a → Set)
     (RBt' : ∀{a w d}
       → (qh : ∀{a w} → (pa : P (El𝒰 (Ah w)) a) → d [ w , a ]∈ El𝒰 (∈t (Bh pa)))
       → Ctxt → Term → Term → (p : P (El𝒰 (Ah w)) a)
       → P (El𝒰 (∈t (Bh p))) (da (qh p)) → Set)
     : Ctxt → Term → Term → (f : D) → (ty : Π A B ∈𝒰) → P (El𝒰 ty) f → Set where
-- : Ctxt → Term → Term → (f : D) → P (El𝒰 (uPi nfB Ah Bh)) f → Set where
  ®𝒰λ : ∀{Γ r t d R S T} -- {nfA : Nf A} {nfd : Nf d}
      → (qh : ∀{a w} → (pa : P (El𝒰 (Ah w)) a) → d [ w , a ]∈ El𝒰 (∈t (Bh pa)))
      -> (ty : Π A B ∈𝒰)
      -> (proof : P (El𝒰 ty) (Lam A d))
      → Θ ∷ Γ ⊢ R ∼ Π S T → RA Γ S
      → Θ ∷ Γ ⊢ r ∼ Lam S t ∶ R
      → (∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Γ → (p : P (El𝒰 (Ah w)) a)
        → RAt Γ' s (wk S w) p
        → RBt' qh Γ' (t [ w , s ]ₛ) (T [ w , s ]ₛ) p (wit (∈tm (qh p))))
      → LamRel𝒰 Θ A B RA nfB Ah RB Bh RAt RBt' Γ r R (Lam A d) ty proof
          -- (uhm' nfA nfB nfd Ah Bh qh refl)
  ®𝒰Ne : ∀{Γ r R e} {ty : Π A B ∈𝒰} {q : P (El𝒰 ty) e}
       → Ne e → Θ ∷ Γ ⊢ r ∼ e ∶ R
       → Θ ∷ Γ ⊢ R ∼ Π A B
       → LamRel𝒰 Θ A B RA nfB Ah RB Bh RAt RBt' Γ r R e ty q

data LamRel (Θ : Ctxtₗ) (A B : D)
     (RA : Ctxt → Term → Set)
     (nfA : Nf A)
     (nfB : Nf B)
     (Ah : (w : Wk) → wk A w ∈𝒯)
     (RB : ∀{a w} → Ctxt → Term → P (El𝒯 (Ah w)) a → Set) -- new
     (Bh : ∀{a w} → P (El𝒯 (Ah w)) a → B [ w , a ]∈𝒯)
     (RAt : ∀{a w} → Ctxt → Term → Term → P (El𝒯 (Ah w)) a → Set)
     (RBt : ∀{a w d}
       → (qh : ∀{a w} → (pa : P (El𝒯 (Ah w)) a) → d [ w , a ]∈ El𝒯 (∈t (Bh pa)))
       → Ctxt → Term → Term → (p : P (El𝒯 (Ah w)) a)
         → P (El𝒯 (∈t (Bh p))) (da (qh p)) → Set)

     : Ctxt → Term → Term → (f : D) (ty : Π A B ∈𝒯) → P (El𝒯 ty) f → Set where
-- : Ctxt → Term → Term → (f : D) → P (El𝒯 (tPi nfB Ah Bh)) f → Set where
  ®𝒯λ : ∀{Γ r t d R S T} -- {nfd : Nf d}
      → (qh : ∀{a w} → (pa : P (El𝒯 (Ah w)) a) → d [ w , a ]∈ El𝒯 (∈t (Bh pa)))
      → (ty : Π A B ∈𝒯)
      → (proof : P (El𝒯 ty) (Lam A d))
      → Θ ∷ Γ ⊢ R ∼ Π S T → RA Γ S
      → Θ ∷ Γ ⊢ r ∼ Lam S t ∶ R
      → (∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Γ → (p : P (El𝒯 (Ah w)) a)
        → RAt Γ' s (wk S w) p
        → RBt qh Γ' (t [ w , s ]ₛ) (T [ w , s ]ₛ) p (wit (∈tm (qh p))))
      → LamRel Θ A B RA nfA nfB Ah RB Bh RAt RBt Γ r R (Lam A d) ty proof
          -- (uhm'' nfA nfB nfd Ah Bh qh refl)
  ®𝒯Ne : ∀{Γ r R e} {ty : Π A B ∈𝒯} {q : P (El𝒯 ty) e}
       → Ne e
       → Θ ∷ Γ ⊢ r ∼ e ∶ R
       → Θ ∷ Γ ⊢ R ∼ Π A B
       → LamRel Θ A B RA nfA nfB Ah RB Bh RAt RBt Γ r R e ty q

mutual

  _∷_⊢_®𝒰_ : (Θ : Ctxtₗ) → ∀{A} → Ctxt → Term → A ∈𝒰 → Set
  Θ ∷ Γ ⊢ T ®𝒰 uPi {A} {B} _ Ah Bh =
    PiRel𝒰 Θ A B (λ x y → Θ ∷ x ⊢ y ®𝒰 (Ah Id))
      Ah (λ {_} {w} x x₁ x₂ x₃ → Θ ∷ x ⊢ x₁ ∶ x₂ ®𝒰 Ah w ∋ x₃)
      (λ x x₁ x₂ → Θ ∷ x ⊢ x₁ ®𝒰 ∈t (Bh x₂)) Γ T
  Θ ∷ Γ ⊢ T ®𝒰 uNe x = Θ ∷ Γ ⊢ T ∼ neEl x

  _∷_⊢_®_ : (Θ : Ctxtₗ) → ∀{A} → Ctxt → Term → A ∈𝒯 → Set
  Θ ∷ Γ ⊢ T ® 𝒰⊆𝒯 x = Θ ∷ Γ ⊢ T ®𝒰 x
  Θ ∷ Γ ⊢ T ® tU = Θ ∷ Γ ⊢ T ∼ U
  Θ ∷ Γ ⊢ T ® tPi {A} {B} _ Ah Bh =
    PiRel Θ A B (λ x y → Θ ∷ x ⊢ y ® (Ah Id))
      Ah (λ {_} {w} x x₁ x₂ x₃ → Θ ∷ x ⊢ x₁ ∶ x₂ ® Ah w ∋ x₃)
      (λ x x₁ x₂ → Θ ∷ x ⊢ x₁ ® ∈t (Bh x₂)) Γ T

  _∷_⊢_∶_®𝒰_∋_ : (Θ : Ctxtₗ) → ∀{A a} → Ctxt → Term → Term
               → (ty : A ∈𝒰) → P (El𝒰 ty) a → Set
  Θ ∷ Γ ⊢ t ∶ T ®𝒰 uPi {A} {B} nfB Ah Bh ∋ a =
    LamRel𝒰 Θ A B (λ x x₁ → Θ ∷ x ⊢ x₁ ®𝒰 (Ah Id)) nfB Ah
      (λ x x₁ x₂ → Θ ∷ x ⊢ x₁ ®𝒰 ∈t (Bh x₂)) Bh
      (λ {_} {w} x x₁ x₂ x₃ → Θ ∷ x ⊢ x₁ ∶ x₂ ®𝒰 Ah w ∋ x₃)
      (λ qh Γ' t[] T[] p q → Θ ∷ Γ' ⊢ t[] ∶ T[] ®𝒰 ∈t (Bh p) ∋ q)
      Γ t T _ (uPi nfB Ah Bh) a
  Θ ∷ Γ ⊢ t ∶ T ®𝒰 uNe x ∋ a = (Θ ∷ Γ ⊢ T ∼ neEl x) × (Θ ∷ Γ ⊢ t ∼ neEl a ∶ T)

  _∷_⊢_∶_®_∋_ : ∀{a A} → Ctxtₗ → Ctxt → Term → Term
              → (ty : A ∈𝒯) → P (El𝒯 ty) a → Set
  Θ ∷ Γ ⊢ t ∶ T ® 𝒰⊆𝒯 x ∋ a = Θ ∷ Γ ⊢ t ∶ T ®𝒰 x ∋ a
  Θ ∷ Γ ⊢ t ∶ T ® tU ∋ a =
    (Θ ∷ Γ ⊢ T ∼ U) × (Θ ∷ Γ ⊢ t ®𝒰 a) × (Θ ∷ Γ ⊢ t ∼ the𝒰 a ∶ U)
  Θ ∷ Γ ⊢ t ∶ T ® tPi {A} {B} nfB Ah Bh ∋ a =
    LamRel Θ A B (λ x x₁ → Θ ∷ x ⊢ x₁ ® (Ah Id)) (𝒯Nf (∈𝒯Id Ah)) nfB Ah
      (λ x x₁ x₂ → Θ ∷ x ⊢ x₁ ® ∈t (Bh x₂)) Bh
      (λ {_} {w} x x₁ x₂ x₃ → Θ ∷ x ⊢ x₁ ∶ x₂ ® Ah w ∋ x₃)
      (λ q x x₁ x₂ p x₃ → Θ ∷ x ⊢ x₁ ∶ x₂ ® ∈t (Bh p) ∋ x₃)
      Γ t T _ (tPi nfB Ah Bh) a

open import Syntax.Typed.EqLemma

der𝒰ₜ : ∀{Θ Γ A X t a} {ty : X ∈𝒰} {p : P (El𝒰 ty) a}
      → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ p → Θ ∷ Γ ⊢ t ∶ A
der𝒰ₜ {ty = uPi x pA x₁} (®𝒰λ _ _ _ _ _ x₅ _) = eq-lemma-tm1 x₅
der𝒰ₜ {ty = uPi x pA x₁} (®𝒰Ne x₂ x₃ k) = eq-lemma-tm1 x₃
der𝒰ₜ {ty = uNe x} (_ ,, y) = eq-lemma-tm1 y

der-ty𝒰ₜ : ∀{Θ Γ A X} {ty : X ∈𝒰} → Θ ∷ Γ ⊢ A ®𝒰 ty → Θ ∷ Γ ⊢ A
der-ty𝒰ₜ {ty = uPi x pA x₁} (®𝒰Π x₂ x₃ x₄) = eq-lemma-ty1 x₂
der-ty𝒰ₜ {ty = uNe x} rel = eq-lemma-ty1 rel

der-tyₜ : ∀{Θ Γ A X} {ty : X ∈𝒯} → Θ ∷ Γ ⊢ A ® ty → Θ ∷ Γ ⊢ A
der-tyₜ {ty = 𝒰⊆𝒯 x} rel = der-ty𝒰ₜ rel
der-tyₜ {ty = tU} rel = eq-lemma-ty1 rel
der-tyₜ {ty = tPi x pA x₁} (®𝒯Π x₂ x₃ x₄) = eq-lemma-ty1 x₂

derₜ : ∀{Θ Γ A X t a} {ty : X ∈𝒯} {p : P (El𝒯 ty) a}
     → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ p → Θ ∷ Γ ⊢ t ∶ A
derₜ {ty = 𝒰⊆𝒯 x} rel = der𝒰ₜ rel
derₜ {ty = tU} (eq ,, _ ,, x) = coe (eq-lemma-tm1 x) (∼symm eq)
derₜ {ty = tPi x pA x₁} (®𝒯λ qh _ _ x₂ x₃ x₄ x₅) = eq-lemma-tm1 x₄
derₜ {ty = tPi x pA x₁} (®𝒯Ne x₂ x₃ x₄) = eq-lemma-tm1 x₃

allNe𝒰 : ∀{Θ Γ A X t e} → (ty : X ∈𝒰) → (ne : Ne e)
       → Θ ∷ Γ ⊢ A ∼ X
       → Θ ∷ Γ ⊢ t ∼ e ∶ A → Θ ∷ Γ ⊢ t ∶ A ®𝒰 ty ∋ hasNe (El𝒰 ty) ne
allNe𝒰 (uPi x pA x₁) ne eq eq' = ®𝒰Ne ne eq' eq
allNe𝒰 (uNe x) ne eq eq' = eq ,, eq'

allNe𝒯 : ∀{Θ Γ A X t e} → (ty : X ∈𝒯) → (ne : Ne e)
       → Θ ∷ Γ ⊢ A ∼ X
       → Θ ∷ Γ ⊢ t ∼ e ∶ A → Θ ∷ Γ ⊢ t ∶ A ® ty ∋ hasNe (El𝒯 ty) ne
allNe𝒯 (𝒰⊆𝒯 x) = allNe𝒰 x
allNe𝒯 tU ne eq eq' = eq ,, ∼El (∼coe eq' eq) ,, ∼coe eq' eq
allNe𝒯 (tPi x pA x₁) ne eq eq' = ®𝒯Ne ne eq' eq
