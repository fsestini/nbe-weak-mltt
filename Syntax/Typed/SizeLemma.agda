module Syntax.Typed.SizeLemma where

open import Function
open import Syntax.Raw
open import Syntax.Typed.Context
open import Syntax.Typed.Typed
open import Syntax.Typed.Inversion
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Data.Unit
open import Size
open import Relation.Binary.PropositionalEquality

open import Syntax.Typed.Model

private
  ⊧⊧_ : Ctxtₗ → Set
  ⊧⊧ ◇ = ⊤
  ⊧⊧ (Θ # A) = ⊧⊧ Θ × Tm 0 A

  ⊧_∷_ : Ctxtₗ → Ctxt → Set
  ⊧ Θ ∷ ◇ = ⊧⊧ Θ
  ⊧ Θ ∷ (Γ # A) = ⊧ Θ ∷ Γ × Tm (clen Γ) A

  _∷_⊧_ : Ctxtₗ → Ctxt → Term → Set
  Θ ∷ Γ ⊧ A = Tm (clen Γ) A

  _∷_⊧_∼_ : Ctxtₗ → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ A ∼ B = Tm (clen Γ) A × Tm (clen Γ) B

  _∷_⊧_∶_ : Ctxtₗ → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ t ∶ A = Tm (clen Γ) A × Tm (clen Γ) t

  _∷_⊧_∼_∶_ : Ctxtₗ → Ctxt → Term → Term → Term → Set
  Θ ∷ Γ ⊧ t ∼ s ∶ A = Tm (clen Γ) A × Tm (clen Γ) t × Tm (clen Γ) s

  invert-ctx : ∀{Θ Γ} → ⊧ Θ ∷ Γ → ⊧⊧ Θ
  invert-ctx {Γ = ◇} h = h
  invert-ctx {Γ = Γ # x} h = invert-ctx {Γ = Γ} (p1 h)

  point-at : ∀{Θ A n} → ⊧⊧ Θ → Θ [ n ]ₗ↦ A → Tm 0 A
  point-at h (here x) = p2 h
  point-at h (there x) = point-at (p1 h) x

  bnd : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → Θ ∷ Γ ⊧ Bound n ∶ A
  bnd h here = tm-wk-lemma _ 0 1 (p2 h) ,, tmVar z≤n
  bnd (h1 ,, h2) (there x) with bnd h1 x
  bnd (h1 ,, h2) (there x) | p ,, q = tm-wk-lemma _ 0 1 p ,, tmVar (pj-tm-var q)

sizeModel : Model
sizeModel = record
  { ⊧⊧_ = ⊧⊧_ ; ⊧_∷_ = ⊧_∷_ ; _∷_⊧_ = _∷_⊧_ ; _∷_⊧_∶_ = _∷_⊧_∶_ ; _∷_⊧_∼_ = _∷_⊧_∼_
  ; _∷_⊧_∼_∶_ = _∷_⊧_∼_∶_ ; M-⊢ₘ◇ = tt ; M-⊢ₘ# = _,,_ ; M-⊢◇ = id ; M-⊢# = _,,_
  ; M-U = const tmU ; M-El = p2 ; M-Π = const tmPi
  ; M-free = λ {Θ} {Γ} _ x y → liftTm _ (point-at (invert-ctx {Γ = Γ} x) y) ,, tmFree
  ; M-bound = bnd ; M-lam = λ x x₁ x₂ → (tmPi x₁ (p1 x₂)) ,, (tmLam x₁ (p2 x₂))
  ; M-app = λ { _ _ (tmPi _ q' ,, q₁) ss _ →
      sub-cover-lemma _ 0 q' (p2 ss) ,, tmApp q₁ (p2 ss) }
  ; M-U-Π = λ _ z z₁ → tmU ,, tmPi (p2 z) (p2 z₁)
  ; M-coe = λ x y → p2 y ,, p2 x
  ; M-∼refl = λ z → z ,, z ; M-∼symm = λ x → p2 x ,, p1 x
  ; M-∼trans = λ x y → p1 x ,, p2 y
  ; M-∼Pi = λ x x₁ x₂ x₃ → tmPi (p1 x₂) (p1 x₃) ,, tmPi (p2 x₂) (p2 x₃)
  ; M-∼El = p2 ; M-∼refl' = λ x → (p1 x) ,, p2 x ,, p2 x
  ; M-∼symm' = λ x → (p1 x) ,, p2 (p2 x) ,, p1 (p2 x)
  ; M-∼trans' = λ x x₁ → (p1 x₁) ,, p1 (p2 x) ,, p2 (p2 x₁)
  ; M-∼coe = λ x x₁ → p2 x₁ ,, p2 x
  ; M-∼β = λ _ _ x ih ih' →
      liftTm _ (sub-cover-lemma 0 0 (p1 ih) (p2 ih')) ,,
      liftTm _ (tmApp (tmLam (p1 ih') (p2 ih)) (p2 ih')) ,,
      liftTm _ (sub-cover-lemma 0 0 (p2 ih) (p2 ih'))
  ; M-∼ξ = λ _ ih ih' →
      tmPi (p1 ih) (p1 ih') ,, tmLam (p1 ih) (p1 (p2 ih')) ,,
                               tmLam (p2 ih) (p2 (p2 ih'))
  ; M-∼compPi = λ _ ih ih' → p1 ih ,, tmPi (p1 (p2 ih)) (p1 (p2 ih')) ,,
                                    tmPi (p2 (p2 ih)) (p2 (p2 ih'))
  ; M-∼compApp = λ _ x x₁ x₂ →
      sub-cover-lemma _ 0 (pj-tm-Π₂ (p1 x)) (p1 (p2 x₁)) ,,
      tmApp (p1 (p2 x)) (p1 (p2 x₁)) ,, tmApp (p2 (p2 x)) (p2 (p2 x₁))
  }

open Modeling sizeModel

ctxLen : ∀{Θ Γ i} → ⊢⟨ i ⟩ Θ ∷ Γ → ⊧ Θ ∷ Γ
ctxLen = model-ctx

tyLen : ∀{Θ Γ A i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A → Θ ∷ Γ ⊧ A
tyLen = model-ty

ₗ↦Len : ∀{Θ A n i} → ⊢⟨ i ⟩ Θ → Θ [ n ]ₗ↦ A → Tm 0 A
ₗ↦Len ctx x = p1 (model-tm (free (⊢◇ ctx) x))

↦Len : ∀{Θ Γ A n i} → ⊢⟨ i ⟩ Θ ∷ Γ → Γ [ n ]↦ A → Tm (clen Γ) A
↦Len ctx x = p1 (model-tm (bound ctx x))

tmLen : ∀{Θ Γ t A i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Γ ⊧ t ∶ A
tmLen = model-tm

ty∼Len : ∀{Θ Γ A B i} → ⟨ i ⟩ Θ ∷ Γ ⊢ A ∼ B → Θ ∷ Γ ⊧ A ∼ B
ty∼Len = model-ty∼

tm∼Len : ∀{Θ Γ A t s i} → ⟨ i ⟩ Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊧ t ∼ s ∶ A
tm∼Len = model-tm∼

mutual

  tySameSzLemmaL : ∀{Θ Γ A B n} → Θ ∷ Γ ⊢ A ∼ B → Tm n A → Tm n B
  tySameSzLemmaL (∼refl x) tm = tm
  tySameSzLemmaL (∼symm eq) tm = tySameSzLemmaR eq tm
  tySameSzLemmaL (∼trans eq eq') tm = tySameSzLemmaL eq' (tySameSzLemmaL eq tm)
  tySameSzLemmaL (∼Pi eq eq') (tmPi tm tm') =
    tmPi (tySameSzLemmaL eq tm) (tySameSzLemmaL eq' tm')
  tySameSzLemmaL (∼El x) tm = tmSameSzLemmaL x tm

  tySameSzLemmaR : ∀{Θ Γ A B n} → Θ ∷ Γ ⊢ A ∼ B → Tm n B → Tm n A
  tySameSzLemmaR (∼refl x) tm = tm
  tySameSzLemmaR (∼symm eq) tm = tySameSzLemmaL eq tm
  tySameSzLemmaR (∼trans eq eq') tm = tySameSzLemmaR eq (tySameSzLemmaR eq' tm)
  tySameSzLemmaR (∼Pi eq eq') (tmPi tm tm') =
    tmPi (tySameSzLemmaR eq tm) (tySameSzLemmaR eq' tm')
  tySameSzLemmaR (∼El x) tm = tmSameSzLemmaR x tm

  tmSameSzLemmaL : ∀{Θ Γ A t s n} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Tm n t → Tm n s
  tmSameSzLemmaL (∼refl x) tm = tm
  tmSameSzLemmaL (∼symm eq) tm = tmSameSzLemmaR eq tm
  tmSameSzLemmaL (∼trans eq eq') tm = tmSameSzLemmaL eq' (tmSameSzLemmaL eq tm)
  tmSameSzLemmaL (∼coe eq x) tm = tmSameSzLemmaL eq tm
  tmSameSzLemmaL (∼β x x₁ x₂) tm =
    liftTm _ (sub-cover-lemma 0 0 (p2 (tmLen x₁)) (p2 (tmLen x₂)))
  tmSameSzLemmaL (∼ξ x eq) (tmLam tm tm') =
    tmLam (tySameSzLemmaL x tm) (tmSameSzLemmaL eq tm')
  tmSameSzLemmaL (∼compPi eq eq') (tmPi tm tm') =
    tmPi (tmSameSzLemmaL eq tm) (tmSameSzLemmaL eq' tm')
  tmSameSzLemmaL (∼compApp eq eq' _) (tmApp tm tm') =
    tmApp (tmSameSzLemmaL eq tm) (tmSameSzLemmaL eq' tm')

  tmSameSzLemmaR : ∀{Θ Γ A t s n} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Tm n s → Tm n t
  tmSameSzLemmaR (∼refl x) tm = tm
  tmSameSzLemmaR (∼symm eq) tm = tmSameSzLemmaL eq tm
  tmSameSzLemmaR (∼trans eq eq') tm = tmSameSzLemmaR eq (tmSameSzLemmaR eq' tm)
  tmSameSzLemmaR (∼coe eq x) tm = tmSameSzLemmaR eq tm
  tmSameSzLemmaR (∼β x x₁ x₂) tm =
    liftTm _ (tmApp (tmLam (p1 (tmLen x₂))
      (p2 (tmLen x₁))) (p2 (tmLen x₂)))
  tmSameSzLemmaR (∼ξ x eq) (tmLam tm tm') =
    tmLam (tySameSzLemmaR x tm) (tmSameSzLemmaR eq tm')
  tmSameSzLemmaR (∼compPi eq eq') (tmPi tm tm') =
    tmPi (tmSameSzLemmaR eq tm) (tmSameSzLemmaR eq' tm')
  tmSameSzLemmaR (∼compApp eq eq' _) (tmApp tm tm') =
    tmApp (tmSameSzLemmaR eq tm) (tmSameSzLemmaR eq' tm')

TmC : Ctxt → Set
TmC ◇ = ⊤
TmC (Γ # A) = TmC Γ × Tm (clen Γ) A

TmCLemma : ∀{Γ A n} → TmC Γ → Γ [ n ]↦ A → Tm (clen Γ) A
TmCLemma (_ ,, q) here = tm-wk-lemma _ 0 1 q
TmCLemma (p ,, _) (there x) = tm-wk-lemma _ 0 1 (TmCLemma p x)

tyCloLemma : ∀{Θ Γ A t} Γ'
  → Θ ∷ Γ ++ Γ' ⊢ t ∶ A → TmC Γ' → Tm (clen Γ') t → Tm (clen Γ') A
tyCloLemma Γ' (free x x₁) tmc tmt = liftTm _ (ₗ↦Len (invert-ctx-ctx x) x₁)
tyCloLemma Γ' (bound ctx x) tmc tmt =
  TmCLemma tmc (cut-lemma _ _ _ x (pj-tm-var tmt))
tyCloLemma Γ' (lam {A = A} t) tmc (tmLam tmA tmt) = tmPi tmA aux
  where aux = tyCloLemma (Γ' # A) t (tmc ,, tmA) tmt
tyCloLemma Γ' (app t s _) tmc (tmApp tmt tms) with tyCloLemma Γ' t tmc tmt
tyCloLemma Γ' (app t s _) tmc (tmApp tmt tms) | tmPi _ tmB =
  sub-cover-lemma (clen Γ') 0 tmB tms
tyCloLemma Γ' (U-Π _ _) _ (tmPi _ _) = tmU
tyCloLemma Γ' (coe t x) tmc tmt = tySameSzLemmaL x (tyCloLemma Γ' t tmc tmt)
  where aux = tyCloLemma Γ' t tmc tmt
