module Syntax.Typed.MegaLemma where

open import Size
open import Function
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p₁ ; proj₂ to p₂)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Syntax.Raw
open import Syntax.Typed.Context
open import Syntax.Typed.ContextLemma
open import Syntax.Typed.Inversion
open import Syntax.Typed.Typed
open import Syntax.Typed.SizeLemma
open import Syntax.Typed.Renaming
open import Syntax.Typed.Model
open import Syntax.Typed.MetaRenaming

module SubDef where

  infix 4 _∷_⊢ₛ_∼_∶_
  data _∷_⊢ₛ_∼_∶_ : Ctxt → Ctxt → Subst → Subst → Ctxt → Set where
    ∼Id   : ∀{Θ Γ} → Θ ∷ Γ ⊢ₛ Id ∼ Id ∶ Γ
    ∼Cons : ∀{Θ Δ Γ A σ τ t s}
          → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ
          → Θ ∷ Δ ⊢ t ∶ sub A σ → Θ ∷ Δ ⊢ s ∶ sub A τ
          → Θ ∷ Δ ⊢ t ∼ s ∶ sub A σ → Θ ∷ Δ ⊢ s ∼ t ∶ sub A τ
          → Θ ∷ Δ ⊢ₛ σ , t ∼ τ , s ∶ Γ # A
    ∼Wk   : ∀{Θ ∇ Δ Γ σ τ w} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → Θ ∷ ∇ ⊢ᵣ w ∶ Δ
          → Θ ∷ ∇ ⊢ₛ σ · w ∼ τ · w ∶ Γ

open SubDef public

flippe : ∀{Θ Δ Γ σ τ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → Θ ∷ Δ ⊢ₛ τ ∼ σ ∶ Γ
flippe ∼Id = ∼Id
flippe (∼Cons σ t s x y) = ∼Cons (flippe σ) s t y x
flippe (∼Wk σ x) = ∼Wk (flippe σ) x

proj1 : ∀{Θ Δ Γ σ τ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → Θ ∷ Δ ⊢ₛ σ ∼ σ ∶ Γ
proj1 ∼Id = ∼Id
proj1 (∼Cons σ t s x y) = ∼Cons (proj1 σ) t t (∼refl t) (∼refl t)
proj1 (∼Wk σ x) = ∼Wk (proj1 σ) x

proj2 : ∀{Θ Δ Γ σ τ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → Θ ∷ Δ ⊢ₛ τ ∼ τ ∶ Γ
proj2 ∼Id = ∼Id
proj2 (∼Cons σ t s x y) = ∼Cons (proj2 σ) s s (∼refl s) (∼refl s)
proj2 (∼Wk σ x) = ∼Wk (proj2 σ) x

record RTy (Θ Δ : Ctxt) (A B : Term) (σ τ : Subst) : Set where
  constructor ⟨_∣_∣_⟩
  field
    lx : Θ ∷ Δ ⊢ sub A σ
    rx : Θ ∷ Δ ⊢ sub B τ
    eq : Θ ∷ Δ ⊢ sub A σ ∼ sub B τ

record RTm (Θ Δ : Ctxt) (A t s : Term) (σ τ : Subst) : Set where
  constructor ⟨_∣_∣_⟩
  field
    lx : Θ ∷ Δ ⊢ sub t σ ∶ sub A σ
    rx : Θ ∷ Δ ⊢ sub s τ ∶ sub A σ
    eq : Θ ∷ Δ ⊢ sub t σ ∼ sub s τ ∶ sub A σ

open RTy
open RTm

open import Data.Unit

mutual

  ⊧⊧_ : Ctxtₗ → Set
  ⊧⊧ ◇ = ⊤
  ⊧⊧ (Θ # A) = ⊧⊧ Θ × (Θ ∷ ◇ ⊧ A)

  ⊧_∷_ : Ctxt → Ctxt → Set
  ⊧ Θ ∷ ◇ = ⊧⊧ Θ
  ⊧ Θ ∷ (Γ # A) = (⊧ Θ ∷ Γ) × (Θ ∷ Γ ⊧ A)

  _∷_⊧_ : Ctxt → Ctxt → Term → Set
  Θ ∷ Γ ⊧ A = ∀{σ τ Δ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → RTy Θ Δ A A σ τ

  _∷_⊧_∶_ : Ctxt → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ t ∶ A =
    ∀{σ τ Δ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → RTy Θ Δ A A σ τ × RTm Θ Δ A t t σ τ

  _∷_⊧_∼_ : Ctxt → Ctxt → Term → Term → Set
  Θ ∷ Γ ⊧ A ∼ B =
    ∀{σ τ Δ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → RTy Θ Δ A B σ τ

  _∷_⊧_∼_∶_ : Ctxt → Ctxt → Term → Term → Term → Set
  Θ ∷ Γ ⊧ t ∼ s ∶ A =
    ∀{σ τ Δ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → RTy Θ Δ A A σ τ × RTm Θ Δ A t s σ τ

lll : ∀{Θ} → ⊧⊧ Θ → ⊢ Θ
lll {◇} c = ⊢◇
lll {Θ # x} (c ,, a) = ⊢# (lll c) (≡ty (id-sub _) (lx (a ∼Id)))

mctx-meaning : ∀{Θ} → ⊧⊧ Θ → ∀{σ τ Δ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ ◇ → ⊢ Θ ∷ Δ
mctx-meaning c ∼Id = ⊢◇ (lll c)
mctx-meaning c (∼Wk σ x) = ⊢wk-ctx (mctx-meaning c σ) x

ctx-meaning : ∀{Θ Γ} → ⊧ Θ ∷ Γ → ∀{σ τ Δ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → ⊢ Θ ∷ Δ
ctx-meaning {Θ} {◇} c σ = mctx-meaning c σ
ctx-meaning {Θ} {Γ # A} (c ,, a) ∼Id =
  ⊢# (ctx-meaning c ∼Id) (≡ty (id-sub _) (lx (a ∼Id)))
ctx-meaning {Θ} {Γ # A} (c ,, a) (∼Cons σ _ _ _ _) = ctx-meaning c σ
ctx-meaning {Θ} {Γ # A} c (∼Wk σ x) = ⊢wk-ctx (ctx-meaning c σ) x

rty-p1 : ∀{Θ Γ A B} → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ A ∼ A
rty-p1 h σ = ⟨ lx aux ∣ lx aux' ∣ ∼trans (eq aux) (∼symm (eq aux')) ⟩
  where aux = h σ ; aux' = h (proj2 σ)

rty-p2 : ∀{Θ Γ A B} → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ B ∼ B
rty-p2 h σ = ⟨ rx aux' ∣ rx aux ∣ ∼trans (∼symm (eq aux')) (eq aux) ⟩
  where aux = h σ ; aux' = h (proj1 σ)

rtm-symm : ∀{Θ Γ A t s} → Θ ∷ Γ ⊧ t ∼ s ∶ A → Θ ∷ Γ ⊧ s ∼ t ∶ A
rtm-symm h σ = p₁ (h σ) ,, ⟨ rx (p₂ aux) ∣ coe (lx (p₂ aux')) (eq $ p₁ aux')
                           ∣ ∼coe (∼symm (eq $ p₂ aux')) (eq $ p₁ aux') ⟩
  where aux = h (proj1 σ) ; aux' = h (flippe σ)

rtm-trans : ∀{Θ Γ A t s w}
          → Θ ∷ Γ ⊧ t ∼ s ∶ A → Θ ∷ Γ ⊧ s ∼ w ∶ A → Θ ∷ Γ ⊧ t ∼ w ∶ A
rtm-trans td sd σ = ty ,, ⟨ lx h ∣ rx h'
 ∣ ∼trans (eq h) (∼coe (eq $ p₂ (sd (proj2 σ))) (∼symm (eq ty))) ⟩
  where ty = p₁ (td σ) ; h = p₂ (td σ) ; h' = p₂ (sd σ)

⊢sh : ∀{Θ Δ Γ A σ τ} → Θ ∷ Δ ⊢ₛ σ ∼ τ ∶ Γ → ⊧ Θ ∷ Γ → RTy Θ Δ A A σ τ
    → Θ ∷ Δ # sub A σ ⊢ₛ sh σ ∼ sh τ ∶ Γ # A
⊢sh {A = A} σ ctx ih =
  ∼Cons (∼Wk σ (⊢Up ⊢Id ihl)) bnd (coe bnd eqq) bnd' (∼coe bnd' eqq)
  where
    ihc = ctx-meaning ctx σ ; ihl = lx ih
    bnd = bound (⊢# ihc ihl) (≡↦ (wk-subst A) here) ; bnd' = ∼refl bnd
    eqq = ≡ty∼ (wk-subst A) (wk-subst A) (⊢wk-ty-∼ (eq ih) (⊢Up ⊢Id ihl))

sub-lam : ∀{Θ Γ A B t}
        → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A → Θ ∷ (Γ # A) ⊧ t ∶ B → Θ ∷ Γ ⊧ Lam A t ∶ Π A B
sub-lam ch Ah th σ = aux ,,
  record { lx = lam (lx $ p₂ ih') ; rx = coe (lam (lx $ p₂ ih'2)) (∼symm (eq aux))
         ; eq = ∼ξ (eq ih) (eq $ p₂ ih') }
  where ih = Ah σ ; ih2 = Ah (proj2 σ)
        ih' = th (⊢sh σ ch ih) ; ih'2 = th (⊢sh (proj2 σ) ch ih2)
        aux = record { lx = Π (lx ih) (lx $ p₁ ih') ; rx = Π (rx ih) (lx $ p₁ ih'2)
                     ; eq = ∼Pi (eq ih) (eq $ p₁ ih') }

sub-app : ∀{Θ Γ A B t s} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A
  → Θ ∷ Γ ⊧ t ∶ Π A B → Θ ∷ Γ ⊧ s ∶ A → Θ ∷ Γ # A ⊧ B → Θ ∷ Γ ⊧ App t s ∶ (B [ s ])
sub-app {Θ} {Γ} {A} {B} {t} {s} ch Ah th sh Bh {σ = σ} {τ} σp =
  ⟨ ≡ty eqq (lx ihB) ∣ ≡ty eqq'' (rx ihB) ∣ ≡ty∼ eqq eqq'' (eq ihB) ⟩ ,,
  record { lx = ≡tm eqq' refl (app (lx h1) (lx h2) (lx Bsh))
         ; rx = let aux = app (lx h1') (lx h2') (lx Bsh')
                in coe aux (≡ty∼ (sym (trans (sub-comp B)
                  (≈ˢsub (≈ˢcons sub-id-R) B))) eqq (∼symm (eq ihB)))
         ; eq = ≡∼ refl refl eqq' (∼compApp (eq h1) (eq h2) (lx Bsh)) }
  where
    eqq = sym (trans (sub-comp B) (≈ˢsub (≈ˢtrans (sub-comp-R {_} {Id} {σ})
            (≈ˢcons (sub-id-L))) B))
    eqq'' = sym (trans (sub-comp B) (≈ˢsub (≈ˢtrans (sub-comp-R {_} {Id} {τ})
            (≈ˢcons (sub-id-L))) B))
    eqq' = trans (sub-comp B) (sym (trans (sub-comp B)
      (≈ˢsub (≈ˢtrans (sub-comp-R {s} {Id} {σ}) (≈ˢcons (≈ˢtrans (sub-id-L {σ})
        (≈ˢsym (sub-id-R {σ}))))) B)))
    h1 = p₂ (th σp) ; h1' = p₂ (th (flippe σp))
    Bsh = Bh (⊢sh σp ch (Ah σp)) ; Bsh' = Bh (⊢sh (flippe σp) ch (Ah (flippe σp)))
    h2 = p₂ (sh σp) ; h2' = p₂ (sh (flippe σp))
    ihB = Bh (∼Cons σp (lx h2) (lx h2') (eq h2) (eq h2'))

sub-U-Π : ∀{Θ Γ A B} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A ∶ U → Θ ∷ Γ # A ⊧ B ∶ U → Θ ∷ Γ ⊧ Π A B ∶ U
sub-U-Π ch Ah Bh σ =
  ⟨ U (ctx-meaning ch σ) ∣ U (ctx-meaning ch σ) ∣ ∼refl (U (ctx-meaning ch σ)) ⟩ ,,
  ⟨ U-Π (lx ih) (lx ih') ∣ U-Π (rx ih) (clemma-tm (rx ih')
    (ceq# (idctx∼ (ctx-meaning ch σ)) (El $ rx ih) (∼El $ eq ih) (∼El $ eq ih)))
  ∣ ∼compPi (eq ih) (eq ih') ⟩
  where ih = p₂ (Ah σ) ; ih' = p₂ (Bh (⊢sh σ ch
               ⟨ El (lx ih) ∣ El (rx ih) ∣ ∼El (eq ih) ⟩))

sub-coe : ∀{Θ Γ A B t} → Θ ∷ Γ ⊧ t ∶ A → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ t ∶ B
sub-coe th eh σ =
  record { lx = rx ih ; rx = rx ih' ; eq = ∼trans (∼symm (eq ih)) (eq (eh σ)) } ,,
  record { lx = coe (lx ih'') (eq ih) ; rx = coe (rx ih'') (eq ih)
         ; eq = ∼coe (eq ih'') (eq ih) }
  where ih = eh (proj1 σ) ; ih' = eh (proj2 σ) ; ih'' = p₂ (th σ)

sub-∼symm : ∀{Θ Γ A B} → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ B ∼ A
sub-∼symm eh σ = record { lx = rx $ eh (proj1 σ) ; rx = lx $ eh (proj2 σ)
                        ; eq = ∼symm $ eq $ eh (flippe σ) }

sub-∼trans : ∀{Θ Γ A B C} → Θ ∷ Γ ⊧ A ∼ B → Θ ∷ Γ ⊧ B ∼ C → Θ ∷ Γ ⊧ A ∼ C
sub-∼trans eh eh' σ = record { lx = lx $ eh σ ; rx = rx $ eh' σ
                             ; eq = ∼trans (eq $ eh σ) (eq $ eh' (proj2 σ)) }

sub-∼Pi : ∀{Θ Γ A A' B B'} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A
        → Θ ∷ Γ ⊧ A ∼ A' → Θ ∷ Γ # A ⊧ B ∼ B' → Θ ∷ Γ ⊧ Π A B ∼ Π A' B'
sub-∼Pi ch Ah eh eh' σ =
  record { lx = Π (lx ih) (lx ih') ; rx = Π (rx ih) (clemma-ty (rx ih')
    (ceq# (idctx∼ (ctx-meaning ch σ)) (rx ih) (eq ih) (eq ih))) ; eq = ∼Pi (eq ih) (eq ih') }
  where ih = eh σ ; ih' = eh' (⊢sh σ ch (Ah σ))

inv-mc : ∀{Θ A n} → ⊢ Θ → Θ [ n ]ₗ↦ A → Θ ∷ ◇ ⊢ A
inv-mc ⊢◇ ()
inv-mc (⊢# c ty) (here x) = extend-ty ty ty
inv-mc (⊢# c ty) (there x) = extend-ty (inv-mc c x) ty

⊧ctx⇒⊧mctx : ∀{Θ Γ} → ⊧ Θ ∷ Γ → ⊧⊧ Θ
⊧ctx⇒⊧mctx {̄_} {◇} c = c
⊧ctx⇒⊧mctx {̄_} {Γ # x} (c ,, _) = ⊧ctx⇒⊧mctx {_} {Γ} c

kkk : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → RTy Θ Γ A A Id Id
kkk {_} {_ # A} (c ,, a) here with a ∼Id
kkk {_} {_ # A} (c ,, a) here | ⟨ lx ∣ rx ∣ eq ⟩ =
  ⟨ ≡ty (sym (id-sub _)) wkk ∣ ≡ty (sym (id-sub _)) wkk
  ∣ ≡ty∼ (trans (cong₂ wk (id-sub A) refl) (sym (id-sub _)))
         (trans (cong₂ wk (id-sub A) refl) (sym (id-sub _)))
         (⊢wk-ty-∼ eq (⊢Up ⊢Id Ad)) ⟩
  where Ad = ≡ty (id-sub _) lx ; wkk = (⊢wk-ty Ad (⊢Up ⊢Id Ad))
kkk {_} {_ # A} (c ,, a) (there x) with kkk c x
kkk {_} {_ # A} (c ,, a) (there {A = B} x) | ⟨ lx' ∣ rx' ∣ eq' ⟩ =
  ⟨ ≡ty (sym (id-sub _)) wkk ∣ ≡ty (sym (id-sub _)) wkk
  ∣ ≡ty∼ (trans (cong₂ wk (id-sub B) refl) (sym (id-sub _)))
         (trans (cong₂ wk (id-sub B) refl) (sym (id-sub _)))
         (⊢wk-ty-∼ eq' (⊢Up ⊢Id Ad)) ⟩
  where Bd = ≡ty (id-sub B) lx' ; Ad = ≡ty (id-sub A) (lx (a ∼Id))
        wkk = (⊢wk-ty Bd (⊢Up ⊢Id Ad))

azd : ∀{σ t} A → sub (wk A (Up Id)) (σ , t) ≡ sub A σ
azd A = trans (subst-wk A) (≈ˢsub id-wk-sub-L A)

sub-bound : ∀{Θ Γ A n} → ⊧ Θ ∷ Γ → Γ [ n ]↦ A → Θ ∷ Γ ⊧ Bound n ∶ A
sub-bound c x ∼Id = kkk c x ,, ⟨ bnd ∣ bnd ∣ ∼refl bnd ⟩
  where bnd = ≡tm (sym (id-sub _)) refl (bound (ctx-meaning c ∼Id) x)
sub-bound {_} {_ # A} (c ,, a) here (∼Cons σ x₁ x₂ x₃ x₄) =
  ⟨ ≡ty'' (azd A) (lx (a σ)) ∣ ≡ty'' (azd A) (rx (a σ))
  ∣ ≡ty∼ (sym (azd A)) (sym (azd A)) (eq (a σ)) ⟩ ,,
  ⟨ ≡tm'' (azd A) refl x₁ ∣ ≡tm'' (azd A) refl (coe x₂ (∼symm (eq (a σ))))
  ∣ ≡tm∼ refl refl (sym (azd A)) x₃ ⟩
sub-bound {_} {_ # A} (c ,, a) (there x) (∼Cons σ x₁ x₂ x₃ x₄) with sub-bound c x σ
sub-bound {_} {_ # A} (c ,, a) (there {A = B} x) (∼Cons σ x₁ x₂ x₃ x₄)
  | ⟨ lx' ∣ rx' ∣ eq' ⟩ ,, ⟨ lx'' ∣ rx'' ∣ eq'' ⟩ =
  ⟨ ≡ty'' (azd B) lx' ∣ ≡ty'' (azd B) rx'
  ∣ ≡ty∼ (sym (azd B)) (sym (azd B)) eq' ⟩ ,,
  ⟨ ≡tm'' (azd B) refl lx'' ∣ ≡tm'' (azd B) refl rx''
  ∣ ≡tm∼ refl refl (sym (azd B)) eq'' ⟩
sub-bound c x (∼Wk σ x₁) with sub-bound c x σ
sub-bound {A = A} c x (∼Wk σ w) | ⟨ lx' ∣ rx' ∣ eq' ⟩ ,, ⟨ lx'' ∣ rx'' ∣ eq'' ⟩ =
  ⟨ ≡ty (wk-subst A) (⊢wk-ty lx' w) ∣ ≡ty (wk-subst A) (⊢wk-ty rx' w)
  ∣ ≡ty∼ (wk-subst A) (wk-subst A) (⊢wk-ty-∼ eq' w) ⟩ ,,
  ⟨ ≡tm (wk-subst A) refl (⊢wk-tm lx'' w) ∣ ≡tm (wk-subst A) refl (⊢wk-tm rx'' w)
  ∣ ≡tm∼ refl refl (wk-subst A) (⊢wk-tm-∼ eq'' w) ⟩


sub-comp-aux : ∀ {σ} t s → sub (t [ s ]) σ ≡ (sub t (sh σ)) [ sub s σ ]
sub-comp-aux {σ} t s =
  trans (sub-comp t) (trans (≈ˢsub (sub-comp-R {s}
  ∘≈ˢ ≈ˢcons (sub-id-L ∘≈ˢ ≈ˢsym sub-id-R)) t) (sym (sub-comp t)))

sub-comp-aux' : ∀ {σ} t s → sub (t [ s ]) σ ≡ sub t (σ , sub s σ)
sub-comp-aux' t s =
  trans (sub-comp-aux t s)
 (trans (sub-comp t) (≈ˢsub (≈ˢcons sub-id-R) t))

⊧β : ∀{Θ Γ A B t s} → Θ ∷ ◇ # A ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
   → ⊧ Θ ∷ Γ → Θ ∷ ◇ # A ⊧ t ∶ B
   → Θ ∷ ◇ ⊧ s ∶ A → Θ ∷ Γ ⊧ App (Lam A t) s ∼ t [ s ] ∶ (B [ s ])
⊧β {Θ} {Γ} {A} {B} {t} {s} td sd ch th sh σ =
  ⟨ ≡ty'' (null-sub tmm) Bsw ∣ ≡ty'' (null-sub tmm) Bsw
  ∣ ≡ty∼ (sym (trans (null-sub tmm) (sym (null-wk tmm))))
         (sym (trans (null-sub tmm) (sym (null-wk tmm)))) (⊢wk-ty-∼ Bs∼ w) ⟩ ,,
  ⟨ ≡tm'' (trans (null-sub tmm) (sym (null-wk tmm)))
          (trans (null-sub tmapp) (sym (null-wk tmapp)))
    (⊢wk-tm (app (lam td) sd Bd) w)
  ∣ ≡tm'' (trans (null-sub tmm) (sym (null-wk tmm)))
          (trans (null-sub tmts) (sym (null-wk tmts))) (⊢wk-tm ts w)
  ∣ ≡tm∼ (sym (null-sub tmapp)) (sym (null-sub tmts)) (sym (null-sub tmm)) (∼β cd td sd) ⟩
  where
    cd = ctx-meaning ch σ ; w = ⊢up cd
    sh' = sh ∼Id ; sd' = lx (p₂ sh')
    th' = th (⊢sh ∼Id (⊧ctx⇒⊧mctx {Θ} {Γ} ch) (p₁ sh'))
    Bd = ≡ty' (cong₂ _#_ refl (id-sub A)) (id-sub' B 1) (lx (p₁ th'))
    tmt = tmLen td ; tms = tmLen sd
    tmm = (sub-cover-lemma 0 0 (p₁ tmt) (p₂ tms))
    tmts = sub-cover-lemma 0 0 (p₂ tmt) (p₂ tms)
    tmapp = tmApp (tmLam (p₁ tms) (p₂ tmt)) (p₂ tms)
    th'' = th (∼Cons ∼Id sd' sd' (∼refl sd') (∼refl sd'))
    Bs = ≡ty (cong (sub B) (cong (_,_ Id) (id-sub s))) (lx (p₁ th''))
    Bsw = ≡ty (null-wk tmm) (⊢wk-ty Bs w)
    Bs∼ = ≡ty∼ (cong (sub B) (cong (_,_ Id) (id-sub s)))
               (cong (sub B) (cong (_,_ Id) (id-sub s))) (eq (p₁ th''))
    ts = ≡tm (cong (sub B) (cong (_,_ Id) (id-sub s)))
             (cong (sub t) (cong (_,_ Id) (id-sub s))) (lx (p₂ th''))
    ts∼ = ≡tm∼ (cong (sub t) (cong (_,_ Id) (id-sub s)))
               (cong (sub t) (cong (_,_ Id) (id-sub s)))
               (cong (sub B) (cong (_,_ Id) (id-sub s))) (eq (p₂ th''))

⊧ξ : ∀{Θ Γ A A' B t t'} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A ∼ A' → Θ ∷ Γ # A ⊧ t ∼ t' ∶ B
   → Θ ∷ Γ ⊧ Lam A t ∼ Lam A' t' ∶ Π A B
⊧ξ ch Ah th σ =
  ⟨ Π (lx Ax') (lx (p₁ tx)) ∣ Π (rx Ax') (rx (p₁ tx')) ∣ ∼Pi (eq Ax') (eq (p₁ tx)) ⟩ ,,
  ⟨ lam (lx (p₂ tx)) ∣ coe (lam (clemma-tm (rx (p₂ tx)) eqq))
    (∼Pi (∼symm (eq (Ah σ))) (clemma-ty∼ (eq (p₁ tx'')) eqq))
  ∣ ∼ξ (eq (Ah σ)) (eq (p₂ tx)) ⟩
  where
    eqq = (ceq# (idctx∼ (ctx-meaning ch σ)) (rx (Ah σ)) (eq (Ah σ)) (eq (Ah σ)))
    Ax' = rty-p1 Ah σ ; Ax'' = rty-p1 Ah (proj2 σ)
    tx = th (⊢sh σ ch Ax') ; tx' = th (⊢sh (proj2 σ) ch Ax'')
    tx'' = th (⊢sh (proj1 σ) ch (rty-p1 Ah (proj1 σ)))


compApp : ∀{Θ Γ r r' s s' A B} → ⊧ Θ ∷ Γ
        → Θ ∷ Γ ⊧ r ∼ r' ∶ Π A B → Θ ∷ Γ ⊧ s ∼ s' ∶ A
        → Θ ∷ Γ # A ⊧ B → Θ ∷ Γ ⊧ App r s ∼ App r' s' ∶ (B [ s ])
compApp {r = r} {r'} {s} {s'} {A} {B} ch rh sh Bh σ =
  ⟨ ≡ty'' (sub-comp-aux' B s) (lx Bs) ∣ ≡ty'' (sub-comp-aux' B s) (rx Bs)
  ∣ ≡ty∼ (sym (sub-comp-aux' B s)) (sym (sub-comp-aux' B s)) (eq Bs) ⟩ ,,
  ⟨ ≡tm'' (sub-comp-aux B s) refl (app (lx rxtm) (lx (p₂ sx)) (lx Bd))
  ∣ ≡tm'' (sub-comp-aux B s) refl (coe (app (rx (p₂ rxx')) (rx (p₂ sx2))
    (clemma-ty (rx Bd) (ceq# (idctx∼ (ctx-meaning ch σ))
      (rx (p₁ sx)) (eq (p₁ sx)) (eq (p₁ sx)))))
      (≡ty∼ (sym (trans (sym (sub-comp-aux B s')) (sub-comp-aux' B s')))
            (sym (trans (sym (sub-comp-aux B s)) (sub-comp-aux' B s)))
              (∼symm (eq Bs'))))
  ∣ ≡tm∼ refl refl (sym (sub-comp-aux B s))
      (∼compApp (eq (p₂ rxx)) (eq (p₂ sx)) (lx Bd)) ⟩
  where
    sx = sh σ ; sx1 = sh (proj1 σ) ; sx2 = sh (proj2 σ) ; sxx = sh (flippe σ)
    aux = rtm-symm sh (flippe σ) ; aux' = rtm-trans sh (rtm-symm sh)
    Bd = Bh (⊢sh σ ch (p₁ sx))
    Bs = Bh (∼Cons σ (lx (p₂ sx)) (lx (p₂ sx2)) (eq (p₂ (aux' σ)))
         (eq (p₂ (aux' (flippe σ)))))
    Bs' = Bh (∼Cons σ (lx (p₂ sx)) (rx (p₂ sx2)) (eq (p₂ sx)) (eq (p₂ aux)))
    rxx = rh σ ; rxx' = rh (proj2 σ) ; rxtm = p₂ (rh σ)

compPi : ∀{Θ Γ A A' B B'} → ⊧ Θ ∷ Γ → Θ ∷ Γ ⊧ A ∼ A' ∶ U
       → Θ ∷ Γ # A ⊧ B ∼ B' ∶ U → Θ ∷ Γ ⊧ Π A B ∼ Π A' B' ∶ U
compPi ch Ah Bh σ = ⟨ ud ∣ ud ∣ ∼refl ud ⟩ ,,
  ⟨ U-Π (lx Ax) (lx Bx)
  ∣ U-Π (rx Ax) (clemma-tm (rx Bx) (ceq# (idctx∼ cd)
     (El (rx Ax)) (∼El (eq Ax)) (∼El (eq Ax)))) ∣ ∼compPi (eq Ax) (eq Bx) ⟩
  where
    cd = ctx-meaning ch σ ; ud = U cd
    Ax = p₂ (Ah σ) ; Ax' = rtm-trans Ah (rtm-symm Ah) σ
    Bx = p₂ (Bh (⊢sh σ ch ⟨ El (lx Ax) ∣ El (lx (p₂ (Ah (flippe σ))))
         ∣ ∼El (eq (p₂ Ax')) ⟩))

subModel : Model
subModel = record
  { ⊧⊧_ = ⊧⊧_ ; ⊧_∷_ = ⊧_∷_ ; _∷_⊧_ = _∷_⊧_
  ; _∷_⊧_∶_ = _∷_⊧_∶_ ; _∷_⊧_∼_ = _∷_⊧_∼_ ; _∷_⊧_∼_∶_ = _∷_⊧_∼_∶_
  ; M-⊢ₘ◇ = tt ; M-⊢ₘ# = _,,_ ; M-⊢◇ = id ; M-⊢# = _,,_
  ; M-U = λ x σ → let u = U (ctx-meaning x σ) in ⟨ u ∣ u ∣ ∼refl u ⟩
  ; M-El = λ x σ → let y = p₂ (x σ) in ⟨ El (lx y) ∣ El (rx y) ∣ ∼El (eq y) ⟩
  ; M-Π = λ ch Ah Bh σ → let x = Ah σ ; y = Bh (⊢sh σ ch (Ah σ)) in
     ⟨ Π (lx x) (lx y) ∣ Π (rx x) (rx (Bh (⊢sh (proj2 σ) ch (Ah (proj2 σ)))))
     ∣ ∼Pi (eq x) (eq y) ⟩
  ; M-free = λ _ c' x σ → let c = ctx-meaning c'
                              cd = invert-ctx-ctx (c ∼Id) ; tm = ₗ↦Len cd x
                              eq = trans (null-wk tm) (sym (null-sub tm))
                              eq' = trans (null-wk tm) (sym (null-sub tm))
                              Ad = ⊢wk-ty (inv-mc cd x) (⊢up (c σ))
                              fd = free (c σ) (≡ₗ↦ (sym (null-sub tm)) x)
      in ⟨ ≡ty eq Ad ∣ ≡ty eq' Ad ∣ ≡ty∼ eq eq' (∼refl Ad) ⟩ ,,
         ⟨ fd ∣ fd ∣ ∼refl fd ⟩
  ; M-bound = sub-bound
  ; M-lam = sub-lam ; M-app = sub-app ; M-U-Π = sub-U-Π ; M-coe = sub-coe
  ; M-∼refl = λ x x₁ → x x₁ ; M-∼symm = sub-∼symm ; M-∼trans = sub-∼trans
  ; M-∼Pi = sub-∼Pi
  ; M-∼El = λ x σ → let ih = p₂ (x σ) in ⟨ El (lx ih) ∣ El (rx ih) ∣ ∼El (eq ih) ⟩
  ; M-∼refl' = λ x σ → p₁ (x σ) ,, p₂ (x σ) ; M-∼symm' = rtm-symm
  ; M-∼trans' = λ x x₁ σ → rtm-trans x x₁ σ
  ; M-∼coe = λ x y σ → let ih = p₂ $ x σ ; ih' = y (proj1 σ) in rty-p2 y σ ,,
      ⟨ coe (lx ih) (eq ih') ∣ coe (rx ih) (eq ih') ∣ ∼coe (eq ih) (eq ih') ⟩
  ; M-∼β = ⊧β ; M-∼ξ = ⊧ξ ; M-∼compPi = compPi ; M-∼compApp = compApp }
