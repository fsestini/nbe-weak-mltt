module Syntax.Raw.Substitution.Properties where

open import Utils
open import Function
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming public
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Syntax.Raw.Substitution.Substitution
open import Syntax.Raw.Substitution.Equality

postulate id-sub-var' : ∀ x n u → wk (sub-var x (shift n Id)) (up u Id) ≡ Bound (x + u)
-- id-sub-var' x zero _ = {!!}
-- id-sub-var' zero (suc n) _ = {!!}
-- id-sub-var' (suc x) (suc n) u = {!!}

id-sub' : ∀ t n → sub t (shift n Id) ≡ t
id-sub' (Free x) n = refl
id-sub' (Bound x) n =
  trans (sym (id-wk 0 _)) (trans (id-sub-var' x n 0) (cong Bound (plus-0 _)))
id-sub' (Lam t t₁) n = cong₂ Lam (id-sub' t n) (id-sub' t₁ (suc n))
id-sub' (App t₁ t₂) n = cong₂ App (id-sub' t₁ n) (id-sub' t₂ n)
id-sub' U n = refl
id-sub' (Π t t₁) n = cong₂ Π (id-sub' t n) (id-sub' t₁ (suc n))

id-sub : ∀ t → sub t Id ≡ t
id-sub t = id-sub' t 0

eq-dot : ∀{σ τ w} → σ ≈ˢ τ → (σ · w) ≈ˢ (τ · w)
eq-dot {w = w} (≈ˢin eq) = ≈ˢin λ x → cong (flip wk w) (eq x)

eq-dot' : ∀{σ w w'} → w ≈ʷ w' → (σ · w) ≈ˢ (σ · w')
eq-dot' weq = ≈ˢin λ x → ≈ʷwk weq _

sh-skip-lemma : ∀{σ w} → sh σ · Skip w ≈ˢ sh (σ · w)
sh-skip-lemma {σ} {w} =
  ≈ˢin λ { zero → refl
         ; (suc x) → trans (wk-comp (sub-var x σ))
                    (trans (≈ʷwk (eq-up idw-L) (sub-var x σ))
                           (sym (wk-comp (sub-var x σ)))) }

subst-lift-sw : ∀ {w σ} t → sub t (sh σ · Skip w) ≡ sub t (sh (σ · w))
subst-lift-sw t = ≈ˢsub sh-skip-lemma t

wk-subst : ∀{w σ} t → wk (sub t σ) w ≡ sub t (σ · w)
wk-subst (Free x) = refl
wk-subst (Bound x) = refl
wk-subst (Lam A t) =
  cong₂ Lam (wk-subst A) (trans (wk-subst t) (subst-lift-sw t))
wk-subst (App t s) = cong₂ App (wk-subst t) (wk-subst s)
wk-subst U = refl
wk-subst {w} {σ} (Π A B) =
  cong₂ Π (wk-subst A) (trans (wk-subst {Skip w} {sh σ} B) (subst-lift-sw B))

subst-lift-ws : ∀{w σ} t → sub t (Skip w ʷ· sh σ) ≡ sub t (sh (w ʷ· σ))
subst-lift-ws = ≈ˢsub (≈ˢin λ { zero → refl ; (suc x) → refl })

subst-wk-var : ∀ w σ x → sub-var (wk-var x w) σ ≡ sub-var x (w ʷ· σ)
subst-wk-var w Id x = refl
subst-wk-var w (σ · w') x = cong (flip wk w') (subst-wk-var w σ x)
subst-wk-var Id (σ , t) x = refl
subst-wk-var (Up w) (σ , t) x = subst-wk-var w σ x
subst-wk-var (Skip w) (σ , t) zero = refl
subst-wk-var (Skip w) (σ , t) (suc x) = subst-wk-var w σ x

subst-wk : ∀{w σ} t → sub (wk t w) σ ≡ sub t (w ʷ· σ)
subst-wk (Free x) = refl
subst-wk {w} {σ} (Bound x) = subst-wk-var w σ x
subst-wk {w} {σ} (Lam A t) =
  cong₂ Lam (subst-wk A) (trans (subst-wk t) (subst-lift-ws {w} {σ} t))
subst-wk {w} {σ} (App t s) =
  cong₂ App (subst-wk t) (subst-wk s)
subst-wk U = refl
subst-wk {w} {σ} (Π A B) =
  cong₂ Π (subst-wk A) (trans (subst-wk B) (subst-lift-ws {w} {σ} B))

sub-id-R : ∀{σ} → σ · Id ≈ˢ σ
sub-id-R {σ} = ≈ˢin λ x → id-wk 0 (sub-var x σ)

id-wk-sub-L : ∀ {σ} → (Id ʷ· σ) ≈ˢ σ
id-wk-sub-L {Id} = sub-id-R
id-wk-sub-L {σ · x} = eq-dot id-wk-sub-L
id-wk-sub-L {σ , x} = ≈ˢrefl

id-wk-comp : ∀ σ τ → (σ ·ˢ (Id ʷ· τ)) ≈ˢ (σ ·ˢ τ)
id-wk-comp σ Id = sub-id-R
id-wk-comp σ (τ · x) = eq-dot (id-wk-comp σ τ)
id-wk-comp σ (τ , x) = ≈ˢrefl

sub-comp-lift : ∀{σ τ} → (sh σ ·ˢ sh τ) ≈ˢ sh (σ ·ˢ τ)
sub-comp-lift {σ} {τ} = ≈ˢcons (eq-dot (id-wk-comp σ τ))

sub-comp-var : ∀ σ τ x → sub (sub-var x σ) τ ≡ sub-var x (σ ·ˢ τ)
sub-comp-var σ Id x = id-sub (sub-var x σ)
sub-comp-var σ (τ · w) x =
  trans (sym (wk-subst (sub-var x σ))) (cong (flip wk w) (sub-comp-var σ τ x))
sub-comp-var Id (τ , t) x = refl
sub-comp-var (σ · w) (τ , t) x =
  trans (subst-wk {w} {τ , t} (sub-var x σ)) (sub-comp-var σ (w ʷ· (τ , t)) x)
sub-comp-var (σ , t) (τ , s) zero = refl
sub-comp-var (σ , t) (τ , s) (suc x) = sub-comp-var σ (τ , s) x

sub-comp : ∀{σ τ} t → sub (sub t σ) τ ≡ sub t (σ ·ˢ τ)
sub-comp {σ} {τ} (Π A B) =
  cong₂ Π (sub-comp A) (trans (sub-comp B) (≈ˢsub (sub-comp-lift {σ} {τ}) B))
sub-comp (Free x) = refl
sub-comp {σ} {τ} (Bound x) = sub-comp-var σ τ x
sub-comp {σ} {τ} (Lam A t) =
  cong₂ Lam (sub-comp A) (trans (sub-comp t) (≈ˢsub (sub-comp-lift {σ} {τ}) t))
sub-comp {σ} {τ} (App t s) = cong₂ App (sub-comp t) (sub-comp s)
sub-comp U = refl

sub-id-L : ∀{σ} → Id ·ˢ σ ≈ˢ σ
sub-id-L {σ} = ≈ˢin λ x → sym (sub-comp-var Id σ x)

subid-LR : ∀{σ} → Id ·ˢ σ ≈ˢ σ · Id
subid-LR = ≈ˢtrans sub-id-L (≈ˢsym sub-id-R)

sub-comp-R : ∀ {t σ τ} → (σ , t) ·ˢ τ ≈ˢ (σ ·ˢ τ , sub t τ)
sub-comp-R {t} {σ} {τ} =
  ≈ˢin λ { zero → sym (sub-comp-var (σ , t) τ 0)
         ; (suc x) → trans (sym (sub-comp-var (σ , t) τ (suc x)))
                           (sub-comp-var σ τ x) }

sub-wk-comp : ∀{σ w s} → σ · w , wk s w ≈ˢ (σ , s) · w
sub-wk-comp {σ} {w} {s} = ≈ˢin λ { zero → refl ; (suc x) → refl }

-- sgl-comp : ∀{σ s} → sh σ ·ˢ (Id , s) ≈ˢ (σ , s)
-- sgl-comp zero = refl
-- sgl-comp {σ} (suc x) = id-wk 0 (sub-var x σ)

-- singleton-comp : ∀ {σ s} t → sub (sub t (sh σ)) (Id , s) ≡ sub t (σ , s)
-- singleton-comp {σ} {s} t =
--   trans (sub-comp {sh σ} {Id , s} t) (eq-sub (≈ˢcons {s = s} (sub-id-L {σ})) t)

w-accum : ∀{σ w w'} → (σ · w) · w' ≈ˢ σ · (w ·ʷ w')
w-accum {σ} {w} {w'} = ≈ˢin λ x → wk-comp (sub-var x σ)

sub-var-cover-lemma' : ∀{s} n m u x → x ≤ m + n → Tm (u + n) s
                    → Tm (m + (u + n)) (sub-var x (shift m (Id · up u Id , s)))
sub-var-cover-lemma' n zero u zero p tms = tms
sub-var-cover-lemma' .(suc _) zero u (suc x) (s≤s p) tms =
  tm-wk-lemma _ 0 u (tmVar p)
sub-var-cover-lemma' n (suc m) u zero p tms = tmVar z≤n
sub-var-cover-lemma' n (suc m) u (suc x) (s≤s p) tms =
  tm-wk-lemma (m + (u + n)) 0 1 (sub-var-cover-lemma' n m u x p tms)

sub-cover-lemma' : ∀{t s} n m u → Tm (suc (m + n)) t → Tm (u + n) s
                → Tm (m + (u + n)) (sub t (shift m (Id · up u Id , s)))
sub-cover-lemma' n m u tmFree tms = tmFree
sub-cover-lemma' n m u tmU tms = tmU
sub-cover-lemma' n m u (tmVar x₁) tms = sub-var-cover-lemma' n m u _ x₁ tms
sub-cover-lemma' n m u (tmLam tm tm₁) tms =
  tmLam (sub-cover-lemma' n m u tm tms) (sub-cover-lemma' n (suc m) u tm₁ tms)
sub-cover-lemma' n m u (tmApp tm₁ tm₂) tms =
  tmApp (sub-cover-lemma' n m u tm₁ tms) (sub-cover-lemma' n m u tm₂ tms)
sub-cover-lemma' n m u (tmPi tm tm₁) tms =
  tmPi (sub-cover-lemma' n m u tm tms) (sub-cover-lemma' n (suc m) u tm₁ tms)

sub-cover-lemma : ∀{t s} n m → Tm (suc (m + n)) t → Tm n s
                → Tm (m + n) (sub t (shift m (Id , s)))
sub-cover-lemma {t} n m tmt tms =
  Tm≡' (≈ˢsub (≈ˢshift (≈ˢcons sub-id-R) m) t) (sub-cover-lemma' n m 0 tmt tms)

null-sub-var : ∀{σ} n x → x ≤ n → sub-var x (shift (suc n) σ) ≡ Bound x
null-sub-var zero .0 z≤n = refl
null-sub-var (suc n) zero p = refl
null-sub-var {σ} (suc n) (suc x) (s≤s p)
  rewrite null-sub-var {σ} n x p = refl

null-sub : ∀{σ t n} → Tm n t → sub t (shift n σ) ≡ t
null-sub tmFree = refl
null-sub tmU = refl
null-sub (tmVar x) = null-sub-var _ _ x
null-sub (tmLam tm tm₁) =
  cong₂ Lam (null-sub tm) (null-sub tm₁)
null-sub (tmApp tm₁ tm₂) = cong₂ App (null-sub tm₁) (null-sub tm₂)
null-sub (tmPi tm tm₁) = cong₂ Π (null-sub tm) (null-sub tm₁)

¬Tm-sub-var-lemma : ∀{σ} n m x
                  → ¬Tm (m + n) (wk (sub-var x (shift n σ)) (up m Id))
                  → ¬Tm (m + n) (Bound (x + m))
¬Tm-sub-var-lemma zero m zero tm rewrite plus-0 m = ¬tmVar (≤refl m)
¬Tm-sub-var-lemma zero m (suc x) tm rewrite plus-0 m = ¬tmVar (aux x m)
  where
    aux : ∀ x m → suc (x + m) ≥ m
    aux x zero = z≤n
    aux x (suc m) rewrite plus-succ x m = s≤s (aux x m)
¬Tm-sub-var-lemma (suc n) m zero (¬tmVar x) rewrite wk-var-ups 0 m = ¬tmVar x
¬Tm-sub-var-lemma {σ} (suc n) m (suc x) tm =
  ¬Tm≡ (cong Bound (plus-succ x m)) (sym (plus-succ m n))
    (¬Tm-sub-var-lemma {σ} n (suc m) x (¬Tm≡ aux (plus-succ m n) tm))
  where
    aux = trans (wk-comp (sub-var x (shift n σ))) (≈ʷwk (ups-comp 1 m) _)

¬Tm-sub-lemma : ∀{t σ} n → ¬Tm n (sub t (shift n σ)) → ¬Tm n t
¬Tm-sub-lemma {Free x} n tm = tm
¬Tm-sub-lemma {Bound x} n tm =
  ¬Tm≡ (cong Bound (plus-0 x)) refl
    (¬Tm-sub-var-lemma n 0 x (¬Tm≡ (sym (id-wk 0 _)) refl tm))
¬Tm-sub-lemma {Lam t t₁} n (¬tmLam₁ tm) = ¬tmLam₁ (¬Tm-sub-lemma n tm)
¬Tm-sub-lemma {Lam t t₁} n (¬tmLam₂ x tm) = inj¬tmLam₂ (¬Tm-sub-lemma (suc n) tm)
¬Tm-sub-lemma {U} n tm = tm
¬Tm-sub-lemma {Π t t₁} n (¬tmPi₁ tm) = ¬tmPi₁ (¬Tm-sub-lemma n tm)
¬Tm-sub-lemma {Π t t₁} n (¬tmPi₂ x tm) = inj¬tmPi₂ (¬Tm-sub-lemma (suc n) tm)
¬Tm-sub-lemma {App t t₁} n (¬tmApp₁ tm) = ¬tmApp₁ (¬Tm-sub-lemma n tm)
¬Tm-sub-lemma {App t t₁} n (¬tmApp₂ x tm) = inj¬tmApp₂ (¬Tm-sub-lemma n tm)

sub-uncover-var : ∀{s} u n m x → Tm n s
                 → Tm (u + (m + n)) (wk (sub-var x (shift m (Id , s))) (up u Id))
                 → x ≤ m + n
sub-uncover-var u n zero zero tms tmx = z≤n
sub-uncover-var u n zero (suc x) tms tmx = <inv u _ _ ff
  where
    ≤-≡L : ∀{n m r} → n ≤ r → m ≡ n → m ≤ r
    ≤-≡L p refl = p
    <inv : ∀ x y z → x + y < x + z → y < z
    <inv zero y z p = p
    <inv (suc x) y z (s≤s p) = <inv x y z p
    wkv : ∀ u x → wk-var x (up u Id) ≡ u + x
    wkv zero x = refl
    wkv (suc u) x = cong suc (wkv u x)
    ff : u + x < u + n
    ff = ≤-≡L (pj-tm-var tmx) (cong suc (sym (wkv u x)))
sub-uncover-var u n (suc m) zero tms tmx = z≤n
sub-uncover-var {s} u n (suc m) (suc x) tms tmx = s≤s aux
  where
    upup : ∀ u x → wk-var x (Up Id ·ʷ up u Id) ≡ suc (wk-var x (up u Id))
    upup zero x = refl
    upup (suc u) x = cong suc (upup u x)
    tee = (sub-var x (shift m (Id , s)))
    foo : wk (wk tee (Up Id)) (up u Id) ≡ wk tee (Up (up u Id))
    foo = trans (wk-comp {Up Id} {up u Id} tee) (≈ʷwk (≈ʷin (upup u)) tee)
    aux = sub-uncover-var (suc u) n m x tms
      (Tm≡'' (sym (plus-succ u (m + n))) (sym foo) tmx)

sub-uncover : ∀{s n} m t → Tm n s → Tm (m + n) (sub t (shift m (Id , s)))
            → Tm (suc (m + n)) t
sub-uncover m (Free x) tms tmt = tmFree
sub-uncover m (Bound x) tms tmt =
  tmVar (sub-uncover-var 0 _ m x tms (Tm≡' (sym (id-wk 0 _)) tmt))
sub-uncover m (Lam A t) tms (tmLam tmA tmt) =
  tmLam (sub-uncover m A tms tmA) (sub-uncover (suc m) t tms tmt)
sub-uncover m (App a b) tms (tmApp tma tmb) =
  tmApp (sub-uncover m a tms tma) (sub-uncover m b tms tmb)
sub-uncover m U tms tmt = tmU
sub-uncover m (Π A B) tms (tmPi tmA tmB) =
  tmPi (sub-uncover m A tms tmA) (sub-uncover (suc m) B tms tmB)
