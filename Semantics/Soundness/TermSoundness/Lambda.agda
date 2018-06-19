module Semantics.Soundness.TermSoundness.Lambda where

open import Semantics.Soundness.LogicalRelation
open import Semantics.Soundness.SubLogicalRelation.Definition
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness hiding (lamLemma)
open import Data.Product renaming (_,_ to _,,_)
open import Syntax.Typed.Inversion
open import Size
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Syntax.Typed.Model
open import Data.Nat
open import Syntax.Typed.MetaRenaming
open import Syntax.Typed.SizeLemma
open import Syntax.Typed.EqLemma
open import Syntax.Typed.ShrinkLemma
open import Semantics.Soundness.TypeSoundness.Definition
open import Semantics.Soundness.TermSoundness.Definition
open import Semantics.Soundness.LogicalRelation.Irrelevance
open import Data.Unit

open ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
open ⟦_⟧≃⟦_⟧_∈𝒯
open _∈_
open _∈⟦_⟧_
open SemTy
open _[_,_]
open _[_,_]∈_
open _●_∈ap_

lamLemma' : ∀{Θ Δ A B t σ A' B' d}
          → (nfB : Nf B')
          → (nfd : Nf d)
          → (Ah : (w : Wk) → wk A' w ∈𝒯)
          → (Bh : ∀{a w} → P (El𝒯 (Ah w)) a → B' [ w , a ]∈𝒯)
          → (qh : ∀{a w} → (pa : P (El𝒯 (Ah w)) a) → d [ w , a ]∈ El𝒯 (∈t (Bh pa)))
          → (p : P (El𝒯 (tPi nfB Ah Bh)) (Lam A' d))
          → (∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Δ →
            (p₁ : P (El𝒯 (Ah w)) a) →
            Θ ∷ Γ' ⊢ s ∶ wk (sub A σ) w ® Ah w ∋ p₁ →
            Θ ∷ Γ' ⊢ sub t (sh σ) [ w , s ]ₛ ∶ sub B (sh σ) [ w , s ]ₛ ®
            ∈t (Bh p₁) ∋ wit (∈tm (qh p₁)))
          → Θ ∷ Δ ⊢ sub A σ ® Ah Id
          → Θ ∷ Δ # sub A σ ⊢ sub t (sh σ) ∶ sub B (sh σ)
          → Θ ∷ Δ ⊢ Lam (sub A σ) (sub t (sh σ)) ∶ Π (sub A σ) (sub B (sh σ))
                  ® tPi nfB Ah Bh ∋ uhm'' (𝒯Nf (subst _∈𝒯 (id-wk 0 A') (Ah Id)))
                     nfB nfd Ah Bh qh refl
lamLemma' {Θ} {Δ} {A} {B} {t} {σ} {A'} {B'} {d} nfB nfd Ah Bh qh p h relS td =
  ®𝒯λ qh (tPi nfB Ah Bh) (uhm'' nfA' nfB nfd Ah Bh qh refl)
    (∼refl (Π (der-tyₜ {ty = Ah Id} relS) (invert-type td))) relS (∼refl (lam td)) h
  where nfA' = 𝒯Nf (subst _∈𝒯 (id-wk 0 A') (Ah Id))

lamLemma : ∀{Θ Γ t A B i} {j : Size< i}
         → (td : ⟨ j ⟩ Θ ∷ Γ # A ⊢ t ∶ B)
         → ⊧Tm {i = j} td
         → ⊧Ty (proj₂ (invert-ctx-aux (invert-ctx-tm td)))
         → ⊧Tm {i = i} (lam {i = i} {j = j} td)
lamLemma {Θ} {Γ} {t} {A} {B} {i} {j} td ht hA {Δ} {σ} {ρ} ρp mc rel =

  tm-irrel𝒯 refl ((Eval-fun (eLam (invert-eval-Π1 e) (↘tm1 dd))
  (↘tm1 (proj₂ lam-m ρp)))) refl (sym pi-eq) pi (∈ty (proj₂ lam-m ρp))
    ((uhm'' (𝒯Nf (subst _∈𝒯 (id-wk 0 A') (Ah Id))) nfB nfd Ah Bh qh refl))
    ((wit (∈tm (proj₂ lam-m ρp)))) aux

  where
    lam-m = models (lam {i = i} {j = j} td)

    azd = asder (proj₁ lam-m ρp)

    A' = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.resA azd ; B' = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.resB azd
    Ah = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.Ah azd ; Bh = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.hyp azd
    nfA = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.nfA azd ; nfB = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.nfB azd
    e = ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯.ev1 azd

    pi = tPi nfB Ah Bh
    m-A : Θ ∷ Γ ⊧ A
    m-A = models-ty (proj₂ (invert-ctx-aux (invert-ctx-tm td)))
    dd = proj₂ (models td) (⊧sh Θ m-A ρp)
    d = res dd
    nfd = nfEval (↘tm1 dd)
    lam-p = wit (∈tm (proj₂ lam-m ρp))

    pi-eq : resT (proj₂ lam-m ρp) ≡ Π A' B'
    pi-eq = Eval-fun (↘ty (proj₂ lam-m ρp)) e

    lam-eq : res (proj₂ lam-m ρp) ≡ Lam A' d
    lam-eq = Eval-fun (↘tm1 (proj₂ lam-m ρp)) (eLam (invert-eval-Π1 e) (↘tm1 dd))

    p : P (El𝒯 pi) (Lam A' d)
    p = sameTerm≃' pi-eq lam-eq (∈ty (proj₂ lam-m ρp)) pi
      (wit (∈tm (proj₂ lam-m ρp)))

    qh : ∀{a w} (pa : P (El𝒯 (Ah w)) a) → d [ w , a ]∈ El𝒯 (∈t (Bh pa))
    qh {a} {w} pa = record { ↘s = ed ; ∈tm = ∈in pp }
      where
        aucs = proj₂ (models td) (cExt (cWk {w = w} ρp)
                   ⟨ ≡Eval (wk-subst A) refl (wkEval (invert-eval-Π1 e))
                   ∣ Ah w ∣ (∈in pa) ⟩)
        ed : Eval sub d ((Id · w) , a) ↘ res aucs
        ed = sub-comm {t} (↘tm1 dd) (≡Eval (≈ˢsub (≈ˢcons
          (eq-dot (≈ˢsym sub-id-R))) t) refl (↘tm1 aucs))
        pp : P (El𝒯 (∈t (Bh pa))) (res aucs)
        pp = sameTerm𝒯≃ (Eval-fun (sub-comm {B} (invert-eval-Π2 e)
          (≡Eval (≈ˢsub (≈ˢcons (eq-dot (≈ˢsym sub-id-R))) B) refl (↘ty aucs)))
            (↘s (Bh pa))) (∈ty aucs) (∈t (Bh pa)) (wit (∈tm aucs))
    h : ∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Δ → (p₁ : P (El𝒯 (Ah w)) a)
        → Θ ∷ Γ' ⊢ s ∶ wk (sub A σ) w ® Ah w ∋ p₁
        → Θ ∷ Γ' ⊢ sub t (sh σ) [ w , s ]ₛ ∶ sub B (sh σ) [ w , s ]ₛ
                 ® ∈t (Bh p₁) ∋ wit (∈tm (qh p₁))
    h {w} {Γ'} {s} {a} wp p relsa =
      tm-irrel𝒯 (sym (trans (sub-comp t) (≈ˢsub (≈ˢcons (eq-dot sub-id-R)) t)))
       (Eval-fun (sub-comm {t} {_} {d} {sh ρ} {Id · w , a} (↘tm1 dd)
         (≡Eval (≈ˢsub (≈ˢcons (eq-dot (≈ˢsym sub-id-R))) t) refl
           (↘tm1 (proj₂ (models td) (cExt (cWk ρp) aa)))))
         (↘s (qh p))) (sym (trans (sub-comp B) (≈ˢsub (≈ˢcons (eq-dot sub-id-R)) B)))
       (Eval-fun (sub-comm {B} {_} {B'} {sh ρ} {Id · w , a}
         (invert-eval-Π2 e) (≡Eval (≈ˢsub (≈ˢcons (eq-dot (≈ˢsym sub-id-R))) B)
           refl (↘ty (proj₂ (models td) (cExt (cWk ρp) aa))))) (↘s (Bh p)))
           (∈ty (proj₂ (models td) (cExt (cWk ρp) aa)))
       (∈t (Bh p)) (wit (∈tm (proj₂ (models td) (cExt (cWk ρp) aa))))
        (wit (∈tm (qh p))) aucs
      where
        aa : _ ∈⟦ A ⟧ (ρ · w)
        aa = ⟨ ≡Eval (wk-subst A) refl (wkEval (invert-eval-Π1 e)) ∣ Ah w ∣ (∈in p) ⟩
        aucs = ht {Γ'} (cExt (cWk {w = w} ρp) aa) mc
                  (#® (·® rel wp)
                    (tm-irrel𝒯 refl refl (wk-subst A) refl
                    (Ah w) (inT aa) p (wit (nn aa)) relsa))

    Ad = proj₂ (invert-ctx-aux (invert-ctx-tm td))
    Cd = proj₁ (invert-ctx-aux (invert-ctx-tm td))
    sub-A = ⊢sub-ty Ad (derₛ rel)

    aux = lamLemma' {Θ} {Δ} {A} {B} {t} {σ} {A'} {B'} {d} nfB nfd Ah Bh qh p h
      (ty-irrel𝒯 refl (Eval-fun (↘t1 (models-ty Ad ρp)) (≡Eval refl (sym (id-wk 0 _))
       (invert-eval-Π1 e))) (∈ty (models-ty Ad ρp)) (Ah Id) (hA ρp mc rel))
       (⊢sub-tm td (⊢Cons (⊢Wk (derₛ rel) (⊢Up ⊢Id sub-A))
         (bound (⊢# (⊢sub-ctx Cd (derₛ rel)) sub-A) (≡↦ (wk-subst A) here))))
