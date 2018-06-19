module Semantics.Soundness.TermSoundness.Application where

open import Semantics.Soundness.LogicalRelation
open import Semantics.Soundness.SubLogicalRelation.Definition
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
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

appLemmy : ∀{Θ Δ t s σ A B A' B' f a b} {nfB : Nf B'}
         → Θ ∷ Δ # sub A σ ⊢ sub B (sh σ)
         → (Ah : (w : Wk) → wk A' w ∈𝒯)
         → (Bh : ∀{a w} → P (El𝒯 (Ah w)) a → B' [ w , a ]∈𝒯)
         → let typ = tPi nfB Ah Bh
               tys = Ah Id
            in (p : P (El𝒯 typ) f) (q : P (El𝒯 tys) a) (pq : P (El𝒯 (∈t (Bh q))) b)
         → Θ ∷ Δ ⊢ sub t σ ∶ Π (sub A σ) (sub B (sh σ)) ® typ ∋ p
         → Θ ∷ Δ ⊢ sub s σ ∶ sub A σ ® tys ∋ q
         → Θ ∷ Δ ⊢ sub A σ ® Ah Id
         → Θ ∷ Δ ⊢ sub B (σ , sub s σ) ® ∈t (Bh q)
         → f ● a ↘ b
         → Θ ∷ Δ ⊢ App (sub t σ) (sub s σ) ∶ sub B (σ , sub s σ)
                 ® ∈t (proj₂ (asder2 typ) q) ∋ pq
appLemmy {Θ} {Δ} {t} {s} {σ} {A} {B} {A'} {B'} {.(Lam _ _)} {a} Bsh Ah Bh pf q pq
  ht@(®𝒯λ {t = tee} {d} {S = S} {T} qh .(tPi _ Ah Bh) .pf convT relS conv h) hs hA hB (●β x y) = goal
  where
    cc : Θ ∷ Δ ⊢ App (sub t σ) (sub s σ) ∼ App (Lam S tee) a ∶ ((sub B (sh σ)) [ sub s σ ])
    cc = ∼compApp conv (convert-®𝒯-tm {ty = Ah Id} hs) Bsh
    SS : Θ ∷ Δ ⊢ S
    SS = der-tyₜ {ty = Ah Id} relS
    b0 = hasNe (El𝒯 (Ah (Up Id))) (neBound {0})
    cdcd : ⊢ Θ ∷ Δ
    cdcd = invert-ctx-ty SS
    SA' : Θ ∷ Δ ⊢ S ∼ wk A' Id
    SA' = (convert-® {Θ} {Δ} {S} {_} {Ah Id} relS)
    SA : Θ ∷ Δ ⊢ S ∼ A'
    SA = ≡ty∼ refl (id-wk 0 _) SA'
    b0rel : Θ ∷ Δ # S ⊢ Bound 0 ∶ S ↑ ® Ah (Up Id) ∋ b0
    b0rel = allNe𝒯 (Ah (Up Id)) neBound (⊢wk-ty-∼ SA (⊢Up ⊢Id SS))
      (∼refl (bound (⊢# (invert-ctx-ty SS) SS) here))

    ass = h (⊢Up ⊢Id SS) b0 b0rel
    ass' : Θ ∷ Δ # S ⊢ tee ∶ T ® ∈t (Bh b0) ∋ wit (∈tm (qh b0))
    ass' = ≡preserv-tm {ty = ∈t (Bh b0)} (sym (id-sub' T 1)) (sym (id-sub' tee 1)) ass
    tee∼ : Θ ∷ Δ # S ⊢ tee ∼ da (qh b0) ∶ T
    tee∼ = convert-®𝒯-tm {ty = ∈t (Bh b0)} ass'
    tee∼' : Θ ∷ Δ # S ⊢ tee ∼ d ∶ T
    tee∼' = ≡tm∼ refl (Eval-fun (≡Eval (id-sub' d 1) refl
      (↘s (qh b0))) (nfSelf (proj-lam (proj₁ pf)))) refl tee∼
    tmS = tySameSzLemmaR SA (β-Redex-Tm-Lam-A x)
    teed : Θ ∷ ◇ # S ⊢ tee ∶ T
    teed = shrink-tm (derₜ {ty = ∈t (Bh b0)} ass') hc
        (tyCloLemma _ (eq-lemma-tm1 tee∼') hc htee) htee
      where hc = (tt ,, tmS)
            htee = (tmSameSzLemmaR tee∼' (β-Redex-Tm-Lam-t x))
    seed' : Θ ∷ Δ ⊢ a ∶ S
    seed' = coe (eq-lemma-tm2 (convert-®𝒯-tm {ty = Ah Id} hs))
      (∼trans (convert-® {ty = Ah Id} hA) (∼symm SA'))
    seed : Θ ∷ ◇ ⊢ a ∶ S
    seed = shrink-tm seed' tt tmS (β-Redex-Tm-s x)

    rr : Θ ∷ Δ ⊢ a ∶ wk S Id ® Ah Id ∋ q
    rr = ∼preservation-tm {ty = Ah Id} (∼trans (convert-® {ty = Ah Id} hA)
      (≡ty∼ refl (sym (id-wk 0 _)) (∼symm (convert-® {ty = Ah Id} relS))))
        (convert-®𝒯-tm {ty = Ah Id} hs) hs
    cc' : Θ ∷ Δ ⊢ App (Lam S tee) a ∼ tee [ a ] ∶ (T [ a ])
    cc' = ∼β cdcd teed seed
    goal'' : Θ ∷ Δ ⊢ tee [ Id , a ]ₛ ∶ T [ Id , a ]ₛ ® ∈t (Bh q) ∋ wit (∈tm (qh q))
    goal'' = h ⊢Id q rr
    goal' : Θ ∷ Δ ⊢ tee [ a ] ∶ T [ a ] ® ∈t (Bh q) ∋ pq
    goal' = tm-irrel𝒯 (≈ˢsub (≈ˢcons sub-id-R) tee) (Eval-fun (↘s (qh q))
      (≡Eval (sym (≈ˢsub (≈ˢcons sub-id-R) d)) refl y)) (≈ˢsub (≈ˢcons sub-id-R) T)
        refl (∈t (Bh q)) (∈t (Bh q)) (wit (∈tm (qh q))) pq goal''
    tyty' : Θ ∷ Δ ⊢ sub B (σ , sub s σ) ∼ sub T (Id , a)
    tyty' = ∼trans (convert-® {ty = ∈t (Bh q)} hB)
      (∼symm (convert-®𝒯-tm-ty (∈t (Bh q)) goal'))
    goal : Θ ∷ Δ ⊢ App (sub t σ) (sub s σ) ∶ sub B (σ , sub s σ) ® ∈t (Bh q) ∋ pq
    goal = ∼preservation-tm {ty = ∈t (Bh q)} (∼symm tyty')
        (∼trans (∼symm cc') (∼symm (∼coe cc (≡ty∼ (sym (trans (sub-comp B)
          (≈ˢsub (≈ˢcons sub-id-R) B))) refl tyty')))) goal'

appLemmy Bsh Ah Bh p q pq (®𝒯Ne () x₃ _) hs hA hB (●β x x₁)
appLemmy {B = B} Bsh Ah Bh p q pq ht hs hA hB (●Ne x) =
  tm-irrel𝒯 refl refl refl refl (∈t (Bh q)) (∈t (Bh q))
    (hasNe (El𝒯 (∈t (Bh q))) x) pq aux
  where
    tyeq = convert-® {ty = ∈t (Bh q)} hB
    eqeq' = ∼compApp (convert-®𝒯-tm {ty = tPi _ Ah Bh} ht)
                     (convert-®𝒯-tm {ty = Ah Id} hs) Bsh
    eqeq = ≡tm∼ refl refl (trans (sub-comp B) (≈ˢsub (≈ˢcons sub-id-R) B)) eqeq'
    aux = allNe𝒯 (∈t (Bh q)) x tyeq eqeq


open ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈𝒯
open import Function

extract : ∀{s s' A ρ} → (x : ⟦ s ⟧≃⟦ s' ⟧ ρ ∈tm⟦ A ⟧) → res x ∈⟦ A ⟧ ρ
extract record { ∈ty = ty ; ↘ty = ety ; ∈tm = tm } = ⟨ ety ∣ ty ∣ tm ⟩

same-ap : ∀{t s t' s' ts ts'}
        → Eval App t s ↘ ts → Eval t ↘ t' → Eval s ↘ s' → t' ● s' ↘ ts' → ts ≡ ts'
same-ap (eApp e e' x) et es ap rewrite Eval-fun e et | Eval-fun e' es = ●-fun x ap

appLemmy' : ∀{Θ Γ A B t s i} {j k l : Size< i}
          → (td : ⟨ j ⟩ Θ ∷ Γ ⊢ t ∶ Π A B)
          → ⊧Tm td
          → (sd : ⟨ k ⟩ Θ ∷ Γ ⊢ s ∶ A)
          → ⊧Tm sd
          → (Bd : ⟨ l ⟩ Θ ∷ Γ # A ⊢ B)
          → ⊧Ty (proj₂ (invert-ctx-aux (invert-ctx-ty Bd)))
          → ⊧Ty Bd
          → ⊧Tm (app td sd Bd)
appLemmy' {Θ} {Γ} {A} {B} {t} {s} td ht sd hs Bd hA hB {Δ} {σ} {ρ} ρp mc rel = goal
  where
    f = res (proj₂ (models td) ρp)
    a = res (proj₂ (models sd) ρp)
    zz = asder (proj₁ (models td) ρp)
    typ : Π (resA zz) _ ∈𝒯
    typ = tPi (nfB zz) (Ah zz) (hyp zz)
    p = wit (∈tm (proj₂ (models td) ρp))
    q = wit (∈tm (proj₂ (models sd) ρp))
    typ' = (∈ty (proj₂ (models td) ρp))
    tys' = (∈ty (proj₂ (models sd) ρp))

    pieq = (Eval-fun (↘ty (proj₂ (models td) ρp)) (ev1 zz))
    aeq = (Eval-fun (↘ty (proj₂ (models sd) ρp))
      (invert-eval-Π1 (≡Eval refl (cong₂ Π (sym (id-wk 0 _)) refl) (ev1 zz))))

    pee : P (El𝒯 typ) f
    pee = sameTerm𝒯≃ pieq (∈ty (proj₂ (models td) ρp)) typ p
    qee : P (El𝒯 (Ah zz Id)) a
    qee = sameTerm𝒯≃ aeq (∈ty (proj₂ (models sd) ρp)) (Ah zz Id) q
    appe = proj₂ pee qee
    relt : Θ ∷ Δ ⊢ sub t σ ∶ Π (sub A σ) (sub B (sh σ)) ® typ ∋ pee
    relt = tm-irrel𝒯 refl refl refl pieq typ' typ p pee (ht ρp mc rel)
    relsa : Θ ∷ Δ ⊢ sub s σ ∶ sub A σ ® Ah zz Id ∋ qee
    relsa = tm-irrel𝒯 refl refl refl aeq tys' (Ah zz Id) q qee (hs ρp mc rel)
    relA : Θ ∷ Δ ⊢ sub A σ ® Ah zz Id
    relA = ty-irrel𝒯 refl (Eval-fun (↘t1 (models-ty (proj₂ (invert-ctx-aux
      (invert-ctx-ty Bd))) ρp)) ((invert-eval-Π1 (≡Eval refl
        (cong₂ Π (sym (id-wk 0 _)) refl) (ev1 zz)))))
      (∈ty (models-ty (proj₂ (invert-ctx-aux (invert-ctx-ty Bd))) ρp))
        (Ah zz Id) (hA ρp mc rel)

    in-a = (extract (proj₂ (models sd) ρp))

    relsa' : Θ ∷ Δ ⊢ sub s σ ∶ sub A σ ® inT in-a ∋ wit (nn in-a)
    relsa' = tm-irrel𝒯 refl refl refl (Eval-fun (≡Eval refl (sym (id-wk 0 _))
      (invert-eval-Π1 (ev1 zz))) (ev in-a)) (Ah zz Id) (inT in-a) qee
        (wit (nn in-a)) relsa

    hbhb = (hB (cExt ρp (extract (proj₂ (models sd) ρp))) mc (#® rel relsa'))

    e1 : (sub B (sh ρ)) [ Id , a ]↘ resT (models-ty Bd (cExt ρp in-a))
    e1 = ≡Eval (sym (trans (sub-comp B) (≈ˢsub (≈ˢcons sub-id-R) B))) refl
      (↘t1 (models-ty Bd (cExt ρp in-a)))

    e2 : (resB zz) [ Id , a ]↘ Fa (hyp zz qee)
    e2 = ≡Eval (≈ˢsub (≈ˢcons sub-id-R) (resB zz)) refl (↘s (hyp zz qee))

    e2' : sub B (sh ρ) [ Id , a ]↘ Fa (hyp zz qee)
    e2' = ≡Eval (sym (sub-comp B)) refl
      (sub-uncomm {B} (invert-eval-Π2 (ev1 zz)) e2)

    relB : Θ ∷ Δ ⊢ sub B (σ , sub s σ) ® ∈t (hyp zz qee)
    relB = ty-irrel𝒯 refl (Eval-fun e1 e2')
      (∈ty (models-ty Bd (cExt ρp in-a))) (∈t (hyp zz qee)) hbhb

    subA = (⊢sub-ty (invert-type sd) (derₛ rel))

    aux = appLemmy {Θ} {Δ} {t} {s} {σ} {A} {B} {_} {_} {f} {a} {_}
      (⊢sub-ty Bd (⊢Cons (⊢Wk (derₛ rel) (⊢Up ⊢Id subA))
        (bound (⊢# (⊢sub-ctx (invert-ctx-tm sd) (derₛ rel)) subA) (≡↦ (wk-subst A) here))))
        (Ah zz) (hyp zz) pee qee (wit (∈tm appe))
      relt relsa relA relB (≡App (id-wk 0 _) refl (↘ap appe))

    apd = proj₂ (models (app td sd Bd)) ρp

    e3' : Eval sub (sub B (sh ρ)) (Id , sub s ρ) ↘ resT apd
    e3' = ≡Eval (trans (sub-comp B) (sym (trans (sub-comp B)
      (sym (≈ˢsub (≈ˢtrans (sub-comp-R {s} {Id} {ρ})
      (≈ˢcons (≈ˢtrans sub-id-L (≈ˢsym sub-id-R)))) B))))) refl (↘ty apd)

    e3 : Eval sub (sub B (sh ρ)) (Id , a) ↘ resT apd
    e3 = sub-comm3 {sub B (sh ρ)} 0 e3' (↘tm1 (proj₂ (models sd) ρp))

    eq : Fa (hyp zz qee) ≡ resT apd
    eq = Eval-fun e2' e3

    goal : Θ ∷ Δ ⊢ App (sub t σ) (sub s σ) ∶ sub (B [ s ]) σ
                 ® ∈ty (proj₂ (models (app td sd Bd)) ρp)
                 ∋ wit (∈tm (proj₂ (models (app td sd Bd)) ρp))
    goal = tm-irrel𝒯 refl (sym (same-ap (↘tm1 (proj₂ (models (app td sd Bd)) ρp))
      (≡Eval refl (sym (id-wk 0 _)) (↘tm1 (proj₂ (models td) ρp)))
      (↘tm1 (proj₂ (models sd) ρp)) (↘ap appe)))
      (sym (trans (sub-comp B) (≈ˢsub (≈ˢtrans (sub-comp-R {s} {Id} {σ})
        (≈ˢcons sub-id-L)) B))) eq (∈t (hyp zz qee))
      (∈ty (proj₂ (models (app td sd Bd)) ρp)) (wit (∈tm appe))
        (wit (∈tm (proj₂ (models (app td sd Bd)) ρp))) aux
