module Semantics.Soundness.TermSoundness.Pi where

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
open _[_,_]
open _∈_
open _∈⟦_⟧_
open SemTy
open ⟦Π_∣_⟧≃⟦Π_∣_⟧_∈_∣_

open import Size

upi : ∀{Θ Γ A B i} {j k : Size< i}
    → (Ad : ⟨ j ⟩ Θ ∷ Γ ⊢ A ∶ U)
    → (Bd : ⟨ k ⟩ Θ ∷ Γ # A ⊢ B ∶ U)
    → ⊧Tm Ad → ⊧Tm Bd → ⊧Tm {i = i} (U-Π Ad Bd)
upi {Θ} {Γ} {A} {B} Ad Bd hA hB {Δ} {σ} {ρ} ρp mc rel =
  tm-irrel𝒯 refl (Eval-fun (↘tm1 upi-tm) (↘tm1 (proj₂ (models (U-Π Ad Bd)) ρp)))
  refl (Eval-fun (nfSelf nfU) (↘ty (proj₂ (models (U-Π Ad Bd)) ρp)))
    tU (∈ty (proj₂ (models (U-Π Ad Bd)) ρp)) pp
    (wit (∈tm (proj₂ (models (U-Π Ad Bd)) ρp))) goal
  where
    upi-m = (models (U-Π Ad Bd))
    upi-tm = proj₂ upi-m ρp
    zz = asdeur upi-tm
    A' = resA zz ; B' = resB zz ; Ah = hypA zz ; Bh = hypB zz
    e = ev1 zz ; e1 = invert-eval-Π1 e ; e2 = invert-eval-Π2 e

    pp : P (El𝒯 tU) (res upi-tm)
    pp = sameT (Eval-fun (↘ty upi-tm) (nfSelf nfU))
      (∈ty upi-tm) tU (wit (∈tm upi-tm))

    goal' : Θ ∷ Δ ⊢ Π (sub A σ) (sub B (sh σ)) ®𝒰 uPi (nfresB zz) Ah Bh
    goal' = ®𝒰Π (∼refl (El (⊢sub-tm (U-Π Ad Bd) (derₛ rel))))
      (ty-irrel𝒰 refl (Eval-fun (↘tm1 ma) (≡Eval refl (sym (id-wk 0 _))
        (invert-eval-Π1 (ev1 zz)))) pa (Ah Id) (proj₁ (proj₂ ha))) h
      where
        ma = (proj₂ (models Ad) ρp)
        pa : P (El𝒯 tU) (res ma)
        pa = sameTerm≃' ((Eval-fun (↘ty ma) (nfSelf nfU))) refl (∈ty ma) tU (wit (∈tm ma))
        ha : Θ ∷ Δ ⊢ sub A σ ∶ U ® tU ∋ pa
        ha = tm-irrel𝒯 refl refl refl (Eval-fun (↘ty ma) (nfSelf nfU)) (∈ty ma)
          tU (wit (∈tm ma)) pa (hA ρp mc rel)
        h : ∀{w Γ' s a} → Θ ∷ Γ' ⊢ᵣ w ∶ Δ → (p : P (El𝒰 (Ah w)) a)
          → Θ ∷ Γ' ⊢ s ∶ wk (sub A σ) w ®𝒰 Ah w ∋ p
          → Θ ∷ Γ' ⊢ sub B (sh σ) [ w , s ]ₛ ®𝒰 ∈t (Bh p)
        h {w} {Γ'} {s} {a} wp p relsa =
          ty-irrel𝒰 (sym (trans (sub-comp B) (≈ˢsub (≈ˢcons (eq-dot sub-id-R)) B)))
            (Eval-fun (↘tm1 Ba) (≡Eval ((≈ˢsub (≈ˢcons (eq-dot sub-id-R)) B)) refl
              (sub-uncomm {B} {_} {Fa (Bh p)} {sh ρ} {Id · w , a}
                (invert-eval-Π2 (ev1 zz)) (↘s (Bh p))))) (wit pu) (∈t (Bh p))
                  (proj₁ (proj₂ aux'))
          where
            aa = ⟨ ≡Eval (wk-subst A) refl (wkEval {w = w} (invert-eval-Π1 (ev1 zz)))
                 ∣ (𝒰⊆𝒯 (Ah w)) ∣ (∈in p) ⟩
            relsa' : Θ ∷ Γ' ⊢ s ∶ sub A (σ · w) ®𝒰 Ah w ∋ wit (nn aa)
            relsa' = tm-irrel𝒰 refl (wk-subst A) refl (Ah w) (Ah w) p (wit (nn aa)) relsa
            Ba = (proj₂ (models Bd) (cExt (cWk ρp) aa))
            pu : res Ba ∈ El𝒯 tU
            pu = ∈in (sameTerm≃' (Eval-fun (↘ty Ba) (nfSelf nfU)) refl
              (∈ty Ba) tU (wit (∈tm Ba)))
            aux : Θ ∷ Γ' ⊢ sub B (σ · w , s) ∶ U
                         ® ∈ty (proj₂ (models Bd) (cExt (cWk ρp) aa))
                         ∋ wit (∈tm (proj₂ (models Bd) (cExt (cWk ρp) aa)))
            aux = hB (cExt (cWk ρp) aa) mc (#® (·® rel wp) relsa')
            aux' : Θ ∷ Γ' ⊢ sub B (σ · w , s) ∶ U ® tU ∋ wit pu
            aux' = tm-irrel𝒯 refl refl refl (Eval-fun (↘ty Ba) (nfSelf nfU))
              (∈ty Ba) tU (wit (∈tm Ba)) (wit pu) aux

    convA : Θ ∷ Δ ⊢ sub A σ ∼ A' ∶ U
    convA = ≡tm∼ refl (Eval-fun (↘tm1 (proj₂ (models Ad) ρp)) e1) refl
      (convert-®𝒯-tm {ty = ∈ty (proj₂ (models Ad) ρp)} (hA ρp mc rel))
    cd : ⊢ Θ ∷ Δ
    cd = invert-ctx-tm∼ convA

    Adσ = eq-lemma-tm1 convA

    kk : Θ ∷ Δ # sub A σ ⊢ sub A (σ · Up Id) ∼ wk (resA zz) (Up Id)
    kk = ≡ty∼ (wk-subst A) refl (⊢wk-ty-∼ (∼El convA) (⊢Up ⊢Id (El Adσ)))

    b0rel = allNe𝒰 {Θ} {Δ # sub A σ} {sub A (σ · Up Id)}
          (Ah (Up Id)) (neBound {0})
          kk (∼refl (bound (⊢# cd (El Adσ)) (≡↦ (wk-subst A) here)))

    b0 = ⟨ (≡Eval (wk-subst A) refl (wkEval {w = Up Id} e1))
         ∣ (𝒰⊆𝒯 (Ah (Up Id)))
         ∣ (∈in (hasNe (El𝒰 (Ah (Up Id))) neBound)) ⟩

    hB0 = hB {Δ # sub A σ} {sh σ} {sh ρ} (cExt (cWk {w = Up Id} ρp) b0) mc
        (#® (·® rel (⊢Up ⊢Id (El Adσ))) b0rel)

    convB' : Θ ∷ Δ # sub A σ ⊢ sub B (sh σ) ∼ res (proj₂ (models Bd) (cExt (cWk ρp) b0)) ∶ U
    convB' = convert-®𝒯-tm {ty = ∈ty (proj₂ (models Bd) (cExt (cWk ρp) b0))} hB0

    convB : Θ ∷ Δ # sub A σ ⊢ sub B (sh σ) ∼ B' ∶ U
    convB = ≡tm∼ refl (Eval-fun (↘tm1 (proj₂ (models Bd) (cExt (cWk ρp) b0))) e2) refl convB'

    conv : Θ ∷ Δ ⊢ Π (sub A σ) (sub B (sh σ)) ∼ Π A' B' ∶ U
    conv = ∼compPi convA convB

    goal'' : Θ ∷ Δ ⊢ Π (sub A σ) (sub B (sh σ)) ®𝒰 pp
    goal'' = ty-irrel𝒰 refl (Eval-fun (ePi e1 e2) (↘tm1 upi-tm))
      (uPi (nfresB zz) Ah Bh) pp goal'
    goal : Θ ∷ Δ ⊢ Π (sub A σ) (sub B (sh σ)) ∶ U ® tU ∋ pp
    goal = (∼refl (U cd)) ,, goal'' ,, ≡tm∼ refl (Eval-fun (ePi e1 e2)
      (↘tm1 upi-tm)) refl conv
