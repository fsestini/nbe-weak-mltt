module Semantics.Soundness.SubLogicalRelation where

-- open import Data.Nat hiding (_≥_)
-- open import Data.Maybe
-- open import Syntax renaming (_,_ to Cons)
-- open import Syntax.Renaming
-- open import Semantics.Domain renaming (B to Bnd)
-- open import Data.Product
-- open import Data.Unit
-- open import Data.Empty
-- open import Semantics.Type
-- -- open import Semantics.Environment
-- open import Semantics.Soundness.LogicalRelation

-- infix 4 _∷_⊢ₛ_®_∶_
-- data _∷_⊢ₛ_®_∶_ (Θ : Ctxtₗ) : Ctxt → Subst → DSubst → Ctxt → Set where
--   ◇® : ∀{Γ σ ρ} → Θ ∷ Γ ⊢ₛ σ ∶ ◇ → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ ◇
--   #® : ∀{Γ Δ A σ ρ t} {a : D C}
--      → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ
--      → Θ ∷ ◇ ⊢ t ∶ A
--      → Θ ∷ Γ ⊢ A ∶ t ® a
--      → Θ ∷ Γ ⊢ₛ Cons σ t ® sCons ρ a ∶ Δ # A
--   ●® : ∀{Γ Δ A σ ρ} → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → Θ ∷ Γ # A ⊢ₛ σ ● ® sDot ρ ∶ Δ # A

-- derₛ : ∀{Θ Γ Δ σ ρ} → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → Θ ∷ Γ ⊢ₛ σ ∶ Δ
-- derₛ (◇® σ) = σ
-- derₛ (#® rels t relt) = cons (derₛ rels) t
-- derₛ (●® rel) = dot (derₛ rel)

-- cl : ∀{Θ Γ Δ σ ρ} → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → Cl σ
-- cl (◇® id) = em
-- cl (#® rels t _) = ex (cl rels) (tyClosed t)
-- cl (●® rels) = dt (cl rels)
