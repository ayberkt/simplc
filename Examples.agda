module Examples where

open import Data.Vec  using (_∷_; [])
open import Data.Fin  renaming (suc to S; zero to Z)
open import Data.Empty using (⊥)

open import Defs
open import SecurityTypeSystem
open import Imp

dom : level-assignment 2
dom = low ∷ high ∷ []

-- Example of a program in which a low-sensitivity data is written to a
-- high-sensitivity one.
example₁ : Stmt 2
example₁ = S Z := ref Z

-- Observe that this is typable.
_ : high ⊢[ dom ] example₁
_ = T-ass (T-ref _) (⊑-refl high)

-- Another example in which the flow direction is the inverse of example₁.
example₂ : Stmt 2
example₂ = Z := ref (S Z)

-- Proof that example₂ is not typable.
ill-typed₂ : ∀ ℓ → ℓ ⊢[ dom ] example₂ → ⊥
ill-typed₂ low (T-ass (T-ref .(S Z)) ())
ill-typed₂ high (T-ass (T-ref .(S Z)) ())
