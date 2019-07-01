module Defs where

open import Data.Vec using (Vec)

data SecurityLevel : Set where
  low high : SecurityLevel

data _⊑_ : SecurityLevel → SecurityLevel → Set where
  ⊑-refl : (sl : SecurityLevel) → sl ⊑ sl
  ⊑-sub : low ⊑ high

_⊔_ : SecurityLevel → SecurityLevel → SecurityLevel
sl ⊔ low = sl
sl ⊔ high = high

level-assignment = Vec SecurityLevel
