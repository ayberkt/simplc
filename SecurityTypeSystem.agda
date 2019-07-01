module SecurityTypeSystem where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Data.Fin using (Fin)

_[_] : ∀ {ℓ} {A : Set ℓ} {n} → Vec A n → Fin n → A
dom [ i ] = lookup i dom

open import Defs
open import Imp

data ⊢[_]_∈_ {∣V∣ : ℕ} (dom : level-assignment ∣V∣) : Expr ∣V∣ → SecurityLevel → Set where
  T-ref : ∀ (i : Fin ∣V∣) → ⊢[ dom ] (ref i) ∈ (dom [ i ])
  T-lit : ∀ n → ⊢[ dom ] (lit n) ∈ low
  T-add : ∀ {e₀ e₁ : Expr ∣V∣} {l₀ l₁ : SecurityLevel}
          → ⊢[ dom ] e₀ ∈ l₀
          → ⊢[ dom ] e₁ ∈ l₁
          → ⊢[ dom ] (e₀ + e₁) ∈ (l₀ ⊔ l₁)

data _⊢[_]_ {∣V∣ : ℕ} (pc : SecurityLevel) (dom : level-assignment ∣V∣) : Stmt ∣V∣ → Set where
  T-skip : pc ⊢[ dom ] skip
  T-seq : ∀ {stmt₀ stmt₁ : Stmt ∣V∣}
        → pc ⊢[ dom ] stmt₀
        → pc ⊢[ dom ] stmt₁
        → pc ⊢[ dom ] (seq stmt₀ stmt₁)
  T-ass : ∀ {l : SecurityLevel} {i : Fin ∣V∣} {e : Expr ∣V∣}
        → ⊢[ dom ] e ∈ l
        → (l ⊔ pc) ⊑ (dom [ i ])
        → pc ⊢[ dom ] (i := e)
  T-if : ∀ {l : SecurityLevel} {cond : Expr ∣V∣} {s₀ s₁ : Stmt ∣V∣}
       → ⊢[ dom ] cond ∈ l
       → (l ⊔ pc) ⊢[ dom ] s₀
       → (l ⊔ pc) ⊢[ dom ] s₁
       → pc ⊢[ dom ] (if cond then s₀ else s₁)
  T-while : ∀ {l : SecurityLevel} {cond : Expr ∣V∣} {bdy : Stmt ∣V∣}
          → ⊢[ dom ] cond ∈ l
          → (l ⊔ pc) ⊢[ dom ] bdy
          → pc ⊢[ dom ] (while cond ⁅ bdy ⁆)
