module Noninterference where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List)

open import Machine
open import Defs
open import Imp

-- Low-projection equality for two states.
data _≈ₗ[_]_ : {∣V∣ : ℕ} → Vec ℕ ∣V∣ → level-assignment ∣V∣ → Vec ℕ ∣V∣ → Set where
  ≈ₗ-nil    : [] ≈ₗ[ [] ] []
  ≈ₗ-cons-L : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {σ σ′ : State ∣V∣}
                (v : ℕ)
            → σ ≈ₗ[ dom ] σ′
            → (v ∷ σ) ≈ₗ[ low ∷ dom ] (v ∷ σ′)
  ≈ₗ-cons-H : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {σ σ′ : State ∣V∣}
                (v v′ : ℕ)
            → σ ≈ₗ[ dom ] σ′
            → (v ∷ σ) ≈ₗ[ high ∷ dom ] (v′ ∷ σ′)

-- noninterference property

noninterference : {∣V∣ : ℕ} → level-assignment ∣V∣ → Stmt ∣V∣ → Set
noninterference {∣V∣} level stmt =
  ∀ {σ₀ σ₀′ σ₂ σ₂′ : State ∣V∣}
    → σ₀ ≈ₗ[ level ] σ₂
    → ⟨ σ₀ , stmt ⟩⇓ σ₀′
    → ⟨ σ₂ , stmt ⟩⇓ σ₂′
    → σ₀′ ≈ₗ[ level ] σ₂′

noninterferenceₘ : ∀ {∣V∣ : ℕ} → level-assignment ∣V∣ → List (Instr ∣V∣) → Set
noninterferenceₘ {∣V∣} level prog =
  ∀ {M₀ M₁ : Memory ∣V∣} {C₀ C₁ : Config ∣V∣}
    → M₀ ≈ₗ[ level ] M₁
    → [ init-config M₀ , prog ]halts-with C₀
    → [ init-config M₁ , prog ]halts-with C₁
    → Config.mem C₀ ≈ₗ[ level ] Config.mem C₁
