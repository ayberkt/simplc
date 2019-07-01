module Imp where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat  using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin  using (Fin)
open import Data.Vec  using (Vec; lookup; _[_]≔_)

data Expr (∣V∣ : ℕ) : Set where
  ref : Fin ∣V∣ → Expr ∣V∣
  lit : ℕ → Expr ∣V∣
  _+_ : Expr ∣V∣ → Expr ∣V∣ → Expr ∣V∣

data Stmt (∣V∣ : ℕ) : Set where
  skip          : Stmt ∣V∣
  seq           : Stmt ∣V∣ → Stmt ∣V∣ → Stmt ∣V∣
  _:=_          : Fin ∣V∣ → Expr ∣V∣ → Stmt ∣V∣
  if_then_else_ : Expr ∣V∣ → Stmt ∣V∣ → Stmt ∣V∣ → Stmt ∣V∣
  while_⁅_⁆     : Expr ∣V∣ → Stmt ∣V∣ → Stmt ∣V∣

State = Vec ℕ

data eval {∣V∣ : ℕ} (σ : State ∣V∣) : Expr ∣V∣ → ℕ → Set where
  E-ref : ∀ i → eval σ (ref i) (lookup i σ)
  E-lit : ∀ n → eval σ (lit n) n
  E-add : ∀ {e e′ : Expr ∣V∣} {n n′ : ℕ}
        → eval σ e  n
        → eval σ e′ n′
        → eval σ (e + e′) (n +ℕ n′)

data ⟨_,_⟩⇓_ {∣V∣ : ℕ} (σ : State ∣V∣) : Stmt ∣V∣ → State ∣V∣ → Set where
  E-skip : ⟨ σ , skip ⟩⇓ σ
  E-seq : ∀ {s s′ : Stmt ∣V∣} {σ′ σ′′ : State ∣V∣}
        → ⟨ σ , s ⟩⇓ σ′
        → ⟨ σ′ , s′ ⟩⇓ σ′′
        → ⟨ σ , seq s s′ ⟩⇓ σ′′
  E-assign : ∀ {i} {e : Expr ∣V∣} {val : ℕ}
           → eval σ e val
           → ⟨ σ , i := e ⟩⇓ (σ [ i ]≔ val)
  E-ifz : ∀ {cond : Expr ∣V∣} (s₀ s₁ : Stmt ∣V∣) {σ′ : State ∣V∣}
        → eval σ cond zero
        → ⟨ σ , s₁ ⟩⇓ σ′
        → ⟨ σ , if cond then s₀ else s₁ ⟩⇓ σ′
  E-ifs : ∀ {cond : Expr ∣V∣} (s₀ s₁ : Stmt ∣V∣) {σ′ : State ∣V∣} {n : ℕ}
        → eval σ cond (suc n)
        → ⟨ σ , s₀ ⟩⇓ σ′
        → ⟨ σ , if cond then s₀ else s₁ ⟩⇓ σ′
  E-whilez : ∀ {cond : Expr ∣V∣} (body : Stmt ∣V∣)
           → eval σ cond zero
           → ⟨ σ , while cond ⁅ body ⁆ ⟩⇓ σ
  E-whiles : ∀ {cond : Expr ∣V∣} {body : Stmt ∣V∣} {σ′ σ′′ : State ∣V∣} {n : ℕ}
           → eval σ cond (suc n)
           → ⟨ σ , body ⟩⇓ σ′
           → ⟨ σ′ , while cond ⁅ body ⁆ ⟩⇓ σ′′
           → ⟨ σ , while cond ⁅ body ⁆ ⟩⇓ σ′′

EvalExpr-deterministic : ∀ {∣V∣ m m′ : ℕ} {σ : State ∣V∣} {expr : Expr ∣V∣}
                       → eval σ expr m
                       → eval σ expr m′
                       → m ≡ m′
EvalExpr-deterministic (E-ref _) (E-ref _) = refl
EvalExpr-deterministic (E-lit _) (E-lit _) = refl
EvalExpr-deterministic (E-add eval1 eval2) (E-add expr-eval1' expr-eval2')
  rewrite EvalExpr-deterministic eval1 expr-eval1'
        | EvalExpr-deterministic eval2 expr-eval2' =  refl
