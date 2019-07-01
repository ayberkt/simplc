module Compiler where

import Relation.Binary.PropositionalEquality as Eq

open        Eq               using    (_≡_; refl; sym; cong; subst)
open import Data.Nat         using    (ℕ; zero; suc)
                             renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
open import Data.List        using    (List; _∷_; _∷ʳ_; []; _++_; [_]; length)
open import Data.Star        using    (ε; _◅_; _◅◅_)
open import Data.List.Properties using (length-++)
open import Relation.Nullary using    (¬_)
open import Data.Product     using    (Σ-syntax; _,_)
open import Function         using    (_∘_)

open import SecurityTypeSystem
open import Noninterference
open import Soundness
open import Machine
open import Defs
open import Imp

⟦_⟧E : ∀ {∣V∣ : ℕ} → Expr ∣V∣ → MachineProgram ∣V∣
⟦ ref x   ⟧E = [ LOAD x ]
⟦ lit n   ⟧E = [ CONST n ]
⟦ e₀ + e₁ ⟧E = (⟦ e₀ ⟧E ++ ⟦ e₁ ⟧E) ∷ʳ ADD

-- The compilation function.
⟦_⟧ : ∀ {∣V∣ : ℕ} → Stmt ∣V∣ → MachineProgram ∣V∣
⟦ skip                 ⟧ = []
⟦ seq s₀ s₁            ⟧ = ⟦ s₀ ⟧ ++ ⟦ s₁ ⟧
⟦ x := v               ⟧ = ⟦ v ⟧E ∷ʳ (STR x)
⟦ if c then s₀ else s₁ ⟧ =
  let
     ⟦s₁⟧   = ⟦ s₁ ⟧
     ⟦s₀⟧   = ⟦ s₀ ⟧
     ∣⟦s₀⟧∣ = length ⟦s₀⟧
     ∣⟦s₁⟧∣ = length ⟦s₁⟧
   in
        ⟦ c ⟧E ++ BRZ⁺ (∣⟦s₀⟧∣ +ℕ 2) ∷ ⟦s₀⟧ ++ CONST 0 ∷ BRZ⁺ ∣⟦s₁⟧∣ ∷ ⟦s₁⟧
⟦ while c ⁅ s ⁆        ⟧ =
  let
     ⟦c⟧E = ⟦ c ⟧E
     |⟦c⟧E| = length ⟦c⟧E
     ⟦s⟧   = ⟦ s ⟧
     ∣⟦s⟧∣ = length ⟦s⟧
   in
        ⟦c⟧E ++ BRZ⁺ (∣⟦s⟧∣ +ℕ 2) ∷ ⟦s⟧ ++ CONST 0 ∷ BRZ⁻ (|⟦c⟧E| +ℕ (1 +ℕ ∣⟦s⟧∣) +ℕ 2) ∷ []

lemma4 : ∀ n m → suc n +ℕ suc m ≡ n +ℕ suc (m +ℕ 1)
lemma4 n m rewrite sym (+-comm 1 m)
                 | +-comm n (suc m)
                 | +-comm n (suc (suc m)) =
  refl

no-last-plus-one : ∀ {∣V∣} {P : MachineProgram ∣V∣} {I : Instr ∣V∣} → ¬ P [ length P ]≈ I
no-last-plus-one {P = []} ()
no-last-plus-one {P = _ ∷ _} (tail x) = no-last-plus-one x

last-step : ∀ {∣V∣} {P : MachineProgram ∣V∣} {mem stack} {C₁′ : Config ∣V∣} →
      ¬ ([ ⟨ length P , stack , mem ⟩ , P ]↝ C₁′)
last-step (R-const x)   = no-last-plus-one x
last-step (R-add   x)   = no-last-plus-one x
last-step (R-load  x)   = no-last-plus-one x
last-step (R-str   x)   = no-last-plus-one x
last-step (R-br⁺Z  x)   = no-last-plus-one x
last-step (R-br⁺S  x)   = no-last-plus-one x
last-step (R-br⁻Z  x _) = no-last-plus-one x
last-step (R-br⁻S  x)   = no-last-plus-one x

⟦⟧E-correct : ∀ {∣V∣} {σ : State ∣V∣}
                 {e : Expr ∣V∣} {res : ℕ} {S : Stack}
             → eval σ e res
             → [ ⟨ 0 , S , σ ⟩ , ⟦ e ⟧E ]↝⋆ ⟨ length ⟦ e ⟧E , res ∷ S , σ ⟩
⟦⟧E-correct (E-ref i)               = R-load  (head []) ◅ ε
⟦⟧E-correct (E-lit n)               = R-const (head []) ◅ ε
⟦⟧E-correct {σ = σ} {S = S} (E-add {e₀} {e₁} {m} {n} p₀ p₁)
  rewrite length-++ (⟦ e₀ ⟧E ++ ⟦ e₁ ⟧E) {ADD ∷ []} =
    hauptsatz exec-operands exec-add
  where
    len₀ = length (⟦ e₀ ⟧E ++ ⟦ e₁ ⟧E)
    len₁ = length ((⟦ e₀ ⟧E ++ ⟦ e₁ ⟧E) ∷ʳ ADD)
    exec-operands : [ ⟨ 0 , S , σ ⟩ , ⟦ e₀ ⟧E ++ ⟦ e₁ ⟧E ]↝⋆ ⟨ len₀ , n ∷ m ∷ S , σ ⟩
    exec-operands rewrite length-++ ⟦ e₀ ⟧E {⟦ e₁ ⟧E} =
      hauptsatz (⟦⟧E-correct p₀) (⟦⟧E-correct p₁)
    exec-add : [ ⟨ 0 , n ∷ m ∷ S , σ ⟩ , [ ADD ] ]↝⋆ ⟨ 1 , m +ℕ n ∷ S , σ ⟩
    exec-add =  R-add (head []) ◅ ε

↝⋆-correct : ∀ {∣V∣} {σ₀ σ₁ : State ∣V∣}
                {P : Stmt ∣V∣}
           → ⟨ σ₀ , P ⟩⇓ σ₁
           → [ init-config σ₀ , ⟦ P ⟧ ]↝⋆ ⟨ length ⟦ P ⟧ , [] , σ₁ ⟩
↝⋆-correct E-skip = ε
↝⋆-correct (E-seq {s₀} {s₁} p₀ p₁) rewrite length-++ ⟦ s₀ ⟧ {⟦ s₁ ⟧} =
  hauptsatz (↝⋆-correct p₀) (↝⋆-correct p₁)
↝⋆-correct (E-assign {i} {e} p) rewrite length-++ ⟦ e ⟧E {STR i ∷ []} =
  hauptsatz (⟦⟧E-correct p) (R-str (head []) ◅ ε)
↝⋆-correct {σ₀ = σ₀} {σ₁} (E-ifz {cond} s₀ s₁ c⇓0 eval-s₁)
  rewrite length-++ ⟦ cond ⟧E
                    {BRZ⁺ (length ⟦ s₀ ⟧  +ℕ 2) ∷ ⟦ s₀ ⟧
                     ++ CONST 0 ∷ BRZ⁺ (length ⟦ s₁ ⟧) ∷ ⟦ s₁ ⟧}
        | length-++ (BRZ⁺ (length ⟦ s₀ ⟧  +ℕ 2) ∷ ⟦ s₀ ⟧)
                    {CONST 0 ∷ BRZ⁺ (length ⟦ s₁ ⟧) ∷ ⟦ s₁ ⟧} =
    hauptsatz (⟦⟧E-correct c⇓0) (R-br⁺Z (head _) ◅ E-br)
  where
    ∣⟦s₁⟧∣    = length ⟦ s₁ ⟧
    ∣⟦s₀⟧∣    = length ⟦ s₀ ⟧
    IH        = ↝⋆-correct eval-s₁
    p-skip-s₁ = CONST 0 ∷ BRZ⁺ ∣⟦s₁⟧∣ ∷ ⟦ s₁ ⟧
    p-skip-s₀ = BRZ⁺ (∣⟦s₀⟧∣ +ℕ 2) ∷ ⟦ s₀ ⟧ 
    E-else : [ ⟨ 2 , [] , σ₀ ⟩ , p-skip-s₁ ]↝⋆ ⟨ 2 +ℕ ∣⟦s₁⟧∣ , [] , σ₁ ⟩
    E-else = ↝⋆-prepend (↝⋆-prepend IH)
    E-br : [ ⟨ suc (∣⟦s₀⟧∣ +ℕ 2) , [] , σ₀ ⟩ , p-skip-s₀ ++ p-skip-s₁ ]↝⋆
             ⟨ suc (∣⟦s₀⟧∣ +ℕ (2 +ℕ ∣⟦s₁⟧∣)) , [] , σ₁ ⟩
    E-br = ↝⋆-prepend⋆ {is = BRZ⁺ (length ⟦ s₀ ⟧ +ℕ 2) ∷ ⟦ s₀ ⟧} E-else
↝⋆-correct (E-ifs {cond} s₀ s₁ c⇓suc eval-s₀)
  rewrite length-++ ⟦ cond ⟧E {BRZ⁺ (length ⟦ s₀ ⟧  +ℕ 2) ∷ ⟦ s₀ ⟧ ++ CONST 0 ∷ BRZ⁺ (length ⟦ s₁ ⟧) ∷ ⟦ s₁ ⟧}
        | length-++ (BRZ⁺ (length ⟦ s₀ ⟧  +ℕ 2) ∷ ⟦ s₀ ⟧) {CONST 0 ∷ BRZ⁺ (length ⟦ s₁ ⟧) ∷ ⟦ s₁ ⟧} =
  hauptsatz (⟦⟧E-correct c⇓suc) (hauptsatz (R-br⁺S (head _) ◅ ↝⋆-prepend (↝⋆-correct eval-s₀)) (R-const (head _) ◅ R-br⁺Z (tail (head _)) ◅ ε))
↝⋆-correct (E-whilez {cond} body c⇓0)
  rewrite length-++ (⟦ cond ⟧E) {(BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧) ++ CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []}
        | length-++ (BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧) {CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []}
  =  hauptsatz (⟦⟧E-correct c⇓0) (R-br⁺Z (head _) ◅ ε)
↝⋆-correct {σ₀ = σ₀} (E-whiles {cond} {body = body} {σ′ = σ′} {n = n} c⇓suc eval-body eval) = step0 ◅◅ (R-br⁺S
  {P = ⟦ cond ⟧E ++ (BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧) ++ CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []}
  (index-prepend {is = ⟦ cond ⟧E} (index-append {is = CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []} (head ⟦ body ⟧))) ◅ step1) ◅◅
  R-const (index-prepend {is = ⟦ cond ⟧E} step2) ◅ R-br⁻Z step3 refl ◅ ↝⋆-correct eval
  where
    step0 : [ ⟨ 0 , [] , σ₀ ⟩ ,
      ⟦ cond ⟧E ++ (BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧) ++ CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ [] ]↝⋆
      ⟨ length ⟦ cond ⟧E +ℕ 0 , suc n ∷ [] , σ₀ ⟩
    step0 rewrite +-identityʳ (length ⟦ cond ⟧E) = ↝⋆-append⋆ (⟦⟧E-correct c⇓suc)
    step1 : [ ⟨ suc (length ⟦ cond ⟧E +ℕ 0) , [] , σ₀ ⟩ ,
      ⟦ cond ⟧E ++ BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧ ++ CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧) +ℕ 2) ∷ []
      ]↝⋆ ⟨ length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧) , [] , σ′ ⟩
    step1 rewrite +-identityʳ (length ⟦ cond ⟧E) | +-comm 1 (length ⟦ cond ⟧E)
      = ↝⋆-prepend⋆ {is = ⟦ cond ⟧E} (↝⋆-append⋆ {is = CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []}
        (↝⋆-prepend {i = BRZ⁺ (length ⟦ body ⟧ +ℕ 2)}(↝⋆-correct eval-body)))
    step2 : (BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧ ++ CONST zero ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧) +ℕ 2) ∷ [])
              [ suc (length ⟦ body ⟧) ]≈ CONST zero
    step2 = subst
      (λ n → (BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧ ++ CONST zero ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧) +ℕ 2) ∷ []) [ suc (n) ]≈ CONST zero)
      (+-identityʳ (length ⟦ body ⟧))
      (index-prepend {is = BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧} (head _))
    step3′ : (BRZ⁻ (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧) +ℕ 2) ∷ [])
             [ zero ]≈ BRZ⁻ (suc (suc (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧))))
    step3′ rewrite (+-comm 2 ((length ⟦ cond ⟧E) +ℕ (suc (length ⟦ body ⟧)))) = head []
    step3 : (⟦ cond ⟧E ++ BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧ ++ CONST zero ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧) +ℕ 2) ∷ [])
              [ suc (length ⟦ cond ⟧E +ℕ suc (length ⟦ body ⟧)) ]≈ BRZ⁻ _
    step3 rewrite lemma4 (length ⟦ cond ⟧E) (length ⟦ body ⟧) =
      index-prepend (index-prepend {is = BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧} (tail step3′))

{-
--shorter but does not work because of R-br⁻Z:

↝⋆-correct {σ₀ = σ₀} (E-whiles {cond} {body} {σ′} {n = n} c⇓suc eval-body eval) rewrite length-++ (⟦ cond ⟧E)
  {(BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧) ++ CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []}
  | length-++ (BRZ⁺ (length ⟦ body ⟧ +ℕ 2) ∷ ⟦ body ⟧) {CONST 0 ∷ BRZ⁻ (length ⟦ cond ⟧E +ℕ (1 +ℕ length ⟦ body ⟧) +ℕ 2) ∷ []}
  = hauptsatz (⟦⟧E-correct c⇓suc) (hauptsatz (R-br⁺S (head _) ◅
    ↝⋆-prepend (↝⋆-correct eval-body)) (R-const (head _) ◅ R-br⁻Z (tail (head _)) {!!} ◅
    ↝⋆-prepend⋆ (↝⋆-prepend (↝⋆-correct eval))))
-}

correct : ∀ {∣V∣} {P : Stmt ∣V∣} {σ₀ σ₁ : State ∣V∣}
         → ⟨ σ₀ , P ⟩⇓ σ₁
         → [ init-config σ₀ , ⟦ P ⟧ ]halts-with ⟨ length ⟦ P ⟧ , [] , σ₁ ⟩
correct {P = P} {σ₁ = σ₁} x = ↝⋆-correct x , λ _ x → last-step x

correct⁻¹ : ∀ {∣V∣} {σ₀ : State ∣V∣} {C₀ : Config ∣V∣}
              {P : Stmt ∣V∣}
          → (∀ σ → Σ[ σ′ ∈ (State ∣V∣) ] ⟨ σ , P ⟩⇓ σ′)
          → [ init-config σ₀ , ⟦ P ⟧ ]halts-with C₀
          → ⟨ σ₀ , P ⟩⇓ Config.mem C₀
correct⁻¹ {σ₀ = σ₀} {C₀} {P} P-term φ with P-term σ₀
correct⁻¹ {σ₀ = σ₀} {C₀} {P} P-term φ | σ₁ , χ
  rewrite machine-det φ (correct χ) = χ

noninterference-preserved : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {P : Stmt ∣V∣}
                          → (∀ σ → Σ[ σ′ ∈ (State ∣V∣) ] ⟨ σ , P ⟩⇓ σ′)
                          → noninterference dom P → noninterferenceₘ dom ⟦ P ⟧
noninterference-preserved P-term P-NI M₀≈ₗM₁ M₀hwC₀ M₁hwC₁ =
  P-NI M₀≈ₗM₁ (correct⁻¹ P-term M₀hwC₀) (correct⁻¹ P-term M₁hwC₁)

main-theorem : ∀ {∣V∣ : ℕ} {P : Stmt ∣V∣} {dom : level-assignment ∣V∣}
                 {ℓ : SecurityLevel}
             → (∀ σ → Σ[ σ′ ∈ (State ∣V∣) ] ⟨ σ , P ⟩⇓ σ′)
             → ℓ ⊢[ dom ] P → noninterferenceₘ dom ⟦ P ⟧
main-theorem P-term = noninterference-preserved P-term ∘ sound
