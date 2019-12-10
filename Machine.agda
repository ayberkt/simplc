module Machine where

open import Relation.Binary.PropositionalEquality as Eq

open         Eq.≡-Reasoning
open         Eq                 using    (_≡_; refl; sym; cong; subst; trans)
open import Data.List           using    (List; _∷_; []; _++_)
                                renaming (length to len)
open import Data.Vec            using    (Vec; lookup; _[_]≔_)
open import Data.Fin            using    (Fin)
open import Data.Product        using    (Σ-syntax; _×_; _,_)
open import Data.Star           using    (Star; ε; _◅_; _◅◅_)
open import Data.Empty          using    (⊥; ⊥-elim)
open import Relation.Nullary    using    (¬_)
open import Data.Nat            using    (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using    (+-identityʳ; +-cancelʳ-≡)

Offset : Set
Offset = ℕ

data Instr (∣V∣ : ℕ) : Set where
  ADD   : Instr ∣V∣
  CONST : ℕ → Instr ∣V∣
  LOAD  : Fin ∣V∣ → Instr ∣V∣
  STR   : Fin ∣V∣ → Instr ∣V∣
  HALT  : Instr ∣V∣
  BRZ⁺  : Offset → Instr ∣V∣
  BRZ⁻  : Offset → Instr ∣V∣

MachineProgram : ℕ → Set
MachineProgram ∣V∣ = List (Instr ∣V∣)

Stack : Set
Stack = List ℕ

PrgCounter : Set
PrgCounter = ℕ

Memory : ℕ → Set
Memory = Vec ℕ

record Config (∣V∣ : ℕ) : Set where
  constructor ⟨_,_,_⟩
  field
    pc     : PrgCounter
    stack  : Stack
    mem    : Memory ∣V∣

init-config : ∀ {∣V∣ : ℕ} → Memory ∣V∣ → Config ∣V∣
init-config mem = ⟨ 0 , [] , mem ⟩

pc-increment : ∀ {∣V∣ : ℕ} → Config ∣V∣ → Config ∣V∣
pc-increment ⟨ pc , stack , mem ⟩ = ⟨ suc pc , stack , mem ⟩

pc-increase : ℕ → ∀ {∣V∣ : ℕ} → Config ∣V∣ → Config ∣V∣
pc-increase n ⟨ pc , stack , mem ⟩ = ⟨ n + pc , stack , mem ⟩

infix 3 [_,_]↝_

-- `is[pc] ≈ i` is inhabited iff the list of instructions `is` contains
-- instruction `i` at location `pc`.
-- TODO: this is probably defined in the standard library. Make use of that
-- instead.
data _[_]≈_ {∣V∣ : ℕ} : MachineProgram ∣V∣ → ℕ → Instr ∣V∣ → Set where
  head : ∀ {i : Instr ∣V∣} (p : MachineProgram ∣V∣) → (i ∷ p) [ 0 ]≈ i
  tail : ∀ {i i′ : Instr ∣V∣} {p : MachineProgram ∣V∣} {n}
       → p [ n ]≈ i′ → (i ∷ p) [ suc n ]≈ i′

[∙]≈-det : ∀ {∣V∣ : ℕ} {p : MachineProgram ∣V∣} {ind : ℕ} {i₀ i₁ : Instr ∣V∣}
         → p [ ind ]≈ i₀
         → p [ ind ]≈ i₁
         → i₀ ≡ i₁
[∙]≈-det (head is) (head is′) = refl
[∙]≈-det (tail φ)  (tail ψ)   = [∙]≈-det φ ψ

data [_,_]↝_ {∣V∣ : ℕ} : Config ∣V∣
                        → MachineProgram ∣V∣
                        → Config ∣V∣
                        → Set where
  R-const : ∀ {n S} {pc : PrgCounter} {P : MachineProgram ∣V∣}  {M : Vec ℕ ∣V∣}
          → P [ pc ]≈ CONST n
          → [ ⟨ pc , S , M ⟩ , P ]↝ ⟨ suc pc , n ∷ S , M ⟩
  R-add : ∀ {n₀ n₁ : ℕ}
            {P : MachineProgram ∣V∣} {pc} {S} {M : Vec ℕ ∣V∣}
        → P [ pc ]≈ ADD
        → [ ⟨ pc , n₁ ∷ n₀ ∷ S , M ⟩ , P ]↝ ⟨ suc pc , n₀ + n₁ ∷ S , M ⟩
  R-load : ∀ {ind : Fin ∣V∣}
             {P : MachineProgram ∣V∣} {pc} {S}  {M : Vec ℕ ∣V∣}
         → P [ pc ]≈ LOAD ind
         → [ ⟨ pc , S , M ⟩ , P ]↝ ⟨ suc pc , lookup M ind ∷ S , M ⟩
  R-str : ∀ {v : ℕ} {ind : Fin ∣V∣}
            {P : MachineProgram ∣V∣} {pc S} {M : Vec ℕ ∣V∣}
        → P [ pc ]≈ STR ind
        → [ ⟨ pc , v ∷ S , M ⟩ , P ]↝ ⟨ suc pc , S , M [ ind ]≔ v ⟩
  R-br⁺Z : ∀ {P : MachineProgram ∣V∣} {pc S} {M : Vec ℕ ∣V∣} {o : Offset}
         → P [ pc ]≈ BRZ⁺ o
         → [ ⟨ pc , 0 ∷ S , M ⟩ , P ]↝ ⟨ (suc pc) + o , S , M ⟩
  R-br⁺S : ∀ {P : MachineProgram ∣V∣} {pc S} {M : Vec ℕ ∣V∣}
             {o : Offset} {n : ℕ}
         → P [ pc ]≈ BRZ⁺ o
         → [ ⟨ pc , suc n ∷ S , M ⟩ , P ]↝ ⟨ suc pc , S , M ⟩
  R-br⁻Z : ∀ {P : MachineProgram ∣V∣} {pc pc′ S} {M : Vec ℕ ∣V∣} {o : Offset}
         → P [ pc ]≈ BRZ⁻ o
         → pc′ + o ≡ suc pc
         → [ ⟨ pc , 0 ∷ S , M ⟩ , P ]↝ ⟨ pc′ , S , M ⟩
  R-br⁻S : ∀ {P : MachineProgram ∣V∣} {pc S} {M : Vec ℕ ∣V∣}
             {o : Offset} {n : ℕ}
         → P [ pc ]≈ BRZ⁻ o
         → [ ⟨ pc , suc n ∷ S , M ⟩ , P ]↝ ⟨ suc pc , S , M ⟩

[_,_]↝⋆_ : ∀ {∣V∣ : ℕ}
         → Config ∣V∣
         → MachineProgram ∣V∣
         → Config ∣V∣
         → Set
[ C , p ]↝⋆ C₀ = Star (λ C′ C₀′ → [ C′ , p ]↝ C₀′) C C₀

[_,_]halts-with_ : ∀ {∣V∣} → Config ∣V∣ → MachineProgram ∣V∣ → Config ∣V∣ → Set
[_,_]halts-with_ {∣V∣} C₀ P C₁  =
  [ C₀ , P ]↝⋆ C₁ × (∀ C₁′ → ¬ [ C₁ , P ]↝ C₁′)

index-append : ∀ {∣V∣ : ℕ} {p : MachineProgram ∣V∣} {is : List (Instr ∣V∣)} {i : Instr ∣V∣}
                       {k : ℕ}
                   → p         [ k ]≈ i
                   → (p ++ is) [ k ]≈ i
index-append (head is) = head (is ++ _)
index-append (tail φ)  = tail (index-append φ)

index-prepend : ∀ {∣V∣ : ℕ} {p : MachineProgram ∣V∣} {is : List (Instr ∣V∣)} {i : Instr ∣V∣}
                       {k : ℕ}
                   → p         [ k ]≈ i
                   → (is ++ p) [ len is + k ]≈ i
index-prepend {is = []} ind = ind
index-prepend {is = _ ∷ _} ind = tail (index-prepend ind)

↝-append⋆ : ∀ {∣V∣ : ℕ} {p : MachineProgram ∣V∣} {is : List (Instr ∣V∣)}
              {C C′ : Config ∣V∣}
          → [ C , p       ]↝ C′
          → [ C , p ++ is ]↝ C′
↝-append⋆ (R-const φ)    = R-const (index-append φ)
↝-append⋆ (R-add   φ)    = R-add   (index-append φ)
↝-append⋆ (R-load  φ)    = R-load  (index-append φ)
↝-append⋆ (R-str   φ)    = R-str   (index-append φ)
↝-append⋆ (R-br⁺Z  φ)    = R-br⁺Z  (index-append φ)
↝-append⋆ (R-br⁺S  φ)    = R-br⁺S  (index-append φ)
↝-append⋆ (R-br⁻Z  φ eq) = R-br⁻Z  (index-append φ) eq
↝-append⋆ (R-br⁻S  φ)    = R-br⁻S  (index-append φ)

↝⋆-append⋆ : ∀ {∣V∣ : ℕ} {p : MachineProgram ∣V∣} {is : List (Instr ∣V∣)}
               {C C′ : Config ∣V∣}
           → [ C , p       ]↝⋆ C′
           → [ C , p ++ is ]↝⋆ C′
↝⋆-append⋆ ε        = ε
↝⋆-append⋆ (φ ◅ φ⋆) = ↝-append⋆ φ ◅ ↝⋆-append⋆ φ⋆

↝-prepend : ∀ {∣V∣ : ℕ} {i : Instr ∣V∣} {p : MachineProgram ∣V∣}
              {C C′ : Config ∣V∣}
          → [              C ,     p ]↝              C′
          → [ pc-increment C , i ∷ p ]↝ pc-increment C′
↝-prepend (R-const φ)    = R-const (tail φ)
↝-prepend (R-add   φ)    = R-add   (tail φ)
↝-prepend (R-load  φ)    = R-load  (tail φ)
↝-prepend (R-str   φ)    = R-str   (tail φ)
↝-prepend (R-br⁺Z  φ)    = R-br⁺Z  (tail φ)
↝-prepend (R-br⁺S  φ)    = R-br⁺S  (tail φ)
↝-prepend (R-br⁻Z  φ eq) = R-br⁻Z  (tail φ) (cong suc eq)
↝-prepend (R-br⁻S  φ)    = R-br⁻S  (tail φ)

↝⋆-prepend : ∀ {∣V∣ : ℕ} {i : Instr ∣V∣} {p : MachineProgram ∣V∣}
               {C C′ : Config ∣V∣}
           → [              C ,     p ]↝⋆              C′
           → [ pc-increment C , i ∷ p ]↝⋆ pc-increment C′
↝⋆-prepend ε        = ε
↝⋆-prepend (φ ◅ φ⋆) = ↝-prepend φ ◅ ↝⋆-prepend φ⋆

↝⋆-prepend⋆ : ∀ {∣V∣ : ℕ} {p : MachineProgram ∣V∣} {is : List (Instr ∣V∣)}
                {C C′ : Config ∣V∣}
            → [                      C ,       p ]↝⋆                      C′
            → [ pc-increase (len is) C , is ++ p ]↝⋆ pc-increase (len is) C′
↝⋆-prepend⋆ {is = []}     φ = φ
↝⋆-prepend⋆ {is = _ ∷ _ } φ = ↝⋆-prepend (↝⋆-prepend⋆ φ)

-- The composability proof for machine  programs.
hauptsatz : ∀ {∣V∣ : ℕ} {p₀ p₁ : MachineProgram ∣V∣}
              {pc pc′ : PrgCounter}
              {stack stack′ stack′′ : Stack}
              {mem mem′ mem′′ : Memory ∣V∣}
          → [ ⟨ pc   , stack   , mem   ⟩ , p₀       ]↝⋆ ⟨ len p₀       , stack′′ , mem′′ ⟩
          → [ ⟨ zero , stack′′ , mem′′ ⟩ , p₁       ]↝⋆ ⟨ pc′          , stack′  , mem′  ⟩
          → [ ⟨ pc   , stack   , mem   ⟩ , p₀ ++ p₁ ]↝⋆ ⟨ len p₀ + pc′ , stack′  , mem′  ⟩
hauptsatz {|V|} {p₀} {p₁} {_} {pc′} {stack′ = S′} {S′′} {mem} {mem′} {mem′′} φ ψ =
    ↝⋆-append⋆ φ ◅◅ ϑ
  where
    ϑ : [ ⟨ len p₀ , S′′ , mem′′ ⟩ , p₀ ++ p₁ ]↝⋆ ⟨ len p₀ + pc′ , S′ , mem′ ⟩
    ϑ =
      subst
        (λ m → [ ⟨ m , _ , _ ⟩ , p₀ ++ p₁ ]↝⋆ ⟨ len p₀ + pc′ , _ , _ ⟩)
        (+-identityʳ (len p₀))
        (↝⋆-prepend⋆ ψ)

step-det : ∀ {∣V∣ : ℕ} {C₀ C₁ C₂ : Config ∣V∣} {P : MachineProgram ∣V∣}
         → [ C₀ , P ]↝ C₁
         → [ C₀ , P ]↝ C₂
         → C₁ ≡ C₂
step-det (R-const p) (R-const q) with [∙]≈-det p q
step-det (R-const p) (R-const q) | refl = refl
step-det (R-const p) (R-add q) with [∙]≈-det p q
step-det (R-const p) (R-add q) | ()
step-det (R-const p) (R-load q) with [∙]≈-det p q
step-det (R-const p) (R-load q) | ()
step-det (R-const p) (R-str q) with [∙]≈-det p q
step-det (R-const p) (R-str q) | ()
step-det (R-const p) (R-br⁺Z q) with [∙]≈-det p q
step-det (R-const p) (R-br⁺Z q) | ()
step-det (R-const p) (R-br⁺S q) with [∙]≈-det p q
step-det (R-const p) (R-br⁺S q) | ()
step-det (R-const p) (R-br⁻Z q eq) with [∙]≈-det p q
step-det (R-const p) (R-br⁻Z q eq) | ()
step-det (R-const p) (R-br⁻S q) with [∙]≈-det p q
step-det (R-const p) (R-br⁻S q) | ()
step-det (R-add _) (R-add _) = refl
step-det (R-add p) (R-const q) with [∙]≈-det p q
step-det (R-add p) (R-const q) | ()
step-det (R-add p) (R-load q) with [∙]≈-det p q
step-det (R-add p) (R-load q) | ()
step-det (R-add p) (R-str q) with [∙]≈-det p q
step-det (R-add p) (R-str q) | ()
step-det (R-add p) (R-br⁺Z q) with [∙]≈-det p q
step-det (R-add p) (R-br⁺Z q) | ()
step-det (R-add p) (R-br⁺S q) with [∙]≈-det p q
step-det (R-add p) (R-br⁺S q) | ()
step-det (R-add p) (R-br⁻Z q _) with [∙]≈-det p q
step-det (R-add p) (R-br⁻Z q _) | ()
step-det (R-add p) (R-br⁻S q) with [∙]≈-det p q
step-det (R-add p) (R-br⁻S q) | ()
step-det (R-load p) (R-load q) with [∙]≈-det p q
step-det (R-load p) (R-load q) | refl = refl
step-det (R-load p) (R-const q) with [∙]≈-det p q
step-det (R-load p) (R-const q) | ()
step-det (R-load p) (R-add q) with [∙]≈-det p q
step-det (R-load p) (R-add q) | ()
step-det (R-load p) (R-str q) with [∙]≈-det p q
step-det (R-load p) (R-str q) | ()
step-det (R-load p) (R-br⁺Z q) with [∙]≈-det p q
step-det (R-load p) (R-br⁺Z q) | ()
step-det (R-load p) (R-br⁺S q) with [∙]≈-det p q
step-det (R-load p) (R-br⁺S q) | ()
step-det (R-load p) (R-br⁻Z q _) with [∙]≈-det p q
step-det (R-load p) (R-br⁻Z q _)| ()
step-det (R-load p) (R-br⁻S q) with [∙]≈-det p q
step-det (R-load p) (R-br⁻S q) | ()
step-det (R-str p) (R-str q) with [∙]≈-det p q
step-det (R-str p) (R-str q) | refl = refl
step-det (R-str p) (R-const q) with [∙]≈-det p q
step-det (R-str p) (R-const q) | ()
step-det (R-str p) (R-add q) with [∙]≈-det p q
step-det (R-str p) (R-add q) | ()
step-det (R-str p) (R-load q) with [∙]≈-det p q
step-det (R-str p) (R-load q) | ()
step-det (R-str p) (R-br⁺Z q) with [∙]≈-det p q
step-det (R-str p) (R-br⁺Z q) | ()
step-det (R-str p) (R-br⁺S q) with [∙]≈-det p q
step-det (R-str p) (R-br⁺S q) | ()
step-det (R-str p) (R-br⁻Z q _) with [∙]≈-det p q
step-det (R-str p) (R-br⁻Z q _) | ()
step-det (R-str p) (R-br⁻S q) with [∙]≈-det p q
step-det (R-str p) (R-br⁻S q) | ()
step-det (R-br⁺Z p) (R-br⁺Z q) with [∙]≈-det p q
step-det (R-br⁺Z p) (R-br⁺Z q) | refl = refl
step-det (R-br⁺Z p) (R-const q) with [∙]≈-det p q
step-det (R-br⁺Z p) (R-const q) | ()
step-det (R-br⁺Z p) (R-add q) with [∙]≈-det p q
step-det (R-br⁺Z p) (R-add q) | ()
step-det (R-br⁺Z p) (R-load q) with [∙]≈-det p q
step-det (R-br⁺Z p) (R-load q) | ()
step-det (R-br⁺Z p) (R-str q) with [∙]≈-det p q
step-det (R-br⁺Z p) (R-str q) | ()
step-det (R-br⁺Z p) (R-br⁻Z q _) with [∙]≈-det p q
step-det (R-br⁺Z p) (R-br⁻Z q _) | ()
step-det (R-br⁺S p) (R-br⁺S q) with [∙]≈-det p q
step-det (R-br⁺S p) (R-br⁺S q) | refl = refl
step-det (R-br⁺S p) (R-const q) with [∙]≈-det p q
step-det (R-br⁺S p) (R-const q) | ()
step-det (R-br⁺S p) (R-add q) with [∙]≈-det p q
step-det (R-br⁺S p) (R-add q) | ()
step-det (R-br⁺S p) (R-load q) with [∙]≈-det p q
step-det (R-br⁺S p) (R-load q) | ()
step-det (R-br⁺S p) (R-str q) with [∙]≈-det p q
step-det (R-br⁺S p) (R-str q) | ()
step-det (R-br⁺S p) (R-br⁻S q) with [∙]≈-det p q
step-det (R-br⁺S p) (R-br⁻S q) | ()
step-det (R-br⁻Z p eq₀) (R-br⁻Z q eq₁) with [∙]≈-det p q
step-det (R-br⁻Z {pc′ = pc} p eq₀) (R-br⁻Z {pc′ = pc′} q eq₁)
  | refl rewrite +-cancelʳ-≡ pc pc′ (trans eq₀ (sym eq₁)) = refl
step-det (R-br⁻Z p _) (R-const q) with [∙]≈-det p q
step-det (R-br⁻Z p _) (R-const q) | ()
step-det (R-br⁻Z p _) (R-add q) with [∙]≈-det p q
step-det (R-br⁻Z p _) (R-add q) | ()
step-det (R-br⁻Z p _) (R-load q) with [∙]≈-det p q
step-det (R-br⁻Z p _) (R-load q) | ()
step-det (R-br⁻Z p _) (R-str q) with [∙]≈-det p q
step-det (R-br⁻Z p _) (R-str q) | ()
step-det (R-br⁻Z p _) (R-br⁺Z q) with [∙]≈-det p q
step-det (R-br⁻Z p _) (R-br⁺Z q) | ()
step-det (R-br⁻S p) (R-br⁻S q) with [∙]≈-det p q
step-det (R-br⁻S p) (R-br⁻S q) | refl = refl
step-det (R-br⁻S p) (R-const q) with [∙]≈-det p q
step-det (R-br⁻S p) (R-const q) | ()
step-det (R-br⁻S p) (R-add q) with [∙]≈-det p q
step-det (R-br⁻S p) (R-add q) | ()
step-det (R-br⁻S p) (R-load q) with [∙]≈-det p q
step-det (R-br⁻S p) (R-load q) | ()
step-det (R-br⁻S p) (R-str q) with [∙]≈-det p q
step-det (R-br⁻S p) (R-str q) | ()
step-det (R-br⁻S p) (R-br⁺S q) with [∙]≈-det p q
step-det (R-br⁻S p) (R-br⁺S q) | ()

machine-det : ∀ {∣V∣ : ℕ} {C₀ C₁ C₂ : Config ∣V∣} {P : MachineProgram ∣V∣}
            → [ C₀ , P ]halts-with C₁ → [ C₀ , P ]halts-with C₂ → C₁ ≡ C₂
machine-det (ε , _) (ε , _)                  = refl
machine-det (ε , φ) (_◅_ {_} {C′} q q⋆ , ψ)  = ⊥-elim (φ C′ q)
machine-det (_◅_ {_} {C′} p p⋆  , φ) (ε , ψ) = ⊥-elim (ψ C′ p)
machine-det (p ◅ p⋆ , φ) (q ◅ q⋆ , ψ) rewrite step-det p q =
  machine-det (p⋆ , φ) (q⋆ , ψ)
