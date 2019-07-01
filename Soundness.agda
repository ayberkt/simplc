module Soundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([]; _∷_; _[_]≔_; lookup)

open import Defs
open import Imp
open import SecurityTypeSystem
open import Noninterference

low-proj₀ : ∀ {l₀ l₁ : SecurityLevel}
            → (l₀ ⊔ l₁) ⊑ low → l₀ ⊑ low
low-proj₀ {l₀} {low} le = le
low-proj₀ {l₀} {high} ()

low-proj₁ : ∀ {l₀ l₁ : SecurityLevel}
            → (l₀ ⊔ l₁) ⊑ low → l₁ ⊑ low
low-proj₁ {l₀} {low} le = ⊑-refl _
low-proj₁ {l₀} {high} ()

≈ₗ-refl : ∀ {∣V∣ : ℕ} (dom : level-assignment ∣V∣) (σ : State ∣V∣)
        → σ ≈ₗ[ dom ] σ
≈ₗ-refl []       []           = ≈ₗ-nil
≈ₗ-refl (low ∷ dom) (n ∷ ns) = ≈ₗ-cons-L n (≈ₗ-refl dom ns)
≈ₗ-refl (high ∷ dom) (n ∷ ns) = ≈ₗ-cons-H n n (≈ₗ-refl dom ns)

≈ₗ-sym : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {σ σ′ : State ∣V∣}
       → σ  ≈ₗ[ dom ] σ′
       → σ′ ≈ₗ[ dom ] σ
≈ₗ-sym ≈ₗ-nil            = ≈ₗ-nil
≈ₗ-sym (≈ₗ-cons-L _ p)  = ≈ₗ-cons-L _ (≈ₗ-sym p)
≈ₗ-sym (≈ₗ-cons-H _ _ p) = ≈ₗ-cons-H _ _ (≈ₗ-sym p)

≈ₗ-trans : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {σ σ′ σ′′ : State ∣V∣}
         → σ  ≈ₗ[ dom ] σ′
         → σ′ ≈ₗ[ dom ] σ′′
         → σ  ≈ₗ[ dom ] σ′′
≈ₗ-trans ≈ₗ-nil ≈ₗ-nil = ≈ₗ-nil
≈ₗ-trans (≈ₗ-cons-L _ le) (≈ₗ-cons-L _ le') = ≈ₗ-cons-L _ (≈ₗ-trans le le')
≈ₗ-trans (≈ₗ-cons-H _ _ le) (≈ₗ-cons-H _ _ le') =
  ≈ₗ-cons-H _ _ (≈ₗ-trans le le')

-- Looking up any low-level reference in two low-equal states results in the
-- same thing
lemma1 : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {σ σ′ : State ∣V∣}
       → σ ≈ₗ[ dom ] σ′
       → (i : Fin ∣V∣)
       → lookup i dom ⊑ low
       → lookup i σ ≡ lookup i σ′
lemma1 {σ = []} {[]} _                 _       _  = refl
lemma1 {_}      {_}  (≈ₗ-cons-L _ _)   zero    _  = refl
lemma1 {_}      {_}  (≈ₗ-cons-L _ p)   (suc i) q  = lemma1 p i q
lemma1 {_}      {_}  (≈ₗ-cons-H _ _ p) (suc i) q  = lemma1 p i q
lemma1 {_}      {_}  (≈ₗ-cons-H _ _ _) zero    ()

-- Updating a high-level reference does not cause any low-observable change.
lemma2 : ∀ {∣V∣ : ℕ} (dom : level-assignment ∣V∣) (σ : State ∣V∣) (i : Fin ∣V∣)
       → high ⊑ lookup i dom
       → (val : ℕ)
       → σ ≈ₗ[ dom ] (σ [ i ]≔ val)
--lemma2 [] [] () dom-i val
--lemma2 (low ∷ dom) (n ∷ σ) zero ()
lemma2 (.high ∷ dom) (n ∷ σ) zero (⊑-refl .high) val = ≈ₗ-cons-H n val (≈ₗ-refl dom σ)
lemma2 (low ∷ dom) (n ∷ σ) (suc i) dom-i val = ≈ₗ-cons-L n (lemma2 dom σ i dom-i val)
lemma2 (high ∷ dom) (n ∷ σ) (suc i) dom-i val = ≈ₗ-cons-H n n (lemma2 dom σ i dom-i val)

-- Updating the state is a congruence wrt to low-level equality.
update-cong : ∀ {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {σ1 σ2 : State ∣V∣}
            → σ1 ≈ₗ[ dom ] σ2
            → (i : Fin ∣V∣) (val : ℕ)
            → (σ1 [ i ]≔ val) ≈ₗ[ dom ] (σ2 [ i ]≔ val)
update-cong (≈ₗ-cons-L _ le)   zero    _ = ≈ₗ-cons-L _ le
update-cong (≈ₗ-cons-H _ _ le) zero    _ = ≈ₗ-cons-H _ _ le
update-cong (≈ₗ-cons-L _ le)   (suc i) _ = ≈ₗ-cons-L _ (update-cong le _ _)
update-cong (≈ₗ-cons-H _ _ le) (suc i) _ = ≈ₗ-cons-H _ _ (update-cong le _ _)

-- Low-sensitivity data if confined within itself i.e., programs that are
-- typable in a high-sensitivity context do not affect the behavior of
-- low-sensitivity data.
conf : ∀ {∣V∣} {dom : level-assignment ∣V∣} {stmt : Stmt ∣V∣}
     → high ⊢[ dom ] stmt
     → {σ σ′ : State ∣V∣}
     → ⟨ σ , stmt ⟩⇓ σ′
     → σ ≈ₗ[ dom ] σ′
conf _ E-skip = ≈ₗ-refl _ _
conf (T-seq D₀ D₁) (E-seq eval₀ eval₁) = ≈ₗ-trans (conf D₀ eval₀) (conf D₁ eval₁)
conf (T-ass expr∈l dom-i) (E-assign eval) = lemma2 _ _ _ dom-i _
conf (T-if _ _ D) (E-ifz _ _ _ eval) = conf D eval
conf (T-if _ D _) (E-ifs _ _ _ eval) = conf D eval
conf _ (E-whilez _ _) = ≈ₗ-refl _ _
conf (T-while cond∈l D) (E-whiles _ eval-bdy eval) =
  ≈ₗ-trans (conf D eval-bdy) (conf (T-while cond∈l D) eval)

expr-sound : ∀ {∣V∣ v : ℕ} {dom : level-assignment ∣V∣} {e : Expr ∣V∣}
                {l : SecurityLevel} {σ σ′ : State ∣V∣} 
           → ⊢[ dom ] e ∈ l
           → l ⊑ low
           → σ ≈ₗ[ dom ] σ′
           → eval σ  e v
           → eval σ′ e v
expr-sound D l-low le (E-lit n) = E-lit n
expr-sound (T-ref .i) l-low le (E-ref i) rewrite lemma1 le i l-low = E-ref i
expr-sound (T-add D₀ D₁) l-low le (E-add eval₀ eval₁) =
  E-add (expr-sound D₀ (low-proj₀ l-low) le eval₀) (expr-sound D₁ (low-proj₁ l-low) le eval₁)

-- soundness proof

sound :
  {∣V∣ : ℕ} {dom : level-assignment ∣V∣} {pc : SecurityLevel} {stmt : Stmt ∣V∣} →
  pc ⊢[ dom ] stmt → noninterference dom stmt

-- high context
sound {pc = high} [pc]⊢stmt le e₀⇓m₀ e₁⇓m₁ =
  ≈ₗ-trans (≈ₗ-trans (≈ₗ-sym (conf [pc]⊢stmt e₀⇓m₀)) le) (conf [pc]⊢stmt e₁⇓m₁)

-- skip in low context
sound {pc = low} T-skip le E-skip E-skip = le

-- seq in low context
sound {pc = low} (T-seq typing-stmt₀ typing-stmt₁) le (E-seq eval₀-stmt₀ eval₁-stmt₀) (E-seq eval₀-stmt₁ eval₁-stmt₁) =
  sound typing-stmt₁ (sound typing-stmt₀ le eval₀-stmt₀ eval₀-stmt₁) eval₁-stmt₀ eval₁-stmt₁

-- assignment in low context
sound {pc = low} (T-ass {l = low} D _) le (E-assign eval₀-expr) (E-assign eval₁-expr)
  rewrite EvalExpr-deterministic (expr-sound D (⊑-refl low) le eval₀-expr) eval₁-expr = update-cong le _ _
sound {pc = low} (T-ass {l = high} _ dom-i) le (E-assign _) (E-assign _) =
  ≈ₗ-trans (≈ₗ-trans (≈ₗ-sym (lemma2 _ _ _ dom-i _)) le) (lemma2 _ _ _ dom-i _)

-- if in low context
sound {pc = low} (T-if _ _ p) le (E-ifz _ _ _ eval₀) (E-ifz  _ _ _ eval₁) =
  sound p le eval₀ eval₁
sound {pc = low} (T-if _ typing-stmts-then _) le (E-ifs _ _ _ eval-stmts-then1) (E-ifs _ _ _ eval-stmts-then2) =
  sound typing-stmts-then le eval-stmts-then1 eval-stmts-then2
sound {pc = low} (T-if {l = low} cond-low _ _) le (E-ifz _ _ cond-zero _) (E-ifs _ _ cond-suc _) with
  EvalExpr-deterministic (expr-sound cond-low (⊑-refl low) le cond-zero) cond-suc
... | () -- zero ≠ suc
sound {pc = low} (T-if {l = high} _ D₀ D₁) le (E-ifz _ _ _ eval-else) (E-ifs _ _ _ eval-then) =
  ≈ₗ-trans (≈ₗ-trans (≈ₗ-sym (conf D₁ eval-else)) le) (conf D₀ eval-then)
sound {pc = low} (T-if {l = low} cond-low _ _) le (E-ifs _ _ cond-suc _) (E-ifz _ _ cond-zero _) with
  EvalExpr-deterministic cond-zero (expr-sound cond-low (⊑-refl low) le cond-suc)
...| () -- suc ≠ zero
sound {pc = low} (T-if {l = high} _ D₀ D₁) le (E-ifs _ _ _ eval-then) (E-ifz _ _ _ eval-else) =
  ≈ₗ-trans (≈ₗ-trans (≈ₗ-sym (conf D₀ eval-then)) le) (conf D₁ eval-else)

-- while in low context
sound {pc = low} (T-while _ _) le (E-whilez _ _) (E-whilez _ _) = le
sound {pc = low} (T-while cond-low typing-stmts-body) le (E-whiles _ eval-body₀ eval-e₀) (E-whiles _ eval-body₁ eval-e₁) =
  sound (T-while cond-low typing-stmts-body) (sound typing-stmts-body le eval-body₀ eval-body₁) eval-e₀ eval-e₁
sound {pc = low} (T-while {l = low} cond-low _ ) le (E-whilez _ cond-zero) (E-whiles cond-suc _ _) with
  EvalExpr-deterministic (expr-sound cond-low (⊑-refl low) le cond-zero) cond-suc
... | () -- zero ≠ suc
sound {pc = low} (T-while {l = high} cond-high D-bdy) le (E-whilez _ _) (E-whiles _ eval-bdy eval) =
  ≈ₗ-trans le (≈ₗ-trans (conf D-bdy  eval-bdy) (conf (T-while cond-high D-bdy) eval))
sound {pc = low} (T-while {l = low} cond-low _) le (E-whiles cond-suc _ _) (E-whilez _ cond-zero) with
  EvalExpr-deterministic cond-zero (expr-sound cond-low (⊑-refl low) le cond-suc)
... | () -- suc ≠ zero
sound {pc = low} (T-while {l = high} cond-high D-bdy) le (E-whiles _  eval-bdy eval) (E-whilez _ _) =
  ≈ₗ-trans (≈ₗ-sym (≈ₗ-trans (conf D-bdy eval-bdy) (conf (T-while cond-high D-bdy) eval))) le
