module PTS where

open import Data.Nat hiding (_<_)
open import Data.Fin hiding (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

mutual

  data Cx : Set where
    ε : Cx
    _,_ : ∀ {i} → (Γ : Cx) → Type Γ i → Cx

  data Type : Cx → ℕ → Set where
    set : ∀ {Γ} (i : ℕ) → Type Γ (suc i)
    ⟦_⟧ : ∀ {Γ i k} → Term Γ {suc i} k → Type Γ i
  

  data _▷_ : Cx → Cx → Set where
    -- Weakening.
    wk : ∀ {Γ i} {σ : Type Γ i} → Γ ▷ (Γ , σ)
    -- Substituting a single variable.
    sub : ∀ {Γ i} {τ : Type Γ i} → Term Γ τ → (Γ , τ) ▷ Γ
    -- Lifting.
    _↑_ : ∀ {Γ Δ i} ρ (σ : Type Γ i) → (Γ , σ) ▷ (Δ , ( σ / ρ))
    -- Identity.
    id⇒ : ∀ {Γ} → Γ ▷ Γ
    -- Composition.
    _⊙_ : ∀ {Γ Δ Θ} → Γ ▷ Δ → Δ ▷ Θ → Γ ▷ Θ
    
  set'' : ∀ {Γ} (i : ℕ) → Type Γ (suc i)
  set'' = set
  
  data Term Γ : {i : ℕ} → Type Γ i → Set where
    set' : ∀ (i : ℕ) → Term Γ (set (suc i))
    ty : ∀ {i : ℕ} → Term Γ (set i) → Term Γ ⟦ set' i ⟧

    Π : ∀ {i j} (s : Term Γ (set i)) (t : Term (Γ , ⟦ s ⟧) (set j)) → Term Γ (set (i ⊔ j))

    --ƛ : ∀ {i j} {s : Term Γ (set i)} {t : Term (Γ , ⟦ s ⟧) (set j)} → Term (Γ , ⟦ s ⟧) ⟦ t ⟧ → Term Γ ⟦ Π s t ⟧
    ƛ' : ∀ {s : Term Γ (set 0)} {t : Term (Γ , ⟦ s ⟧) (set 0)} → Term (Γ , ⟦ s ⟧) ⟦ t ⟧ → Term Γ ⟦ Π s t ⟧

    _#_ : ∀ {i j} {s : Term Γ (set i)} {t : Term (Γ , ⟦ s ⟧) (set j)} → Term Γ ⟦ Π s t ⟧ → (x : Term Γ ⟦ s ⟧) → Term Γ ( ⟦ t ⟧ / (sub x))


  _/_ : {i : ℕ} {Γ Δ : Cx} → Type Γ i → Γ ▷ Δ → Type Δ i
  set i / ρ = set i
  ⟦ set' i ⟧ / ρ = {!!}
  ⟦ ty x ⟧ / ρ = ⟦ ty {!!} ⟧
  ⟦ Π x x₁ ⟧ / ρ = ⟦ (Π {!_/_!} {!!}) ⟧
  ⟦ x₂ # x₃ ⟧ / ρ = {!!}

  
    
                                              
infixr 70 _⇒_
_⇒_ : ∀ {Γ i j} (s : Term Γ (set i)) (t : Term (Γ , ⟦ s ⟧) (set j)) → Term Γ (set (i ⊔ j))
_⇒_ = Π

