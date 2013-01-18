module DingleDangle.old.Pi.Pi where

open import Data.Vec
open import Data.Unit
open import Data.Nat
open import Function

infixl 85 _⊙_
infixl 80 _↑_
infixl 70 _/_
infixl 70 _/⊢_
infix  0 _∋_
infixr 0 _⊢_
infix  0 _▷_

mutual

  data Cx : Set where
    ε   : Cx
    _,_ : (Γ : Cx) → Ty Γ → Cx

  data Codes : Set where
    ‵ℕ ‵⊤ : Codes

  ⟦_⟧ : Codes → Set
  ⟦ ‵ℕ ⟧ = ℕ
  ⟦ ‵⊤ ⟧ = ⊤
    
  data Ty : Cx → Set where
    type : ∀ {Γ} → Ty Γ
    ∣_∣ : ∀ {Γ} → Codes → Ty Γ
    nvec : ∀ {Γ} → Γ ⊢ ∣ ‵ℕ ∣ → Ty Γ
    Π : ∀ {Γ} (τ : Ty Γ) → Ty (Γ , τ) → Ty Γ
    El : ∀ {Γ c} → Γ ⊢ ∣ c ∣ → Ty Γ

  -- Subst Γ Δ is a substitution (or weakening) of something with Γ as
  -- context into something with Δ as context.

  data _▷_ : Cx → Cx → Set where
    -- Weakening.
    wk : ∀ {Γ} σ → Γ ▷ Γ , σ
    -- Substituting a single variable.
    sub : ∀ {Γ τ} → Γ ⊢ τ → Γ , τ ▷ Γ
    -- Lifting.
    _↑_ : ∀ {Γ Δ} ρ σ → Γ , σ ▷ Δ , σ / ρ
    -- Identity.
    id⇒ : ∀ {Γ} → Γ ▷ Γ
    -- Composition.
    _⊙_ : ∀ {Γ Δ Θ} → Γ ▷ Δ → Δ ▷ Θ → Γ ▷ Θ

  data _∋_ : (Γ : Cx) → Ty Γ → Set where
    top : ∀ {Γ τ} → Γ , τ ∋ τ / wk τ
    pop : ∀ {Γ σ τ} → Γ ∋ τ → Γ , σ ∋ τ / wk σ

  data _⊢_ : (Γ : Cx) → Ty Γ → Set where
    Le : ∀ {Γ} → Ty Γ → Γ ⊢ type
    lit : ∀ {Γ c} → ⟦ c ⟧ → Γ ⊢ ∣ c ∣
    vec : ∀ {Γ n} → Vec ℕ n → Γ ⊢ nvec (lit n)
    var : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ
    ƛ_ : ∀ {Γ σ τ} → Γ , σ ⊢ τ → Γ ⊢ Π σ τ
    _#_ : ∀ {Γ σ τ} → Γ ⊢ Π σ τ → (t : Γ ⊢ σ) → Γ ⊢ τ / sub t
 

  ----------------------------------------------------------------------
  -- Synonyms

  -- Constructors cannot occur in types in the mutual block in which
  -- they are defined.

  ∣_∣′ : ∀ {Γ} → Codes → Ty Γ
  ∣_∣′ = ∣_∣

  ----------------------------------------------------------------------
  -- Substitution functions

  -- Applies a substitution to a type

  _/_ : {Γ Δ : Cx} → Ty Γ → Γ ▷ Δ → Ty Δ
  type / ρ = type
  ∣ c ∣ / ρ = ∣ c ∣
  nvec n / ρ = nvec ({!!} ((El n) / ρ))
  --$ forceSubst (n /⊢ ρ)
  Π σ τ / ρ = Π (σ / ρ) (τ / ρ ↑ σ)
  El t / ρ = El $ forceSubst (t /⊢ ρ)

  
  _/⊢_ : ∀ {Γ Δ τ} → Γ ⊢ τ → (ρ : Γ ▷ Δ) → Δ ⊢ τ / ρ
  _/⊢_ = {!!}
  
  forceSubst : ∀ {Γ Δ c} {ρ : Γ ▷ Δ} → Δ ⊢ ∣ c ∣′ / ρ → Δ ⊢ ∣ c ∣′
  forceSubst t = t


replicate-type : ε ⊢ Π ∣ ‵ℕ ∣ (Π (nvec (var top)) (nvec (var (pop top))))
replicate-type = ƛ (ƛ var top)

{-

blah : ε ⊢ nvec (var top /⊢ sub (lit 5))
blah = replicate-type # lit 5

bloo : ?
bloo = blah # ?
-}
