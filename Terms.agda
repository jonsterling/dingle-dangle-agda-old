module DingleDangle.Terms (F : Set) (⟦_⟧ᶠ : F → Set) where

open import Data.String

import DingleDangle.Types
open DingleDangle.Types F ⟦_⟧ᶠ public

open import DingleDangle.Universe
open Variables Uᴷ public using () renaming (_,_ to _,ᴷ_; ε to εᴷ)
open Variables Uᵀ public hiding (top; pop)
open Variables {{...}} public using (top; pop)

infixl 70 _#ᴷ_
infixl 70 _#_

data _⊢_ (Γ : Cx) : ∀ {G k} → G ⊢ᴷ k → Set where

  -- The non-structural content of a lexical entry: this will eventually
  -- include a notion of merge angle license.
  word : ∀ {G} {σ : G ⊢ᴷ *} → String → Γ ⊢ σ

  -- Accessing term variables from context.
  var : ∀ {G} {σ : G ⊢ᴷ *} → Γ ∋ σ → Γ ⊢ σ

  -- Term Abstraction: for when a word selects for another.
  ƛ_ : ∀ {G} {σ τ : G ⊢ᴷ *} → (Γ , σ) ⊢ τ → Γ ⊢ σ ⇒ τ

  -- Type Abstraction: for introducing feature / matrix dependencies.
  Λ_ : ∀ {G k₁ k₂} {m : (G ,ᴷ k₁) ⊢ᴷ k₂} → Γ ⊢ m → Γ ⊢ ‵∀ m

  -- Term Application: this is MERGE.
  _#_ : ∀ {G} {σ τ : G ⊢ᴷ *} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ

  -- Type Application: this is percolation of features.
  _#ᴷ_ : ∀ {G k₁ k₂} {σ : (G ,ᴷ k₁) ⊢ᴷ k₂} → Γ ⊢ ‵∀ σ → (τ : G ⊢ᴷ k₁) → Γ ⊢ σ / τ

-- A shorthand for closed types.
⌈_⌉ = _⊢_ ε {εᴷ}
