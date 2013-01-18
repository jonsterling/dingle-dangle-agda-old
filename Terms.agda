module DingleDangle.Terms where

open import Data.String

open import DingleDangle.Universe

open import DingleDangle.Features
open import DingleDangle.Features.Cat
open import DingleDangle.Features.Number

open import DingleDangle.Types Features ⟦_⟧f

open Variables {{...}}

infixl 70 _#ᴷ_
infixl 70 _#_

data _⊢_ Γ : ∀ {G k} → G ⊢ᴷ k → Set where
  word : ∀ {G} {σ : G ⊢ᴷ *} → String → Γ ⊢ σ
  var : ∀ {G} {σ : G ⊢ᴷ *} → _∋_ {{Uᵀ}} Γ σ → Γ ⊢ σ
  ƛ_ : ∀ {G} {σ τ : G ⊢ᴷ *} → (Γ , σ) ⊢ τ → Γ ⊢ (σ ⇒ τ)
  Λ_ : ∀ {G k₁ k₂} {m : (G , k₁) ⊢ᴷ k₂} → Γ ⊢ m → Γ ⊢ ‵∀ m
  _#ᴷ_ : ∀ {G k₁ k₂} {σ : (G , k₁) ⊢ᴷ k₂} → Γ ⊢ ‵∀ σ → (τ : G ⊢ᴷ k₁) → Γ ⊢ σ / τ
  _#_ : ∀ {G} {σ τ : G ⊢ᴷ *} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ

-- A shorthand for closed types.
⌈_⌉ = _⊢_ ε {ε} 

the : ⌈ ‵∀ (cat ≔ N ∷ var top) ⇒ (cat ≔ D ∷ var top) ⌉
the = Λ ƛ word "the"

dog : ⌈ cat ≔ N ∷ num ≔ sing ∷ ⟨⟩ ⌉
dog = word "dog"

the-dog : ⌈ cat ≔ D ∷ num ≔ sing ∷ ⟨⟩ ⌉
the-dog = the #ᴷ _ # dog



