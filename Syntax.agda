module DingleDangle.Syntax where

open import Data.String
open import Data.Nat
open import Data.Vec hiding (_∈_)
open import Data.List

open import Data.Empty
open import Data.Unit
open import Data.Bool

open import Relation.Nullary.Decidable

open import DingleDangle.Cat
open import DingleDangle.Number
open import DingleDangle.Features
open import DingleDangle.Pair

infixr 0 _▷_
data * : Set₁ where
  !_  : Atom → *
  _▷_ : * → * → *

_≲?_ : * → * → Bool
(! xs) ≲? (! ys) = ⌊ ys ⊆? xs ⌋
(! xs) ≲? (σ ▷ τ) = false
(σ ▷ τ) ≲? (! xs) = false
(σ ▷ τ) ≲? (s ▷ t) = (s ≲? σ) ∧ (τ ≲? t)

_≲_ : * → * → Set
σ ≲ τ = T (σ ≲? τ)

Cx = Vec *

mutual 
  infixr 0 _⊢_
  infixr 0 _$_
  infixr 0 _∋_

  data _∋_ : ∀ {n} → Cx n → * → Set₁ where
    top : ∀ {n τ} {Γ : Cx n} → (τ ∷ Γ) ∋ τ
    pop : ∀ {n σ τ} {Γ : Cx n} → Γ ∋ τ → (σ ∷ Γ) ∋ τ
  
  data _⊢_ {n : ℕ} (Γ : Cx n) : * → Set₁ where
    word : ∀ {fs} → String → Γ ⊢ ! fs
    cast : ∀ {σ τ} {{ _ : σ ≲ τ }} → Γ ⊢ σ → Γ ⊢ τ
    var  : ∀ {τ} → Γ ∋ τ → Γ ⊢ τ
    `λ   : ∀ {σ τ} → σ ∷ Γ ⊢ τ → Γ ⊢ σ ▷ τ
    _$_  : ∀ {σ τ} → Γ ⊢ σ ▷ τ → Γ ⊢ σ → Γ ⊢ τ

  
⟦_⟧ : * → Set₁
⟦ t ⟧ = {n : ℕ} {Γ : Cx n} → Γ ⊢ t

dog : ⟦ ! (⟨ num ∶ sing ⟩ ∷ ⟨ cat ∶ N ⟩ ∷ []) ⟧
dog = word "dog"

the : ∀ {n} → ⟦ ! (⟨ cat ∶ N ⟩ ∷ ⟨ num ∶ n ⟩ ∷ [])
                 ▷ ! (⟨ cat ∶ D ⟩ ∷ ⟨ num ∶ n ⟩ ∷ []) ⟧
the = `λ (word "the")

the-dog : ⟦ ! (⟨ cat ∶ D ⟩ ∷ ⟨ num ∶ sing ⟩ ∷ [] ) ⟧
the-dog = the $ (cast dog)
