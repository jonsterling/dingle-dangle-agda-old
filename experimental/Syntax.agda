module DingleDangle.Syntax where

open import Function

open import Data.String
open import Data.Nat
open import Data.Fin
open import Data.List

open import Data.Empty
open import Data.Unit
open import Data.Bool

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import DingleDangle.Cat
open import DingleDangle.Number
open import DingleDangle.Features
open import DingleDangle.Atom

infixr 0 _▷_

data * : Set where
  !_  : Atom → *
  _▷_ : * → * → *


data _≲_ : * → * → Set where
  !≲[_] : ∀ {xs ys} → xs ⊆ ys → (! ys) ≲ (! xs)
  _▷≲_ : ∀ {σ τ s t} → s ≲ σ → τ ≲ t → (σ ▷ τ) ≲ (s ▷ t)

_≲?_ : Decidable _≲_
(! xs) ≲? (! ys) with ys ⊆? xs
... | yes ys⊆xs = yes !≲[ ys⊆xs ]
... | no ¬ys⊆xs = no $ ¬ys⊆xs ∘ λ { !≲[ x ] → x }
(! _) ≲? (_ ▷ _) = no $ λ ()
(_ ▷ _) ≲? (! _) = no $ λ ()
(σ ▷ τ) ≲? (s ▷ t) with s ≲? σ | τ ≲? t
... | yes s≲σ | yes τ≲t = yes $ s≲σ ▷≲ τ≲t
... | _       | no ¬τ≲t = no $ ¬τ≲t ∘ λ { (_ ▷≲ x) → x }
... | no ¬s≲σ | _ = no $ ¬s≲σ ∘ λ { (x ▷≲ _) → x }

infixr 0 _⊢_
infixr 0 _#_
infixr 0 _∋_

data Cx : Set where
  ε : Cx
  _,_ : Cx → * → Cx

mutual
  data _∋_ : Cx → * → Set where
    top : ∀ {Γ τ} → Γ , τ ∋ τ
    pop : ∀ {Γ σ τ} → Γ ∋ τ → Γ , σ ∋ τ
  
  data _⊢_ Γ : * → Set where
    word : ∀ {fs} → String → Γ ⊢ ! fs
    cast : ∀ {σ τ} {{_ : True (σ ≲? τ) }} → Γ ⊢ σ → Γ ⊢ τ
    var  : ∀ {τ} → Γ ∋ τ → Γ ⊢ τ
    `λ   : ∀ {σ τ} → Γ , σ ⊢ τ → Γ ⊢ σ ▷ τ
    _#_  : ∀ {σ τ} → Γ ⊢ σ ▷ τ → Γ ⊢ σ → Γ ⊢ τ
  
  {-

  
⟦_⟧ : * → Set
⟦ t ⟧ = ∀ {Γ} → Γ ⊢ t

dog : ⟦ ! (⟨ num ∶ sing ⟩ ∷ ⟨ cat ∶ N ⟩ ∷ []) ⟧
dog = word "dog"

the : ∀ {n} → ⟦ ! (⟨ cat ∶ N ⟩ ∷ ⟨ num ∶ n ⟩ ∷ [])
                 ▷ ! (⟨ cat ∶ D ⟩ ∷ ⟨ num ∶ n ⟩ ∷ []) ⟧
the = `λ (word "the")

the-dog : ⟦ ! (⟨ cat ∶ D ⟩ ∷ ⟨ num ∶ sing ⟩ ∷ [] ) ⟧
the-dog = the # cast dog
-}
