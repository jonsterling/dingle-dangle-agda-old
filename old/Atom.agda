module DingleDangle.Atom where

open import Data.List hiding (any; all)
open import Data.List.Any
open import Data.List.All
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong)

open import Function
open import Data.Product

open import DingleDangle.DecEq
open import DingleDangle.Features

record Pair : Set where
  constructor ⟨_∶_⟩
  field
    key : Features
    val : ⟦ key ⟧f
    
pair-≡-inj-val : ∀ {k v₁ v₂} → ⟨ k ∶ v₁ ⟩ ≡ ⟨ k ∶ v₂ ⟩ → v₁ ≡ v₂
pair-≡-inj-val refl = refl

_≟-pair_ : Decidable {A = Pair} _≡_
⟨ k₁ ∶ _ ⟩ ≟-pair ⟨ k₂ ∶ _ ⟩ with k₁ ≟ k₂
...                        | no ¬p = no $ ¬p ∘ cong Pair.key
⟨ .k ∶ v₁ ⟩ ≟-pair ⟨ k ∶ v₂ ⟩ | yes refl with (v₁ ≟ v₂) where vdec = ⟦ k ⟧≟
...                                   | yes p = yes $ cong (λ v → ⟨ _ ∶ v ⟩) p
...                                   | no ¬p = no $ ¬p ∘ pair-≡-inj-val

≟InstancePair : ≟Class Pair
≟InstancePair = record { _≟_ = _≟-pair_ } 

Atom = List Pair

_∈_ : Pair → Atom → Set _
x ∈ xs = Any (_≡_ x) xs

_∈?_ : Decidable _∈_
p ∈? ps = any (_≟-pair_ p) ps

_⊆_ : Atom → Atom → Set _
xs ⊆ ys = All (λ x → x ∈ ys) xs

_⊆?_ : Decidable _⊆_
xs ⊆? ys = all (λ x → x ∈? ys) xs
