module DingleDangle.Features where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong)

import DingleDangle.DecEq

open import Function
open import DingleDangle.Cat
open import DingleDangle.Number

data Features : Set where
  cat : Features
  num : Features

⟦_⟧f : (f : Features) → Set
⟦ cat ⟧f = Cat
⟦ num ⟧f = Number

⟦_⟧≟ : (f : Features) → DingleDangle.DecEq.≟Class ⟦ f ⟧f
⟦ cat ⟧≟ = ≟InstanceCat
⟦ num ⟧≟ = ≟InstanceNumber

≟InstanceFeatures : DingleDangle.DecEq.≟Class Features
≟InstanceFeatures = record { _≟_ = _≟_ } where
  _≟_ : Decidable _≡_
  cat ≟ cat = yes refl
  cat ≟ num = no $ λ ()
  num ≟ cat = no $ λ ()
  num ≟ num = yes refl
