module DingleDangle.Features.Cat where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

import DingleDangle.DecEq

data Cat : Set where
  N D V P : Cat

≟InstanceCat : DingleDangle.DecEq.DecEq Cat
≟InstanceCat = record { _≟_ = _≟_ } where
  _≟_ : Decidable _≡_
  N ≟ N = yes refl
  N ≟ D = no (λ ())
  N ≟ V = no (λ ())
  N ≟ P = no (λ ())
  D ≟ N = no (λ ())
  D ≟ D = yes refl
  D ≟ V = no (λ ())
  D ≟ P = no (λ ())
  V ≟ N = no (λ ())
  V ≟ D = no (λ ())
  V ≟ V = yes refl
  V ≟ P = no (λ ())
  P ≟ N = no (λ ())
  P ≟ D = no (λ ())
  P ≟ V = no (λ ())
  P ≟ P = yes refl 

