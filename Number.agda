module DingleDangle.Number where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

import DingleDangle.DecEq

data Number : Set where
  sing dual plur : Number

≟InstanceNumber : DingleDangle.DecEq.≟Class Number
≟InstanceNumber = record { _≟_ = _≟_ } where
  _≟_ : Decidable _≡_
  sing ≟ sing = yes refl
  sing ≟ dual = no (λ ())
  sing ≟ plur = no (λ ())
  dual ≟ sing = no (λ ())
  dual ≟ dual = yes refl
  dual ≟ plur = no (λ ())
  plur ≟ sing = no (λ ())
  plur ≟ dual = no (λ ())
  plur ≟ plur = yes refl
