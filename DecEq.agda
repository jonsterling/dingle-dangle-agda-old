------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for _≟_
------------------------------------------------------------------------

module DingleDangle.DecEq where

open import Data.Bool using (Bool)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Unit using (⊤)

open import Relation.Binary.Core

------------------------------------------------------------------------
-- Type class

record DecEq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : Decidable {A = A} _≡_

open DecEq {{...}} public

------------------------------------------------------------------------
-- Instances

≟InstanceBool : DecEq Bool
≟InstanceBool = record { _≟_ = Data.Bool._≟_ }

≟InstanceChar : DecEq Char
≟InstanceChar = record { _≟_ = Data.Char._≟_ }

≟Instanceℕ : DecEq ℕ
≟Instanceℕ = record { _≟_ = Data.Nat._≟_ }

≟InstanceString : DecEq String
≟InstanceString = record { _≟_ = Data.String._≟_ }

≟Instance⊤ : DecEq ⊤
≟Instance⊤ = record { _≟_ = Data.Unit._≟_ }
