module DingleDangle.Examples where

open import DingleDangle.Features
open import DingleDangle.Features.Cat
open import DingleDangle.Features.Number

open import DingleDangle.Terms Features ⟦_⟧f

the : ⌈ ‵∀ (cat ≔ N ∷ var top) ⇒ (cat ≔ D ∷ var top) ⌉
the = Λ ƛ word "the"

dog : ⌈ cat ≔ N ∷ num ≔ sing ∷ ⟨⟩ ⌉
dog = word "dog"

the-dog : ⌈ cat ≔ D ∷ num ≔ sing ∷ ⟨⟩ ⌉
the-dog = the #ᴷ _ # dog
