module DingleDangle.Types (F : Set) (⟦_⟧ᶠ : F → Set) where

open import DingleDangle.Universe

open import Level using (suc)
open import Function
open import Data.Unit

data Kind : Set where
  -- an embedding of features into the the sort of kinds
  feat : F → Kind

  -- the kind of attribute-value-matrices
  * : Kind

-- Kinds are the highest universe.
Uᴷ = record { ctx = ⊤; type = ⊤; term = const $ const Kind }
open Variables Uᴷ

infixr 0 _∷_
infixr 70 _⇒_

data _⊢ᴷ_ Γ : Kind → Set where
  _≔_ : ∀ f → ⟦ f ⟧ᶠ → Γ ⊢ᴷ feat f
  ⟨⟩ : Γ ⊢ᴷ *
  _∷_ : ∀ {f} → Γ ⊢ᴷ feat f → Γ ⊢ᴷ * → Γ ⊢ᴷ *
  
  ‵∀_ : ∀ {k₁ k₂} → (Γ , k₁) ⊢ᴷ k₂ → Γ ⊢ᴷ k₂
  var : ∀ {k} → Γ ∋ k → Γ ⊢ᴷ k
  _⇒_ : ∀ (_ _ : Γ ⊢ᴷ *) → Γ ⊢ᴷ *

∀⟨_⟩_ : ∀ {Γ} k₁ {k₂} → (Γ , k₁) ⊢ᴷ k₂ → Γ ⊢ᴷ k₂
∀⟨ _ ⟩ x = ‵∀ x
  
-- Types are classified by kinds.
Uᵀ = record { ctx = Cx; type = Kind; term = _⊢ᴷ_ }


private

  record Kit (_◆_ : Cx → Kind → Set) : Set where
    constructor kit
    field
      variable : ∀ {Γ T}   → Γ ∋ T → Γ ◆ T
      term     : ∀ {Γ T}   → Γ ◆ T → Γ ⊢ᴷ T
      weaken   : ∀ {Γ S T} → Γ ◆ T → (Γ , S) ◆ T
  
  open Kit {{...}}
  
  lift : ∀ {Γ Δ S T _◆_} {{_ : Kit _◆_ }} → (∀ {X} → Γ ∋ X → Δ ◆ X) → (Γ , S) ∋ T → (Δ , S) ◆ T
  lift τ top = variable top
  lift τ (pop i) = weaken (τ i)
  
  traverse : ∀ {Γ Δ T _◆_} {{_ : Kit _◆_}} → (∀ {X} → Γ ∋ X → Δ ◆ X) → Γ ⊢ᴷ T → Δ ⊢ᴷ T
  traverse τ ⟨⟩ = ⟨⟩
  traverse τ (f ≔ rep) = f ≔ rep
  traverse τ (p ∷ avm) = traverse τ p ∷ traverse τ avm
  traverse τ (var v) = term (τ v)
  traverse τ (‵∀ x) = ‵∀ traverse (lift τ) x
  traverse τ (a ⇒ b) = traverse τ a ⇒ traverse τ b
  
  ∋-kit : Kit _∋_
  ∋-kit = kit id var pop
  
  term-kit : Kit _⊢ᴷ_
  term-kit = kit var id (traverse pop)
  
  subst₁ : ∀ {Γ S T} → Γ ⊢ᴷ S → (Γ , S) ⊢ᴷ T → Γ ⊢ᴷ T
  subst₁ {Γ} {S} t = traverse f
    where
    f : ∀ {X} → (Γ , S) ∋ X → Γ ⊢ᴷ X
    f top = t
    f (pop i) = var i

infix 70 _/_
_/_ : ∀ {Γ S T} → (Γ , S) ⊢ᴷ T → Γ ⊢ᴷ S → Γ ⊢ᴷ T
_/_ = flip subst₁

data Env : Cx → Set₁ where
  ε   : Env ε
  _,_ : ∀ {Γ T} (xs : Env Γ) (x : Γ ⊢ᴷ T) → Env (Γ , T)
  
--⟦_⟧ᴷ : Kind → Set₁
--⟦ * ⟧ᴷ = Set

