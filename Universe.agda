module DingleDangle.Universe where

record Universe : Set₁ where
  field
    ctx : Set
    type : Set
    term : ctx → type → Set

module Variables (U : Universe) where
  open Universe {{...}}

  data Cx : Set where
    ε : Cx
    _,_ : ∀ {G τ} → Cx → term G τ → Cx
  
  data _∋_ : ∀ {G τ} → Cx → term G τ → Set where
    top : ∀ {Γ G τ} {x : term G τ} → (Γ , x) ∋ x
    pop : ∀ {Γ G τ} {x y : term G τ} → Γ ∋ x → (Γ , y) ∋ x
