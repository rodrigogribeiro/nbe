module Utils where

-- monad definition

record Monad : Set₁ where
  field
    M : Set → Set
    return : ∀ {A} → A → M A
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
