open import Data.Nat

module CombinatorsNbe where

  data τ : Set where
    nat : τ
    _⇒_ : τ → τ → τ

  infixr 4 _⇒_


  ⟦_⟧τ : τ → Set
  ⟦ nat ⟧τ = ℕ
  ⟦ t₁ ⇒ t₂ ⟧τ = ⟦ t₁ ⟧τ -> ⟦ t₂ ⟧τ

  data Expr : τ → Set where
    K    : ∀ {a b} → Expr (a ⇒ b ⇒ a)
    S    : ∀ {a b c} → Expr ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
    O    : Expr nat
    succ : Expr (nat ⇒ nat)
    _●_  : ∀ {a b} → Expr (a ⇒ b) → Expr a → Expr b
    rec  : ∀ {a} → Expr a → Expr (nat ⇒ a ⇒ a) → Expr nat → Expr a

  rec-nat : ∀ {A : Set} → A → (ℕ → A → A) → ℕ → A
  rec-nat v _ zero = v
  rec-nat v f (suc n) = f n (rec-nat v f n)


  -- standard model

  ⟦_⟧E : ∀ {t} → Expr t → ⟦ t ⟧τ
  ⟦ K ⟧E = λ z _ → z
  ⟦ S ⟧E = λ z z₁ z₂ → z z₂ (z₁ z₂)
  ⟦ O ⟧E = zero
  ⟦ succ ⟧E = suc
  ⟦ e ● e₁ ⟧E = ⟦ e ⟧E ⟦ e₁ ⟧E
  ⟦ rec e e₁ e₂ ⟧E = rec-nat ⟦ e ⟧E ⟦ e₁ ⟧E ⟦ e₂ ⟧E


  -- glueing model

  
