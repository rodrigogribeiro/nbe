open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Syntax
open import Utils


module Standard  (S : Monad) where

  open Monad S

  -- type semantics

  ⟦_⟧ : Ty → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ t ∧ t' ⟧ = ⟦ t ⟧ × ⟦ t' ⟧
  ⟦ t ⊃ t' ⟧ = ⟦ t ⟧ → ⟦ t' ⟧
  ⟦ t ∨ t' ⟧ = ⟦ t ⟧ ⊎ ⟦ t' ⟧
  ⟦ ◆ t ⟧ = M ⟦ t ⟧

  -- context semantics

  ⟦_⟧C : Ctx → Set
  ⟦ [] ⟧C = ⊤
  ⟦ t ∷ C ⟧C = ⟦ t ⟧ × ⟦ C ⟧C

  -- variable semantics

  semVar : ∀ {t Γ} → t ∈ Γ → ⟦ Γ ⟧C → ⟦ t ⟧
  semVar (here refl) (v , _) = v
  semVar (there v) env = semVar v (proj₂ env)

  -- term semantics

  eval : ∀ {t Γ} → Γ ⊢ t → ⟦ Γ ⟧C → ⟦ t ⟧
  eval (id v) env = semVar v env
  eval `⊤ env = tt
  eval (ExFalsum e) env = ⊥-elim (eval e env)
  eval (e , e') env = eval e env , eval e' env
  eval (fst e) env = proj₁ (eval e env)
  eval (snd e) env = proj₂ (eval e env)
  eval (abs e) env = λ z → eval e (z , env)
  eval (app e e') env = eval e env (eval e' env)
  eval (inl e) env = inj₁ (eval e env)
  eval (inr e) env = inj₂ (eval e env)
  eval (case e e' e'') env = ⊎-elim (λ v → eval e' (v , env))
                                    (λ v → eval e'' (v , env))
                                    (eval e env)
  eval (val e) env = return (eval e env)
  eval (bind e e') env = eval e env >>= λ v → eval e' (v , env)
