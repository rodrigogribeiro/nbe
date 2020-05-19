open import Data.List hiding (drop)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional

open import Relation.Binary.PropositionalEquality
open import Syntax
open import Utils


module Embeddings where


-- order preserving embeddings

data _⊇_ : Ctx → Ctx → Set where
  ● : [] ⊇ []
  drop : ∀ {Γ Γ' A} → Γ ⊇ Γ' → (A ∷ Γ) ⊇ Γ'
  keep : ∀ {Γ Γ' A} → Γ ⊇ Γ' → (A ∷ Γ) ⊇ (A ∷ Γ') 


-- renamings

embed-∈ : ∀ {Γ Γ' A} → Γ ⊇ Γ' → A ∈ Γ' → A ∈ Γ
embed-∈ (drop su) v = there (embed-∈ su v)
embed-∈ (keep su) (here refl) = here refl
embed-∈ (keep su) (there v) = there (embed-∈ su v)

embed-⊢ : ∀ {Γ Γ' A} → Γ ⊇ Γ' → Γ' ⊢ A → Γ ⊢ A
embed-⊢ su (id v) = id (embed-∈ su v)
embed-⊢ su `⊤ = `⊤
embed-⊢ su (ExFalsum e) = ExFalsum (embed-⊢ su e)
embed-⊢ su (e , e') = embed-⊢ su e , embed-⊢ su e'
embed-⊢ su (fst e) = fst (embed-⊢ su e)
embed-⊢ su (snd e) = snd (embed-⊢ su e)
embed-⊢ su (abs e) = abs (embed-⊢ (keep su) e)
embed-⊢ su (app e e') = app (embed-⊢ su e) (embed-⊢ su e')
embed-⊢ su (inl e) = inl (embed-⊢ su e)
embed-⊢ su (inr e) = inr (embed-⊢ su e)
embed-⊢ su (case e e' e'') = case (embed-⊢ su e)
                                  (embed-⊢ (keep su) e')
                                  (embed-⊢ (keep su) e'')
embed-⊢ su (val e) = val (embed-⊢ su e)
embed-⊢ su (bind e e') = bind (embed-⊢ su e) (embed-⊢ (keep su) e')

embed-id : ∀ {Γ} → Γ ⊇ Γ
embed-id {[]} = ●
embed-id {t ∷ Γ} = keep embed-id

wk : ∀ {A Γ} → (A ∷ Γ) ⊇ Γ
wk = drop embed-id


-- substitutions

data Sub (Γ : Ctx) : Ctx → Set where
  ●   : Sub Γ []
  _,_ : ∀ {Γ' A} → Sub Γ Γ' → Γ ⊢ A → Sub Γ (A ∷ Γ')


_●ₑ_ : ∀ {Γ Γ' Γ''} → Sub Γ' Γ'' → Γ ⊇ Γ' → Sub Γ Γ''
● ●ₑ su = ●
(s , e) ●ₑ su = (s ●ₑ su) , embed-⊢ su e

drops : ∀ {Γ Γ' A} → Sub Γ Γ' → Sub (A ∷ Γ) Γ'
drops s = s ●ₑ wk

keeps : ∀ {Γ Γ' A} → Sub Γ Γ' → Sub (A ∷ Γ) (A ∷ Γ')
keeps s = drops s , id (here refl)

embed-⊇ : ∀ {Γ Γ'} → Γ ⊇ Γ' → Sub Γ Γ'
embed-⊇ ● = ●
embed-⊇ (drop su) = drops (embed-⊇ su)
embed-⊇ (keep su) = keeps (embed-⊇ su)


applyVar : ∀ {Γ Γ' A} → Sub Γ Γ' → A ∈ Γ' → Γ ⊢ A
applyVar (s , a) (here refl) = a
applyVar (s , _) (there v) = applyVar s v

apply : ∀ {Γ Γ' A} → Sub Γ Γ' → Γ' ⊢ A → Γ ⊢ A
apply s (id v) = applyVar s v
apply s `⊤ = `⊤
apply s (ExFalsum e) = ExFalsum (apply s e)
apply s (e , e') = apply s e , apply s e'
apply s (fst e) = fst (apply s e)
apply s (snd e) = snd (apply s e)
apply s (abs e) = abs (apply (keeps s) e)
apply s (app e e') = app (apply s e) (apply s e')
apply s (inl e) = inl (apply s e)
apply s (inr e) = inr (apply s e)
apply s (case e e' e'') = case (apply s e)
                               (apply (keeps s) e')
                               (apply (keeps s) e'')
apply s (val e) = val (apply s e)
apply s (bind e e') = bind (apply s e)
                           (apply (keeps s) e')



id-sub : ∀ {Γ} → Sub Γ Γ
id-sub {[]} = ●
id-sub {A ∷ Γ} = keeps id-sub
