{-# OPTIONS --without-K #-}
module container.m.from-nat.bisimulation where

open import level
open import sum
open import equality
open import function
open import container.core
open import container.m.coalgebra as MC hiding (IsMor ; _⇒_)
open import container.m.from-nat.coalgebra hiding (X)
open import hott.level

module Def {la lb lc} {C : Container la lb lc} (𝓧 : Coalg C (lb ⊔ lc)) where

  open Container C
  open Σ 𝓧 renaming (proj₁ to X ; proj₂ to γ)
  open MC C using (IsMor ; _⇒_)

  -- Σ-closure of an indexed binary relation
  Σ₂[_] : (∀ {i} → X i → X i → Set (lb ⊔ lc)) → I → Set _
  Σ₂[ _∼_ ] i = Σ (X i) λ x → Σ (X i) λ x′ → x ∼ x′

  -- projections
  module _ {_∼_ : ∀ {i} → X i → X i → Set _} (i : I) where

    Σ₂-proj₁ : Σ₂[ _∼_ ] i → X i
    Σ₂-proj₁ = proj₁

    Σ₂-proj₂ : Σ₂[ _∼_ ] i → X i
    Σ₂-proj₂ = proj₁ ∘' proj₂

    Σ₂-proj₃ : (r : Σ₂[ _∼_ ] i) → _∼_ (Σ₂-proj₁ r) (Σ₂-proj₂ r)
    Σ₂-proj₃ = proj₂ ∘' proj₂

  -- Definition 16 in Ahrens, Capriotti and Spadotti (arXiv:1504.02949v1 [cs.LO])
  -- bisimulation definition
  record Bisim (_∼_ : ∀ {i} → X i → X i → Set _): Set(lb ⊔ lc ⊔ lsuc la) where
    field
      α : Σ₂[ _∼_ ] →ⁱ F Σ₂[ _∼_ ]
      π₁-Mor : IsMor (_ , α) 𝓧 Σ₂-proj₁
      π₂-Mor : IsMor (_ , α) 𝓧 Σ₂-proj₂

    𝓑 : Coalg C _
    𝓑 = _ , α

    π₁ : 𝓑 ⇒ 𝓧
    π₁ = _ , π₁-Mor

    π₂ : 𝓑 ⇒ 𝓧
    π₂ = _ , π₂-Mor

  -- Lemma 17 in Ahrens, Capriotti and Spadotti (arXiv:1504.02949v1 [cs.LO])
  Δ : Bisim (λ {i} → _≡_)
  Δ = record { α = α ; π₁-Mor = π₁-Mor ; π₂-Mor = π₂-Mor }
    where α : Σ₂[ _≡_ ] →ⁱ F Σ₂[ _≡_ ]
          α i (x , ._ , refl) = proj₁ (γ _ x)
                                  , λ b → (proj₂ (γ _ x) b) , (_ , refl)
          π₁-Mor : IsMor (_ , α) 𝓧 _
          π₁-Mor = funextⁱ helper
            where helper : (i : I) → (p : Σ₂[ _≡_ ] i) → _
                  helper i (m , ._ , refl) = refl
          π₂-Mor : IsMor (_ , α) 𝓧 _
          π₂-Mor = funextⁱ helper
            where helper : (i : I) → (p : Σ₂[ _≡_ ] i) → _
                  helper i (m , ._ , refl) = refl


--------------------------------------------------------------------------------
-- coinduction proof principle

module _ {la lb lc} {C : Container la lb lc} where

  open Container C
  open MC C using (IsMor ; _⇒_)

  private
    𝓜 : Coalg C (lb ⊔ lc)
    𝓜 = 𝓛 C
    unfold : ∀ (𝓧 : Coalg C (lb ⊔ lc)) → 𝓧 ⇒ 𝓜
    unfold 𝓧 = proj₁ $ lim-terminal C 𝓧
    unfold-universal = λ {ℓ} (𝓧 : Coalg C ℓ) → proj₂ (lim-terminal C 𝓧)

  open Σ 𝓜 renaming (proj₁ to M ; proj₂ to out) ; open Def 𝓜

  module _ {_∼_ : ∀ {i} → M i → M i → Set (lb ⊔ lc)} (B : Bisim _∼_) where

    -- Theorem 18 in Ahrens, Capriotti and Spadotti (arXiv:1504.02949v1 [cs.LO])
    -- coinduction proof principle
    cpp : ∀ {i} {m m′ : M i} → m ∼ m′ → m ≡ m′
    cpp {i} p = funext-invⁱ (proj₁ $ apΣ π₁=π₂) i (_ , _ , p)
      where open Bisim B
            abstract
              π₁=π₂ : π₁ ≡ π₂
              π₁=π₂ = (sym $ unfold-universal 𝓑 π₁) · unfold-universal 𝓑 π₂


    -- In particular, provided that the bisimulation _∼_ is reflexive, we have:
    module _ (∼-refl : ∀ {i} {m : M i} → m ∼ m) where

      cpp′ : ∀ {i} {m m′ : M i} → m ∼ m′ → m ≡ m′
      cpp′ {i} p = cpp p · sym (cpp ∼-refl)

      cpp′-inv : ∀ {i} {m m′ : M i} → m ≡ m′ → m ∼ m′
      cpp′-inv refl = ∼-refl

      cpp′-id : ∀ {i} {m : M i} → cpp′ ∼-refl ≡ refl {x = m}
      cpp′-id = left-inverse $ cpp ∼-refl

      cpp′-retraction : ∀ {i} {m m′ : M i} (p : m ≡ m′) → cpp′ (cpp′-inv p) ≡ p
      cpp′-retraction refl = left-inverse $ cpp ∼-refl
