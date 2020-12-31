{- W-Algebra code, based on the HoTT book, and, importantly, in Martin Escardo's Introduction to 
   Homotopy Type Theory - in fact, the key section of this proof is just a small adaption of the 
   proof of the similar lemma for natural numbers that's there, library used is Martin Escardo's 
   Type Topology.-}
{-# OPTIONS --safe --exact-split #-}
{-# OPTIONS --without-K --no-import-sorts #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons
open import UF-Equiv
open import UF-Base

open import WTypes

import dfunext-lemmas

import MGS-Equivalences
import MGS-hlevels
import MGS-Retracts

module W-Algebra (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (fe : funext 𝓤₀ 𝓤₀) where

_◁_ : _
_◁_ = MGS-Equivalences._◁_

_≋_ : _
_≋_ = MGS-Equivalences._∼_

codomain' : _
codomain' = MGS-hlevels.codomain

domain' : _
domain' = MGS-hlevels.domain

retract-of-singleton : _
retract-of-singleton = MGS-Equivalences.retract-of-singleton

singleton-types-are-singletons! : _
singleton-types-are-singletons! = MGS-Equivalences.singleton-types-are-singletons
-- the names singleton-types-are-singletons' and singleton-types-are-singletons'' were both
-- already taken!

Σ-retract : _
Σ-retract = MGS-Equivalences.Σ-retract

_◁⟨_⟩_ : _
_◁⟨_⟩_ = MGS-Retracts._◁⟨_⟩_

_◀ : _
_◀ = MGS-Retracts._◀

--
W' : (X : 𝓤₀ ̇) → (X → 𝓤₀ ̇) → 𝓤₀ ̇
W' = W fe

-- The functions below are all as they appear in the HoTT book

WAlg : 𝓤₁ ̇
WAlg = Σ λ (C : 𝓤₀ ̇) → (a : A) → (B a → C) → C

WHom : (C D : WAlg) → 𝓤₀ ̇ 
WHom (C , sc) (D , sd) =
 Σ λ (f : C → D) → (a : A) (h : B a → C) → f (sc a h) ≡ sd a (f ∘ h)
 
isHinitᵂ : (I : WAlg) → 𝓤₁ ̇
isHinitᵂ I = (C : WAlg) → is-contr (WHom I C)

open W-Induction fe A B

W-proj₁ : W' A B → A
W-proj₁ (sup a h) = a

W-proj₂ : (w : W' A B) → (B (W-proj₁ w) → W' A B)
W-proj₂ (sup a h) = h

W-Induction' : (X : W' A B → 𝓤₀ ̇) → ((w : W' A B) → ((b : B (W-proj₁ w))
             → X (W-proj₂ w b)) → X w) → (w : W' A B) → X w
W-Induction' X e = Induction X λ a f → e (sup a f)

W-Recursion' : (X : 𝓤₀ ̇) → ((w : W' A B) → ((b : B (W-proj₁ w)) → X) → X) → W' A B → X
W-Recursion' X e = W-Induction' (λ _ → X) e

W-Iteration' : (X : 𝓤₀ ̇) → ((a : A) (f : B a → X) → X) → W' A B → X
W-Iteration' X e = W-Recursion' X λ w → e (W-proj₁ w)

-- This is the key section
-- The parallels here, and in the three functions above with what appears in section 22 of
-- Matin Escardo's notes, and in the section it depends on, should be clear.
-- The idea is to prove three retractions:
--    i) The type of proofs that ⌜a function from W A B to the W-Algebra C, h, applied to an
--       argument is equal in value to the function λ w → sC (w-proj₁ w) (h ∘ W-proj₂) applied to
--       that same argument⌝ is a retract of the type of proofs that ⌜h applied to an argument is
--       equal in value to the obvious iteration function, above, applied to that same argument⌝.
--   ii) Making use of i), the type of identifications between h and the function involving sC
--       is a retract of the type of identifications between h and the iteration function.
--  iii) Making use of ii), the type of pairs of a function and a proof it is equal to the
--       function involving sC, which is equal to the type of W-Homomorphisms, is a retract of the
--       type of pairs of a function and a proof that it is equal to the iteration function.
-- And then, because this latter type is contractible (which can be proved by path induction), all
-- retracts of it are contractible as well.
module Universal-Property (C : 𝓤₀ ̇) (sC : (a : A) (f : B a → C) → C) where

 first-retraction : (h : W' A B → C) → ((h ≋ (λ w → sC (W-proj₁ w) (h ∘ (W-proj₂ w))))
                                      ◁ (h ≋ W-Iteration' C sC))
 first-retraction h =  r , (s , η)
  where
   r : (h ≋ W-Iteration' C sC) → h ≋ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w))
   r →p (sup a f) = h (sup a f) ≡⟨ →p (sup a f) ⟩
                     W-Iteration' C sC (sup a f) ≡⟨ ap (λ - → (sC a (λ b → - b)))
                                                    ((dfunext fe (→p ∘ f)) ⁻¹) ⟩
                     sC a (h ∘ f) ∎

   s-aux : (codomain' r) → e-Type (λ w → h w ≡ W-Iteration' C sC w) 
   s-aux →p a f g = h (sup a f) ≡⟨ →p (sup a f) ⟩
                     sC a (h ∘ f) ≡⟨ ap (sC a) (dfunext fe g) ⟩
                     W-Iteration' C sC (sup a f) ∎

   s : codomain' r → domain' r
   s →p = Induction _ (s-aux →p)

   η : (→p : h ≋ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w))) → r (s →p) ≡ →p
   η →p = dfunext fe q
    where
     q-aux : e-Type (λ w → r (s →p) w ≡ →p w)
     q-aux a f g = s →p (sup a f) ∙ ap (sC a) (dfunext fe (s →p ∘ f) ⁻¹) ≡⟨ refl ⟩
                   (s-aux →p a f (s →p ∘ f)) ∙ ap (sC a) (dfunext fe (s →p ∘ f) ⁻¹) ≡⟨ refl ⟩
                   (→p (sup a f) ∙ ap (sC a) (dfunext fe (s →p ∘ f)))
                              ∙ (ap (sC a) (dfunext fe (s →p ∘ f) ⁻¹))
       ≡⟨ ap (s-aux →p a f (s →p ∘ f) ∙_) ((ap-sym (sC a) (dfunext fe (s →p ∘ f))) ⁻¹) ⟩
                   →p (sup a f) ∙ ap (sC a) (dfunext fe (s →p ∘ f))
                               ∙ (ap (sC a) (dfunext fe (s →p ∘ f))) ⁻¹
       ≡⟨ ∙assoc (→p (sup a f)) (ap (sC a) (dfunext fe (s →p ∘ f)))
                               ((ap (sC a) (dfunext fe (s →p ∘ f))) ⁻¹) ⟩
                   →p (sup a f)
                   ∙ (ap (sC a) (dfunext fe (s →p ∘ f)) ∙ (ap (sC a) (dfunext fe (s →p ∘ f))) ⁻¹)
       ≡⟨ ap (→p (sup a f) ∙_) (trans-sym' (ap (sC a) (dfunext fe (s →p ∘ f)))) ⟩
                   →p (sup a f) ∎

     q : r (s →p) ∼ →p
     q = Induction _ q-aux

 second-retraction : (h : W' A B → C)
                  → (h ≡ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w))) ◁ (h ≡ W-Iteration' C sC)
 second-retraction h =
                (h ≡ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w))) ◁⟨ ≃-gives-◁ (happly , (fe h _)) ⟩
                ((h ≋ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w))) ◁⟨ first-retraction h ⟩
                ((h ≋ W-Iteration' C sC) ◁⟨ ≃-gives-◁ (≃-sym (happly , fe _ _)) ⟩
                ((h ≡ W-Iteration' C sC) ◀)))
 
 final-retraction : Σ (λ h → h ≡ (λ w → sC (W-proj₁ w) (h ∘ (W-proj₂ w))))
                 ◁ Σ λ h → h ≡ W-Iteration' C sC    
 final-retraction = Σ-retract second-retraction

 using-the-retractions : is-singleton (Σ (λ h → h ≡ (λ w → sC (W-proj₁ w) (h ∘ (W-proj₂ w)))))
 using-the-retractions = retract-of-singleton final-retraction
                         (singleton-types-are-singletons! (W' A B → C) (W-Iteration' C sC))

-- We use the above to prove that W A B is Homotopy initial for the book-definition of that
-- property, because it is equivalent to the type we proved was a retract of the obviously
-- contractible type.
WTypeisHinitᵂ : isHinitᵂ (W' A B , sup)
WTypeisHinitᵂ (C , sC) = γ
 where
  open Universal-Property C sC
  open dfunext-lemmas fe

  α : _
  α = using-the-retractions

  forth-fix : (h : WHom (W' A B , sup) (C , sC))
           → pr₁ h ∼ (λ w → sC (W-proj₁ w) (pr₁ h ∘ W-proj₂ w))
  forth-fix (h , eh) (sup a f) = eh a f

  forth : WHom (W' A B , sup) (C , sC) → Σ (λ h → h ≡ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w)))
  forth (h , eh) = h , (dfunext fe (forth-fix (h , eh)))

  back : Σ (λ h → h ≡ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w))) → WHom (W' A B , sup) (C , sC)
  back (h , eh) = h , λ a f → happly eh (sup a f)

  forth-back-fix : (h' : Σ (λ h → h ≡ (λ w → sC (W-proj₁ w) (h ∘ W-proj₂ w)))) →
                   forth-fix (pr₁ h' , λ a f → happly (pr₂ h') (sup a f)) ≡ happly (pr₂ h')
  forth-back-fix h' = dfunext fe g
   where
    g : _
    g (sup a f) = refl

  forth-back : ∀ h → forth (back h) ≡ h
  forth-back (h , eh) = to-Σ-≡ (refl ,
                              (dfunext fe (forth-fix (h , pr₂ (back (h , eh)))) ≡⟨ refl ⟩
                              (dfunext fe (forth-fix (h , λ a f → happly eh (sup a f))))
                      ≡⟨ ap (dfunext fe) (forth-back-fix (h , eh)) ⟩
                              (dfunext fe (happly eh))
                      ≡⟨ funext-happly h _ eh ⟩
                              eh ∎))
                              
  back-forth : ∀ h → back (forth h) ≡ h
  back-forth (h , eh) = to-Σ-≡ (refl ,
   (dfunext fe (λ a → dfunext fe λ f → happly (dfunext fe (forth-fix (h , eh))) (sup a f)
                      ≡⟨ ap (λ - → - (sup a f)) (happly-funext fe h _ (forth-fix (h , eh))) ⟩
                                         (forth-fix (h , eh)) (sup a f) ≡⟨ refl ⟩
                                         eh a f ∎)))

  β : _
  β = forth , ((back , forth-back) , (back , back-forth))

  γ : _
  γ = equiv-to-singleton β α 
