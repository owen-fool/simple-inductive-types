{- W-Algebra code, based on the HoTT book, through Martin Escardo's
   Type Topology.-}
{-# OPTIONS --safe --exact-split #-}
{-# OPTIONS --without-K #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Equiv
open import UF-Base

module dfunext-lemmas (fe : funext _ _) where

funext-happly : {X : 𝓤₀ ̇ } {A : X → 𝓤₀ ̇ }
               (f g : Π A) (h : f ≡ g)
             → dfunext fe (happly h) ≡ h
funext-happly f g h = inverse-is-retraction happly (fe f g) h
