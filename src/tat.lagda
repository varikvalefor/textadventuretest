\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{selnolig}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\nolig{>>}{>|>}
\nolig{<<}{<|<}

\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le me'oi .Agda.\ versiio be la .tat.\ noi ke'a samselkei je cu frafi'a le bebna}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --guardedness #-}

import Level
import Data.Fin
import Agda.Builtin.IO as ABIO
import Agda.Builtin.Unit as ABU

open import IO
  renaming (
    _>>_ to _>>ᵢₒ_;
    _>>=_ to _>>=ᵢₒ_
  )
open import Function
  using (
    _∘_;
    _$_;
    id
  )
open import Data.Char
  using (
    toUpper
  )
open import Data.List
  using (
    List;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    fromMaybe;
    Maybe;
    just;
    nothing
  )
open import Data.String
  using (
    String;
    words
  )
open import Data.Product
  using (
    proj₁;
    _×_;
    _,_
  )
open import TestAdventure.WYCT
open import VVXtAdventure.Base
open import VVXtAdventure.Funky
open import Truthbrary.Record.Eq
  using (
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    _++_;
    map
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl
  )
\end{code}

\section{la'oi .\F{main}.}

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ IO.lift nurtcati >>ᵢₒ lupe initialD
  where
  postulate nurtcati : ABIO.IO ABU.⊤
  {-# FOREIGN GHC import System.OpenBSD.Plegg #-}
  {-# COMPILE GHC nurtcati = plegg [Stdio] >> univac [] #-}

  lupe = λ q → fromMaybe (interact q) $ fanmo? q
    where
    fanmo? : GameData → Maybe $ IO ⊤
    fanmo? = firstJust ∘ Data.List.map mapti? ∘ fancu
      where
      firstJust : ∀ {a} → {A : Set a} → List $ Maybe A → Maybe A
      firstJust = Data.List.head ∘ Data.List.mapMaybe id
      mapti? = Data.Maybe.map $ putStrLn ∘ proj₁
      fancu : GameData → List COut
      fancu q = zmimrobi'o q ∷
                epicwin? winmsg q ∷
                []

    interact : GameData → IO ⊤
    interact = λ q → prompt >>ᵢₒ ree >>=ᵢₒ crock q
      where
      prompt = putStrLn "What do you do?"
      ree = words ∘ map toUpper <$> getLine
      crock : GameData → List String → IO ⊤
      crock gd s = Data.Product.proj₂ $ chews np $ ("" , gd) , mis m gd
        where
        mis = λ a b → putStrLn a >>ᵢₒ lupe b
        m = "I don't understand a word you just said."
        chews : ∀ {a b c}
              → {A : Set a}
              → {B : A → Set b}
              → {C : (x : A) → B x → Set c}
              → (List
                  (_×_
                    (Maybe $ Data.Product.∃ B)
                    ((x : A) → (z : B x) → C x z)))
              → Data.Product.∃ $ Data.Product.uncurry C
              → Data.Product.∃ $ Data.Product.uncurry C
        chews [] = id
        chews ((nothing , _) ∷ xs) = chews xs
        chews ((just (a , b) , f) ∷ _) _ = (a , b) , f a b
        np : List $ COut × (String → GameData → IO ⊤)
        np = map (λ f → f s gd , λ a b → putStrLn a >>ᵢₒ lupe b) std
          where
          std = sazycimde ++ gasnu
            where
            sazycimde = scream? ∷
                        sayless? ∷
                        inspect? ∷
                        lp? ∷
                        kumski? ∷
                        invent? ∷
                        []
            gasnu = travel? ∷
                    wield? ∷
                    hitme? ∷
                    []
\end{code}
\end{document}
