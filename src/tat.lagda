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
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le me'oi .Agda.\ versiio be la .tat.\ noi ke'a selci'a capli'u samselkei}
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
    _×_;
    _,_
  )
open import TestAdventure.WYCT
open import VVXtAdventure.Base
open import VVXtAdventure.Funky
open import Truthbrary.Record.Eq
open import Data.Unit.Polymorphic
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
  {-# COMPILE GHC nurtcati = plegg [Stdio] >> univac #-}

  lupe = λ q → prompt >>ᵢₒ ree >>=ᵢₒ crock q
    where
    prompt = putStrLn "What do you do?"
    ree = words ∘ map toUpper <$> getLine
    crock : GameData → List String → IO ⊤
    crock gd s = chews np $ putStrLn m >>ᵢₒ lupe gd
      where
      m = "I don't understand a word you just said."
      chews : List $ COut × (GameData → IO ⊤) → IO ⊤ → IO ⊤
      chews ((just (a , b) , f) ∷ _) _ = putStrLn a >>ᵢₒ f b
      chews ((nothing , _) ∷ xs) = chews xs
      chews [] = id
      np = (epicwin? winmsg gd , const boob) ∷
           map (λ f → f s gd , lupe) std
        where
        boob = return $ Level.lift ABU.tt
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
                  []
\end{code}
\end{document}
