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
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

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
import Agda.Builtin.Unit as ABU

open import IO
  renaming (
    _>>_ to _>>ᵢₒ_;
    _>>=_ to _>>=ᵢₒ_
  )
open import Function
open import Data.Bool
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
main = run $ lupe initialD
  where
  -- | ni'o pilno ko'a goi le zo ce'u co'e ki'u le su'u
  -- tu'a ko'a filri'a lo nu na co'e zo'oi .q.
  lupe : GameData → IO ⊤
  lupe = λ q → fromMaybe (interact q) $ fanmo? q
    where
    fanmo? : GameData → Maybe $ IO ⊤
    fanmo? q = firstJust $ Data.List.map mapti? fancu
      where
      firstJust : ∀ {a} → {A : Set a} → List $ Maybe A → Maybe A
      firstJust [] = nothing
      firstJust (just t ∷ _) = just t
      firstJust (nothing ∷ t) = firstJust t
      mapti? = Data.Maybe.map $ putStrLn ∘ proj₁
      fancu = zmimrobi'o q ∷
              epicwin? winmsg q ∷
              []

    interact : GameData → IO ⊤
    interact = λ q → prompt >>ᵢₒ ree >>=ᵢₒ crock q
      where
      prompt = putStrLn "What do you do?"
      ree = words ∘ map toUpper <$> getLine
      crock : GameData → List String → IO ⊤
      crock gd s = chews np $ mis m gd
        where
        mis = λ a b → putStrLn a >>ᵢₒ lupe b
        m = "I don't understand a word you just said."
        chews : List $ COut × (String → GameData → IO ⊤)
              → IO ⊤
              → IO ⊤
        chews ((just (a , b) , f) ∷ _) _ = f a b
        chews ((nothing , _) ∷ xs) d = chews xs d
        chews [] d = d
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
