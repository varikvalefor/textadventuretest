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
    Maybe;
    just;
    nothing
  )
open import Data.String
open import Data.Product
  using (
    _×_;
    _,_
  )
open import VVXtAdventure.Base
open import TestAdventure.Funky
open import Truthbrary.Record.Eq
open import Data.Unit.Polymorphic
open import Truthbrary.Record.LLC
  using (
    map
  )
\end{code}

\section{le tolsti co'e}

\subsection{la'oi .\F{rooms}.}

\begin{code}
rooms : List Room
rooms = dingyliv ∷ []
  where
  dingyliv : Room
  dingyliv = record {
    name = "A DINGY LIVING ROOM";
    cname = "DINGYLIVRM";
    items = []}
\end{code}

\subsection{la'oi .\F{initialD}.}

\begin{code}
initialD : GameData
initialD = record {
  rooms = rooms;
  room = Data.Fin.fromℕ 0;
  forename = "HARRIET";
  surname = "TUBMANN";
  epicwin = false;
  nicknames = "THE O.G. MEATBALL" ∷ [];
  inventory = []}
\end{code}

\section{la'oi .\F{main}.}

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ lupe initialD
  where
  lupe = λ q → prompt >>ᵢₒ ree >>=ᵢₒ crock q
    where
    prompt = putStrLn "What do you do?"
    ree = map (map toUpper) ∘ words IO.<$> getLine
    crock : GameData → List String → IO ⊤
    crock gd s = chews np $ putStrLn m >>ᵢₒ lupe gd
      where
      chews : List $ COut × (GameData → IO ⊤) → IO ⊤ → IO ⊤
      chews ((just (a , b) , f) ∷ _) _ = putStrLn a >>ᵢₒ f b
      chews ((nothing , _) ∷ xs) d = chews xs d
      chews [] d = d
      m = "I don't understand a word you just said."
      np : List $ COut × (GameData → IO ⊤)
      np = (epicwin? gd , boob) ∷
           map (λ f → f s gd , lupe) std
        where
        boob = const $ return $ Level.lift ABU.tt
        std = scream? ∷
              sayless? ∷
              inspect? ∷
              lp? ∷
              []
\end{code}
\end{document}
