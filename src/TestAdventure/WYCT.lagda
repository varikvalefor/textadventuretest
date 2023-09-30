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

\newcommand\cmene{\texttt{WYCT}}

\title{la'o zoi.\ \cmene{}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \cmene{}\ .zoi.\ vasru le velcki be le kelci datni be le me'oi .default.\ ja me'oi .demo.\ ja co'e po la .tat.

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module TestAdventure.WYCT where

import Data.Fin

open import Data.Bool
  using (
    true;
    false
  )
open import Data.List
  using (
    List;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    just;
    nothing
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    _×_;
    _,_
  )
open import VVXtAdventure.Base
open import VVXtAdventure.Funky
open import TestAdventure.Items
open import Relation.Binary.PropositionalEquality
  using (
    refl
  )

import Data.Rational as ℚ
\end{code}

\section{le tolsti co'e}

\subsection{la'oi .\F{rooms}.}

\begin{code}
rooms : List Room
rooms = dingyliv ∷ dingycos ∷ []
  where
  dingycos : Room
  dingycos = record {
    name = "BROOM CLOSET";
    cname = "DINGYLIVCLST";
    travis = "DINGYLIVRM" ∷ [];
    items = []
    }
  dingyliv : Room
  dingyliv = record {
    name = "A DINGY LIVING ROOM";
    cname = "DINGYLIVRM";
    travis = "DINGYLIVCLST" ∷ [];
    items = lamp ∷ table ∷ colorfun ∷ []}
    where
    table : Item
    table = record {
      name = "FLIMSY TABLE";
      cname = "DINGYLIVRMTBL";
      weapwn = nothing;
      rmDescr = ("DINGYLIVRM" , lvdsc) ∷ [];
      dfDescr = "You see a flimsy-looking table.";
      hlDescr = "For some reason, you remove (from \
                \your living room) this flimsy-\
                \looking table.  Possible is that \
                \excessive carrying causes the \
                \degradation of the table; this thing \
                \looks like a real piece.\n\n\
                \The copious amounts (of duct tape, \
                \glue, and string) are the result of \
                \compensation for potential damage \
                \which may be the result of \
                \potentially excessive partying and \
                \whatnot.  Hackathons can be wild.";
      yourfloorisnowclean = refl
      }
      where
      lvdsc = "A flimsy-looking table is in the middle \
              \of the room.  Glue, duct tape, and other \
              \go-to tools of kludgers are attached to \
              \the table."
    lamp : Item
    lamp = record {
      name = "LAMP";
      cname = "DINGYLIVRMLMP";
      weapwn = nothing;
      rmDescr = ("DINGYLIVRM" , lvdsc) ∷ [];
      dfDescr = "You see a lamp.";
      hlDescr = "You took (from the living room \
                \which marks the beginning of your \
                \adventure) this mediocre lamp.";
      yourfloorisnowclean = refl}
      where
      lvdsc = "A pretty mediocre-looking lamp is \
              \nearby."
\end{code}

\subsection{la'oi .\F{winmsg}.}

\begin{code}
winmsg : String
winmsg = "YOU HAVE ACCOMPLISHED\n\
         \THE MISSION.\n\
         \YOU ARE THE VERY PREVAILER\n\
         \THAT PROTECT RIGHT\n\
         \AND JUSTICE.\n\
         \I WOULD EXPRESS MY SINCERE.\n\
         \THANKS TO YOU.\n\n\
         \\
         \TAKE GOOD REST !\n\n\
         \\
         \\tGENERAL KAWASAKI"

\end{code}

\subsection{la'oi .\F{initialD}.}

\begin{code}
initialD : GameData
initialD = record {
  rooms = rooms;
  epicwin = false;
  haters = kelci ∷ [];
  player' = Data.Fin.zero;
  yourfloorisnowclean = refl}
  where
  kelci = record {
    forename = "HARRIET";
    surname = "TUBMANN";
    cname = "XITAS";
    nicknames = "THE O.G. MEATBALL" ∷ [];
    health = ℚ.1ℚ;
    room = Data.Fin.zero;
    inventory = defstick ∷ [];
    wieldedct = nothing;
    yourfloorisnowclean = refl}
\end{code}
\end{document}
