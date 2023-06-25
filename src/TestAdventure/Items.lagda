\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\kulmodis{\textttt{TestAdventure.Items}}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}
\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \kulmodis\ .zoi.\ vasru le velcki be le ctaipe be la'oi .\F{Item}.\ be'o poi ke'a srana la'oi .TestAdventure.

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module TestAdventure.Items where

open import Data.List
open import Data.Maybe
open import Data.String
open import VVXtAdventure.Base
open import Relation.Binary.PropositionalEquality
  using (
    refl
  )
\end{code}

\section{le ctaipe be la'oi .\F{Item}.

\subsection{la'oi .\F{macguffin}.}
ni'o la'oi .\F{macguffin}.\ me'oi .coupon. lo mu'oi glibau.\ leafblower .glibau.

\begin{code}
macguffin : Item
macguffin = record {
  name = "LEAFBLOWER COUPON";
  cname = "LEBLOCO";
  rmDescr = [];
  yourfloorisnowclean = refl;
  weapwn = nothing;
  dfDescr = "You see a coupon (for a leafblower) \
            \which is ludicrously detailed.";
  hlDescr = m}
  where
  m = "You hold a coupon for a \"super-bitchin' XL \
      \DAX and BLEXER High-Throughput Leafblower \
      \476.5: Beefcake Edition\".  Most men whom \
      \you know insist that the naming scheme is a \
      \bit ridiculous... but can still respect the \
      \perceived quality of DAX AND BLEXER's \
      \products.\n\n\
      \You find that this coupon is noteworthy \
      \partially because you suspect that the \
      \creators of the coupon probably wanted to \
      \ create a brochure or something, as opposed \
      \to a simple coupon.\n\n\
      \Anyway, the full text of the coupon is as \
      \follows:\n\n\
      \Hey, asshole.  Are you sick of those leaves \
      \blowing onto the driveway of your awesome \
      \penthouse/dungeon/library combo resort?  \
      \Don't bother answering.  Here at DAX AND \
      \BLEXER, we can always successfully read \
      \minds 82.3745 PERCENT OF THE TIME.  We KNOW \
      \that you're sick of those punk-ass leaves, \
      \and, frankly, we're sick of those punk-ass \
      \leaves, as well.  The whole situation makes \
      \us at DAX and BLEXER want to spew chunks all \
      \over this pig sty.  That's why we're \
      \offering you the following SWEET-ASS \
      \OPPORTUNITY: You can get this SUPER-BITCHIN' \
      \DAX and BLEXER High-Throughput Leafblower \
      \476.5: Beefcake Edition... for only $3200.99\
      \!  We are offering you a discount of 79%.  \
      \This is the discount of a lifetime, man.  \
      \Half of the poor bastards who tested this \
      \ended up dead as a result of the sheer \
      \power, but we at DAX and BLEXER believe that \
      \you, sir, ma'am, or disembodied fish head, \
      \are capable of successfully wielding this \
      \fucking monster.\n\n\
      \COUPON ID: GEbAhcurrjPROix7inD6YmY4W0szXtB35v\
      \EJluAqHLDdPFJVIu3N23lQEzVPWv81FpRcq\n\n\
      \This paragraph marks the end of the \
      \transcription.  Some additional information \
      \follows.\n\n\
      \The upper-left portion of the coupon \
      \is a photograph whose subject is a sweating \
      \body-builder who is using a leafblower.  The \
      \brand name of the leafblower is conveniently \
      \obscured.\n\n\
      \Additionally, a cheesy \"word art\" pop-out \
      \star which reads \"HOLY SHIT!\" is placed on \
      \the right margin of the small coupon.  Lines \
      \which connect this star to the sequences \
      \\"82.3745\" and \"79%\" are drawn."
\end{code}
\end{document}
