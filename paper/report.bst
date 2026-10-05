%% Transparent manuscript bibliography style; processed by genuine BibTeX.
%% Fields are rendered directly from the verified references.bib entries.
%% Citation order is retained. This style adds no bibliographic facts.
ENTRY
 { author title journal volume number pages year booktitle publisher
   institution type note doi url eprint archivePrefix primaryClass }
 {} {}
INTEGERS { nameptr namesleft numnames }
STRINGS { s t }

FUNCTION {format.names}
{ 's := #1 'nameptr := s num.names$ 'numnames :=
  numnames 'namesleft :=
  { namesleft #0 > }
  { s nameptr "{ff~}{vv~}{ll}{, jj}" format.name$ 't :=
    nameptr #1 >
      { namesleft #1 > { ", " * t * } { " and " * t * } if$ }
      { t } if$
    nameptr #1 + 'nameptr :=
    namesleft #1 - 'namesleft :=
  } while$
}

FUNCTION {write.optional}
{ duplicate$ empty$ { pop$ } { write$ } if$ }

FUNCTION {write.entry}
{ newline$ "\bibitem{" write$ cite$ write$ "}" write$ newline$
  author empty$ 'skip$ { author format.names write$ ". " write$ } if$
  title write.optional ". " write$
  journal empty$
    { booktitle empty$
        { institution empty$ 'skip$ { institution write$ ", " write$ } if$
          type empty$ 'skip$ { type write$ " " write$ } if$
          number empty$ 'skip$ { number write$ ", " write$ } if$ }
        { "In {\em " write$ booktitle write$ "}, " write$ } if$ }
    { "{\em " write$ journal write$ "}" write$
      volume empty$ 'skip$ { ", " write$ volume write$ } if$
      number empty$ 'skip$ { "(" write$ number write$ ")" write$ } if$
      ", " write$ } if$
  pages empty$ 'skip$ { "pp.~" write$ pages write$ ", " write$ } if$
  publisher empty$ 'skip$ { publisher write$ ", " write$ } if$
  year write.optional "." write$ newline$
  note empty$ 'skip$ { note write$ "." write$ newline$ } if$
  doi empty$ 'skip$
    { "DOI: \href{https://doi.org/" write$ doi write$ "}{\nolinkurl{" write$
      doi write$ "}}." write$ newline$ } if$
  url empty$ 'skip$ { "\url{" write$ url write$ "}." write$ newline$ } if$
  newline$
}
FUNCTION {article} { write.entry }
FUNCTION {inproceedings} { write.entry }
FUNCTION {techreport} { write.entry }
FUNCTION {misc} { write.entry }
FUNCTION {default.type} { write.entry }
FUNCTION {begin.bib}
{ "\begin{thebibliography}{99}" write$ newline$ }
FUNCTION {end.bib}
{ "\end{thebibliography}" write$ newline$ }
READ
EXECUTE {begin.bib}
ITERATE {call.type$}
EXECUTE {end.bib}
