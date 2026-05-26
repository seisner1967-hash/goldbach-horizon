# TS20 - Horizon Goldbach Synthesis

This directory contains the TS20 synthesis manuscript:

- `TS20_Horizon_Goldbach_Synthesis.tex`

It is intended for XeLaTeX because it uses `fontspec`.

Suggested build command:

```powershell
xelatex TS20_Horizon_Goldbach_Synthesis.tex
xelatex TS20_Horizon_Goldbach_Synthesis.tex
```

The audited Lean scope for the manuscript is:

```text
TS/Goldbach/Strong/TS15
TS/Goldbach/Strong/TS16
TS/Goldbach/Strong/TS17
TS/Goldbach/Strong/TS18
TS/Goldbach/Strong/TS19
```

Expected audit:

```powershell
rg -n "s[o]rry" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19
rg -n "a[x]iom" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19
```

Expected output: no matches.
