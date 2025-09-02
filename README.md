# LeanblueprintTesting

This document explains the repository layout, how to edit and
extend the blueprint, and how to compile and preview your work locally
before pushing changes. If you are already familiar with Git and Lean, you
can skim the command examples and jump straight to the section on writing
blueprint entries.

## Repository overview

The repository has two main parts:

1. Lean code lives under the MyProject/ directory. This is where
definitions and theorems about finite semigroup theory reside. For
instance, MyProject/GreensRelations.lean contains the definitions and
lemmas for Green's R, L, J, H and D relations. 
Currently, this repository contains only the definitoins of green's relations
and some duality lemmas, and only the first file (GreensRelations.lean) is
filled out in the blueprint as of now. 

2. Blueprint sources live under blueprint/. The file
blueprint/src/content.tex is the master table of contents for the
blueprint. While you could write all the LaTeX directly into this file,
It currently consists of a sequence of \input{…} commands, one per
section. Under blueprint/src/LaTeX/GreensRelations/ you will find
individual .tex files corresponding to sections of the blueprint (for
example Preorders.tex, EquivOfPreorder.tex, Equiv.tex, etc.).
Keeping each section in its own file makes it easier to edit and to track
changes. When you add a new section, create a new .tex file in this
directory and add a corresponding
\input{LaTeX/GreensRelations/<FileName>} line to content.tex.

The finished blueprint is rendered automatically by GitHub Actions. Every
push to the main branch triggers a build that compiles the Lean code,
generates HTML and PDF versions of the blueprint, and updates the
dependency graph. The results appear at
https://AydenLamp.github.io/thesis/ within
approximately five minutes of pushing.

## Getting started

1. Clone the repository. If you haven’t already, obtain a copy of the
project using Git:

```bash
git clone https://github.com/lean-summer-research/LeanblueprintTesting.git
cd LeanblueprintTesting
```
Always pull the latest changes before you start work:

```bash
git pull
```

2. Make changes to the Lean code or the LaTeX source. See the
sections below for details.

3. Compile the blueprint locally to check your LaTeX for errors. Run
the following command:

```bash
leanblueprint all
```

The all target runs the Lean compiler, extracts the blueprint
information, builds the dependency graph, and produces HTML and PDF
versions. The initial build can take several minutes.

Note that if you are not in this project's codespace/devcontainer, you
will need to install the `leanblueprint` command-line tool first. See
the leanblueprint for installation instructions: https://github.com/PatrickMassot/leanblueprint

4. Optionally, preview the blueprint locally. To inspect your changes before
pushing, run:

```bash
leanblueprint serve
```

5. This starts a local web server and prints a URL such as
http://localhost:8000. Open that URL in your browser to view the
blueprint. Leave this process running while you work; it will serve
updated pages whenever you rebuild.

6. Stopping the server. When you are finished previewing, return to
the terminal and press Ctrl+C to stop the server.

7. Saving and sharing your work

Once you have edited the .tex files and are happy with the local
preview, commit and push your changes:

```bash
git add blueprint/src/LaTeX/GreensRelations/<YourFile>.tex blueprint/src/content.tex MyProject/<files you changed>
```
Or, to add all changed files:

``` bash
git add .
```

Then, commit and push:

``` bash
git commit -m "Update blueprint: describe new lemma"
git push 
```

GitHub Actions will rebuild the site. After a few minutes, visit
https://lean-summer-research.github.io/LeanblueprintTesting/blueprint/ to
see the updated HTML blueprint. The PDF version is available via the
“Blueprint (pdf)” link on the project homepage.

If you encounter build errors, check the “Actions” tab on GitHub for
details. Typical issues include typos in labels, missing \lean
declarations, or unsatisfied dependencies.

## Writing blueprint entries

Blueprint documents are ordinary LaTeX files with a few additional macros
that connect the prose to the formal Lean code. Each definition,
lemma or theorem should be placed in its own environment and labelled.
Here is a template you can adapt:

```latex
\begin{definition}[Short name]
\label{def:MyDefinition}
Formal statement of your definition.  (Write the mathematics in
complete sentences.)

\lean{Namespace.myDefinition}
\leanok
\end{definition}

\begin{lemma}[Descriptive title]
\label{lem:MyLemma}
Statement of the lemma.
\lean{Namespace.myLemma}
\leanok
\uses{def:MyDefinition, def:OtherDefinition}
\end{lemma}

\begin{proof}
\leanok
Explain the proof in plain mathematical language.  Refer to earlier
results using `\ref{def:MyDefinition}` and list the proof dependencies
explicitly:
\uses{lem:OtherLemma, def:MyDefinition}
\end{proof}
```
Important conventions:

- Labels. Use \label{def:Name} for definitions, \label{lem:Name} for
lemmas, \label{thm:Name} for theorems and so on. These labels are
referenced both in the text (\ref{…}) and in the \uses{…} lines.

- \lean{…}. Inside each definition or lemma, add a \lean{…} line
with the full name of the corresponding Lean declaration. For example,
\lean{RRel} links the definition to the Lean constant RRel. This
macro ensures that the statement in the blueprint matches the Lean code and
produces a hyperlink to the generated documentation.

- \leanok. Place \leanok in every definition, lemma and proof to
assert that it has been fully formalised in Lean. If a statement or
proof has not yet been formalised, you can use \notready instead to
mark it as incomplete.

- Dependencies. Use \uses{…} to specify which earlier labelled
statements your lemma depends on. Separate multiple labels with commas.
In proofs, you can include an additional \uses{…} line at the end of
the proof environment to list the lemmas or definitions used in the
proof.

- Organising sections. Each .tex file should begin with a
\section{…} heading. Keep related statements together, but don’t
hesitate to split the blueprint into multiple smaller files and add them
to content.tex with \input. This makes it easier to navigate and
collaborate.

- Referencing Lean code. You can browse the Lean declarations via the
documentation link above. When deciding which \lean{…} name to use,
look for the declaration in the relevant file (e.g.
MyProject/GreensRelations.lean) and note its full name. Use that name
exactly in the \lean{…} macro. If a statement is split across
multiple lemmas in Lean, list all of them separated by spaces, or pick
the one that best matches your statement.