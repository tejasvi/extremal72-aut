import Lake
open Lake DSL

-- Toolchain leanprover/lean4:v4.35.0-rc3 and Mathlib at tag v4.35.0-rc3 (commit c55e6e786f49, see lake-manifest.json).
-- One thread per Lean process: `-j1` on every library.
-- Build a library with `lake build <name>`; README.md lists the libraries and how to check the controls.
package c72t1 where
  -- Elab.async false: no extra elaboration threads; it has no effect on what is checked.
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩,
    ⟨`Elab.async, false⟩]
  moreLeanArgs := #["-j1"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0-rc3"

-- T1: definitions, final deduction, decomposition, labelling, tests, refutations, axiom report.
@[default_target]
lean_lib C72T1 where
  roots := #[`C72T1]
  -- every module of C72T1/, including C72T1.Axioms, which the root does not import (so importers do not replay
  -- the axiom report)
  globs := #[.andSubmodules `C72T1]
  moreLeanArgs := #["-j1"]

-- The paper-form statements: the module C72T1.Paper, also imported by the C72T1 root.
lean_lib Paper where
  roots := #[`C72T1.Paper]
  moreLeanArgs := #["-j1"]

-- One library per part, each over its own module dir (C72T2/ order 3, C72T3/ order 5, C72T4/ order 2).
-- A library builds once its dir exists.
lean_lib C72T2 where
  globs := #[.submodules `C72T2]
  moreLeanArgs := #["-j1"]

lean_lib C72T3 where
  globs := #[.submodules `C72T3]
  moreLeanArgs := #["-j1"]

lean_lib C72T4 where
  globs := #[.submodules `C72T4]
  moreLeanArgs := #["-j1"]

-- Must-fail controls: one library per part over its own dir (C72T2Controls/, C72T3Controls/,
-- C72T4Controls/), so that building a part's library does not build the controls.
lean_lib C72T2Controls where
  globs := #[.submodules `C72T2Controls]
  moreLeanArgs := #["-j1"]

lean_lib C72T3Controls where
  globs := #[.submodules `C72T3Controls]
  moreLeanArgs := #["-j1"]

lean_lib C72T4Controls where
  globs := #[.submodules `C72T4Controls]
  moreLeanArgs := #["-j1"]

-- T6, order-2 part (Lemma 6.1 (b), the slice property, Lemma 6.3, converse directions), and its controls.
lean_lib C72T6 where
  globs := #[.submodules `C72T6]
  moreLeanArgs := #["-j1"]

lean_lib C72T6Controls where
  globs := #[.submodules `C72T6Controls]
  moreLeanArgs := #["-j1"]

-- T6, order-3 part (Lemma 4.4 with certified M24 facts, Prop. 4.3 converse and class invariance), and its controls.
lean_lib C72T6O3 where
  globs := #[.submodules `C72T6O3]
  moreLeanArgs := #["-j1"]

lean_lib C72T6O3Controls where
  globs := #[.submodules `C72T6O3Controls]
  moreLeanArgs := #["-j1"]

-- T5, the assembly (the Main Theorem from the 12 named hypotheses), and its controls.
lean_lib C72T5 where
  globs := #[.submodules `C72T5]
  moreLeanArgs := #["-j1"]

lean_lib C72T5Controls where
  globs := #[.submodules `C72T5Controls]
  moreLeanArgs := #["-j1"]

-- T6, order-5 part (Lemma 2.5, the normal form), and its controls.
lean_lib C72T6O5 where
  globs := #[.submodules `C72T6O5]
  moreLeanArgs := #["-j1"]

lean_lib C72T6O5Controls where
  globs := #[.submodules `C72T6O5Controls]
  moreLeanArgs := #["-j1"]

-- T6, order-2 part, further results (the bridge `H_D_of_search`, the coset table, (diag) and `Bad(y)` on a
-- basis), in a library of their own.
lean_lib C72T6D where
  globs := #[.submodules `C72T6D]
  moreLeanArgs := #["-j1"]

-- T6, Klein part (Lemma 3.4, Lemma 3.5 (b), (c) for forms, Propositions 3.7 and 3.8), and its controls.
lean_lib C72T6K where
  globs := #[.submodules `C72T6K]
  moreLeanArgs := #["-j1"]

lean_lib C72T6KControls where
  globs := #[.submodules `C72T6KControls]
  moreLeanArgs := #["-j1"]

-- The Main Theorem with the weaker form H_L2_sd of (L2); the library C72T5 is unchanged.
lean_lib C72T5W where
  globs := #[.submodules `C72T5W]
  moreLeanArgs := #["-j1"]

-- Must-fail controls: each module of this library is built on its own and must NOT build.
lean_lib C72T1Controls where
  globs := #[.submodules `C72T1Controls]
  moreLeanArgs := #["-j1"]

-- Plants for the control checker `check_controls.sh`: each module here must make the checker report FAIL.
lean_lib C72T1Plants where
  globs := #[.submodules `C72T1Plants]
  moreLeanArgs := #["-j1"]
