import Lake
open Lake DSL

package «matrix-tu-experimental» {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib MatrixTuExperimental {
  -- add any library configuration options here
}
