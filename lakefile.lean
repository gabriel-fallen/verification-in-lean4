import Lake
open Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.13.0"

package «formal-verification» {
  -- add package configuration options here
}

@[default_target]
lean_lib «FormalVerification» {
  -- add library configuration options here
}
