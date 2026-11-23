import Lake
open Lake DSL

package collatz_adic_lean where
  version := v!"0.1.0"

@[default_target]
lean_lib CollatzAdicBase where
  roots := #[`CollatzAdicBase]
