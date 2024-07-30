import Lake
open Lake DSL

package «learning-lean» where
  -- add package configuration options here

lean_lib «LearningLean» where
  -- add library configuration options here

@[default_target]
lean_exe «learning-lean» where
  root := `Main
