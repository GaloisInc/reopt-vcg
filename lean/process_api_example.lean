-- This is a file that illustrates using the Lean process API to shell out to
-- a process

import system.io

-- Run the given command with the provided input, and return a string with all
-- information written to stdout.
def run_with_input (args:io.process.spawn_args) (input:string) : io string := do
  -- Create process with piped stdin/stdout.
  let piped_args : io.process.spawn_args :=
        { stdin := io.process.stdio.piped
        , stdout := io.process.stdio.piped
        , ..args
        } in do
  child ← io.proc.spawn piped_args,

  -- Write input to child stdin
  io.fs.put_str child.stdin input,
  io.fs.close child.stdin,
  -- Read input from child stdout
  buf ← io.fs.read_to_end child.stdout,
  io.fs.close child.stdout,
  -- Wait for process to exit
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  -- Return buffer
  pure buf.to_string


def main : io unit := do
  msg ← run_with_input { cmd := "/bin/cat" } "Hello World",
  io.put_str_ln msg
