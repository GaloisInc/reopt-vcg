
import system.io

import .instruction
import .sexp -- debugging

namespace decodex86
/- 
 This function decodes the contents of input using the helper binary
 located at path.  The binary is expected to be llvm-tablegen-support
 (from this same repo).  The result of this function is a
 decodex86.document, i.e. a list of instructions (or unknown bytes)
 along with their offset from the start of the buffer.

  In the case of error a string is returned.
-/
def decode (path : string) (input : char_buffer) : io (sum string decodex86.document) :=
  -- Create process with piped stdin/stdout.
  let piped_args : io.process.spawn_args :=
        { stdin := io.process.stdio.piped
        , stdout := io.process.stdio.piped
        , cmd    := path
        , args   := [ repr (buffer.size input) ]
        } in do
  io.put_str_ln "Starting process",

  child ← io.proc.spawn piped_args,

  -- Write input to child stdin
  io.fs.write child.stdin input,
  io.fs.close child.stdin,
  -- Read input from child stdout
  buf ← io.fs.read_to_end child.stdout,
  io.fs.close child.stdout,
  -- Wait for process to exit
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  -- Decode buffer
  return (decodex86.from_buffer buf)
  
end decodex86

/-
def main : io unit := do
  args ← io.cmdline_args,
  match args with
  | [ decoder, path ] := do
      h <- io.mk_file_handle path io.mode.read tt,
      buf <- io.fs.read_to_end h,
      res  <- decodex86.decode decoder buf,
      match res with
      | (sum.inl e) := io.fail ("Decode error: " ++ e)
      | (sum.inr r) := io.put_str_ln (repr r)
      end
  | _ := io.fail "Need a raw binary as input"
  end
-/
