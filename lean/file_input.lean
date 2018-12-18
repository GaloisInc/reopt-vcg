
import system.io -- init.category.lift

structure file_input_state := 
  (handle : io.handle)
  (pos : ℕ)
  (filename : string) -- for reopening 

/- A monad for dealing with the fact that lean doesn't support seeking backwards -/
@[reducible]
def file_input := state_t file_input_state (except_t string io)

namespace file_input

def new_state (filename : string) : io file_input_state := do 
  hdl <- io.mk_file_handle filename io.mode.read tt,
  return { handle := hdl, pos := 0, filename := filename } 

def run_file_input {a} (filename : string) (fr : file_input a) : io (except string a) := do
  st <- new_state filename,
  rv <- (fr.run st).run,
  return (rv.map prod.fst)

def read (n:ℕ) : file_input char_buffer := do
  s <- get,
  monad_lift (io.fs.read s.handle n)

def seek (n : ℕ) : file_input unit := do
  s <- get, 
  if s.pos < n 
  then monad_lift (io.fs.read s.handle (n - s.pos)) >> put { pos := n, ..s }
  else monad_lift (do s' <- new_state s.filename,
                      _  <- io.fs.read s'.handle n,
                      return { pos := n, ..s'}) >>= put 

end file_input
