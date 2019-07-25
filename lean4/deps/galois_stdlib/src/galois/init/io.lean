
/- Low-level API doing file IO -/

namespace Galois

/- c.f. Prim.Fs.handle in library/init/io.lean -/

inductive Fs.Mode
| read | write | readWrite | append

inductive Fs.Whence
| set | cur | seek_end | hole | data

constant Fs.handle : Type := Unit

namespace IO
namespace Prim

open Fs

@[extern 4 cpp "galois::io::prim::handle::mk"]
constant handle.mk (s : @& String) (m : Mode) (bin : Bool := false) : IO handle := default _
-- @[extern 2 cpp "galois::io::prim::handle::do_is_eof"]
-- constant handle.isEof (h : @& handle) : IO Bool := default _
-- @[extern 2 cpp "galois::io::prim::handle::do_flush"]
-- constant handle.flush (h : @& handle) : IO Unit := default _
@[extern 2 cpp "galois::io::prim::handle::do_close"]
constant handle.close (h : @& handle) : IO Unit := default _
@[extern 3 cpp "galois::io::prim::handle::do_read"]
constant handle.read (h : @& handle) (len : Nat) : IO ByteArray := default _
@[extern 3 cpp "galois::io::prim::handle::do_write"]
constant handle.write (h : @& handle) (data : @& ByteArray) : IO Unit := default _
@[extern 4 cpp "galois::io::prim::handle::do_lseek"]
constant handle.lseek (h : @& handle) (off : Int) (whence : Whence): IO Nat := default _

end Prim
end IO
end Galois
