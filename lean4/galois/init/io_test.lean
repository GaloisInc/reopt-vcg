
import galois.init.io

def main (xs : List String) : IO UInt32 := do
  hdl <- Galois.IO.Prim.handle.mk "foo.txt" Galois.Fs.Mode.readWrite,
  _ <- let bytes := ByteArray.push ByteArray.empty 0x42 in Galois.IO.Prim.handle.write hdl bytes,
  _ <- Galois.IO.Prim.handle.lseek hdl 100 Galois.Fs.Whence.set,
  _ <- let bytes := ByteArray.push ByteArray.empty 0x33 in Galois.IO.Prim.handle.write hdl bytes,
  pure 0

  -- ctx ← newLLVMContext,
  -- mb ← newMemoryBufferFromFile xs.head,
  -- m ← parseBitcodeFile mb ctx,

  -- getModuleIdentifier m >>= IO.println,

  -- setModuleIdentifier m "Bob",
  -- getModuleIdentifier m >>= IO.println,
  -- pure 0

