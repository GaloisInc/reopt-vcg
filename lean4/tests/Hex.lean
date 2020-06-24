
import Galois.Init.Nat

namespace Test

namespace Hex

def test : IO UInt32 := do
-- Printing hex at the minimal width
IO.println $ Nat.ppHex 0;
IO.println $ Nat.ppHex 15;
IO.println $ Nat.ppHex 42;
-- Printing hex at specified widths
IO.println $ Nat.ppHexAtWidth 0 1;
IO.println $ Nat.ppHexAtWidth 15 1;
IO.println $ Nat.ppHexAtWidth 42 1;
IO.println $ Nat.ppHexAtWidth 0 10;
IO.println $ Nat.ppHexAtWidth 15 10;
IO.println $ Nat.ppHexAtWidth 42 10;
-- Parsing Hex
IO.println $ repr $ Nat.fromHexString "0x";
IO.println $ repr $ Nat.fromHexString "0xabcdefg";
IO.println $ repr $ Nat.fromHexString "0x0";
IO.println $ repr $ Nat.fromHexString "0x00";
IO.println $ repr $ Nat.fromHexString "0xf";
IO.println $ repr $ Nat.fromHexString "0xF";
IO.println $ repr $ Nat.fromHexString "0x0f";
IO.println $ repr $ Nat.fromHexString "0x2a";
IO.println $ repr $ Nat.fromHexString "0x02a";
IO.println $ repr $ Nat.fromHexString "0x02A";
pure 0

end Hex
end Test


