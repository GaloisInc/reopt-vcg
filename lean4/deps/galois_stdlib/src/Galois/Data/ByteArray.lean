import Galois.Data.Array


namespace ByteArray

def lt (xs ys : ByteArray) : Bool := Array.lt xs.data ys.data


private def appendCharAsBytes (c:Char) (bs : List UInt8) : List UInt8 :=
  let b1  : UInt8 := UInt8.ofNat $ (c.val.land 0x000000FF).toNat;
  let b2  : UInt8 := UInt8.ofNat $ (c.val.land 0x0000FF00).toNat;
  let b3  : UInt8 := UInt8.ofNat $ (c.val.land 0x00FF0000).toNat;
  let b4  : UInt8 := UInt8.ofNat $ (c.val.land 0xFF000000).toNat;
  b1::b2::b3::b4::bs

def fromString (s:String) : ByteArray := 
   (s.data.foldr appendCharAsBytes []).toByteArray

end ByteArray
