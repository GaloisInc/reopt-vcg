
import SmtLib.Syntax
import SmtLib.BitVec


namespace Smt

@[reducible]
protected def SmtSort.denote : SmtSort → Type
| SmtSort.bool => Bool
| SmtSort.bitvec n => BitVec n
| SmtSort.array k v => List (k.denote × v.denote)
-- ^ FIXME an association list would work, but obviously isn't very performant...

-- FIXME / BOOKMARK ... Beq seems more flexible here and allows us to trivially not
-- care about the bitvec proofs or structure of array representation... but of course
-- we don't then get propositional equality =\
axiom SmtSort.denoteHasBeq : forall (s: SmtSort) , HasBeq s.denote

namespace Raw

namespace ConstSort

@[reducible]
protected def denote : ConstSort → Type
| ConstSort.base s => s.denote
| ConstSort.fsort a b => a.denote → b.denote

end ConstSort

-- TODO? SpecConst

@[reducible]
protected def BuiltinIdent.denote : forall cs, BuiltinIdent cs → cs.denote
-- * Core theory
| _, BuiltinIdent.true => true
| _, BuiltinIdent.false => false
| _, BuiltinIdent.not => not
| _, BuiltinIdent.impl => λ p q => !p || q
| _, BuiltinIdent.and => and
| _, BuiltinIdent.or => or
| _, BuiltinIdent.xor => xor
| _, BuiltinIdent.eq s => (SmtSort.denoteHasBeq s).beq
-- | _, smtIte _             => atom "ite"
-- | _, distinct _ _         => atom "distinct"

-- | _, select _ _           => atom "select"
-- | _, store  _ _           => atom "store"
-- | _, eqrange _ _          => atom "eqrange"

-- -- * BitVecs
-- -- hex/binary literals
-- | _, concat _ _           => atom "concat"
-- | _, extract _ i j        => indexed (atom "extract") [Nat.toSExpr i, Nat.toSExpr j]
-- -- unops
-- | _, bvnot   _            => atom "bvnot"
-- | _, bvneg   _            => atom "bvneg"
-- -- binops                   
-- | _, bvand   _            => atom "bvand"
-- | _, bvor    _            => atom "bvor"
-- | _, bvadd   _            => atom "bvadd"
-- | _, bvmul   _            => atom "bvmul"
-- | _, bvudiv  _            => atom "bvudiv"
-- | _, bvurem  _            => atom "bvurem"
-- | _, bvshl   _            => atom "bvshl"
-- | _, bvlshr  _            => atom "bvlshr"
-- -- comparison               
-- | _, bvult   _            => atom "bvult"

-- | _, bvnand  _            => atom "bvnand" 
-- | _, bvnor   _            => atom "bvnor" 
-- | _, bvxor   _            => atom "bvxor"  
-- | _, bvxnor  _            => atom "bvxnor"  
-- | _, bvcomp  _            => atom "bvcomp" 
-- | _, bvsub   _            => atom "bvsub" 
-- | _, bvsdiv  _            => atom "bvsdiv"
-- | _, bvsrem  _            => atom "bvsrem" 
-- | _, bvsmod  _            => atom "bvsmod" 
-- | _, bvashr  _            => atom "bvashr" 

-- | _, repeat i _           => indexed (atom "repeat") [Nat.toSExpr i]

-- | _, zeroExtend  i _     => indexed (atom "zero_extend")  [Nat.toSExpr i]
-- | _, signExtend  i _     => indexed (atom "sign_extend")  [Nat.toSExpr i]
-- | _, rotateLeft  i _     => indexed (atom "rotate_left")  [Nat.toSExpr i]
-- | _, rotateRight i _     => indexed (atom "rotate_right") [Nat.toSExpr i]

-- | _, bvule _              => atom "bvule" 
-- | _, bvugt _              => atom "bvugt" 
-- | _, bvuge _              => atom "bvuge" 
-- | _, bvslt _              => atom "bvslt" 
-- | _, bvsle _              => atom "bvsle" 
-- | _, bvsgt _              => atom "bvsgt" 
-- | _, bvsge _              => atom "bvsge" 
| _, _                    => "TODO"


end Raw

end Smt
