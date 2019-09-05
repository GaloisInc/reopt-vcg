def subb1 : instruction :=
  definst "subb" $ do
    pattern fun (v_3193 : imm int) (v_3195 : reg (bv 8)) => do
      v_6220 <- eval (handleImmediateWithSignExtend v_3193 8 8);
      v_6224 <- getRegister v_3195;
      v_6226 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6220 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_6224));
      v_6227 <- eval (extract v_6226 1 9);
      v_6229 <- eval (isBitSet v_6226 1);
      v_6233 <- eval (eq (bv_xor (extract v_6220 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3195) v_6227;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6220 v_6224) 3) (isBitSet v_6226 4)));
      setRegister cf (notBool_ (isBitSet v_6226 0));
      setRegister of (bit_and (eq v_6233 (isBitSet v_6224 0)) (notBool_ (eq v_6233 v_6229)));
      setRegister pf (parityFlag v_6227);
      setRegister sf v_6229;
      setRegister zf (zeroFlag v_6227);
      pure ()
    pat_end;
    pattern fun (v_3208 : reg (bv 8)) (v_3209 : reg (bv 8)) => do
      v_6290 <- getRegister v_3208;
      v_6294 <- getRegister v_3209;
      v_6296 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6290 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_6294));
      v_6297 <- eval (extract v_6296 1 9);
      v_6299 <- eval (isBitSet v_6296 1);
      v_6303 <- eval (eq (bv_xor (extract v_6290 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3209) v_6297;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6290 v_6294) 3) (isBitSet v_6296 4)));
      setRegister cf (notBool_ (isBitSet v_6296 0));
      setRegister of (bit_and (eq v_6303 (isBitSet v_6294 0)) (notBool_ (eq v_6303 v_6299)));
      setRegister pf (parityFlag v_6297);
      setRegister sf v_6299;
      setRegister zf (zeroFlag v_6297);
      pure ()
    pat_end;
    pattern fun (v_3198 : Mem) (v_3199 : reg (bv 8)) => do
      v_9217 <- evaluateAddress v_3198;
      v_9218 <- load v_9217 1;
      v_9222 <- getRegister v_3199;
      v_9224 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9218 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_9222));
      v_9225 <- eval (extract v_9224 1 9);
      v_9227 <- eval (isBitSet v_9224 1);
      v_9231 <- eval (eq (bv_xor (extract v_9218 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3199) v_9225;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9218 v_9222) 3) (isBitSet v_9224 4)));
      setRegister cf (notBool_ (isBitSet v_9224 0));
      setRegister of (bit_and (eq v_9231 (isBitSet v_9222 0)) (notBool_ (eq v_9231 v_9227)));
      setRegister pf (parityFlag v_9225);
      setRegister sf v_9227;
      setRegister zf (zeroFlag v_9225);
      pure ()
    pat_end;
    pattern fun (v_3163 : imm int) (v_3162 : Mem) => do
      v_10778 <- evaluateAddress v_3162;
      v_10779 <- eval (handleImmediateWithSignExtend v_3163 8 8);
      v_10783 <- load v_10778 1;
      v_10785 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10779 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_10783));
      v_10786 <- eval (extract v_10785 1 9);
      store v_10778 v_10786 1;
      v_10789 <- eval (isBitSet v_10785 1);
      v_10793 <- eval (eq (bv_xor (extract v_10779 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10779 v_10783) 3) (isBitSet v_10785 4)));
      setRegister cf (notBool_ (isBitSet v_10785 0));
      setRegister of (bit_and (eq v_10793 (isBitSet v_10783 0)) (notBool_ (eq v_10793 v_10789)));
      setRegister pf (parityFlag v_10786);
      setRegister sf v_10789;
      setRegister zf (zeroFlag v_10786);
      pure ()
    pat_end;
    pattern fun (v_3171 : reg (bv 8)) (v_3170 : Mem) => do
      v_10846 <- evaluateAddress v_3170;
      v_10847 <- getRegister v_3171;
      v_10851 <- load v_10846 1;
      v_10853 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10847 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_10851));
      v_10854 <- eval (extract v_10853 1 9);
      store v_10846 v_10854 1;
      v_10857 <- eval (isBitSet v_10853 1);
      v_10861 <- eval (eq (bv_xor (extract v_10847 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10847 v_10851) 3) (isBitSet v_10853 4)));
      setRegister cf (notBool_ (isBitSet v_10853 0));
      setRegister of (bit_and (eq v_10861 (isBitSet v_10851 0)) (notBool_ (eq v_10861 v_10857)));
      setRegister pf (parityFlag v_10854);
      setRegister sf v_10857;
      setRegister zf (zeroFlag v_10854);
      pure ()
    pat_end
