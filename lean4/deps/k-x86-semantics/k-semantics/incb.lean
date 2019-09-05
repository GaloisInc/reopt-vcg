def incb1 : instruction :=
  definst "incb" $ do
    pattern fun (v_3041 : reg (bv 8)) => do
      v_5220 <- getRegister v_3041;
      v_5221 <- eval (add v_5220 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_3041) v_5221;
      setRegister af (eq (extract v_5220 4 8) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_5220 0)) (eq (extract v_5220 1 8) (expression.bv_nat 7 127)));
      setRegister pf (parityFlag (extract v_5221 0 8));
      setRegister sf (isBitSet v_5221 0);
      setRegister zf (zeroFlag v_5221);
      pure ()
    pat_end;
    pattern fun (v_3034 : Mem) => do
      v_9143 <- evaluateAddress v_3034;
      v_9144 <- load v_9143 1;
      v_9145 <- eval (add v_9144 (expression.bv_nat 8 1));
      store v_9143 v_9145 1;
      setRegister af (eq (extract v_9144 4 8) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_9144 0)) (eq (extract v_9144 1 8) (expression.bv_nat 7 127)));
      setRegister pf (parityFlag (extract v_9145 0 8));
      setRegister sf (isBitSet v_9145 0);
      setRegister zf (zeroFlag v_9145);
      pure ()
    pat_end
