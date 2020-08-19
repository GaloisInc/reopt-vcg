def incb : instruction :=
  definst "incb" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      v_3 <- eval (add v_2 (expression.bv_nat 8 1));
      store v_1 v_3 1;
      (v_5 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_6 : expression (bv 7)) <- eval (extract v_2 1 8);
      (v_7 : expression (bv 4)) <- eval (extract v_2 4 8);
      setRegister af (eq v_7 (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_2 0) (eq v_6 (expression.bv_nat 7 127)));
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister (lhs.of_reg rh_0);
      v_2 <- eval (add v_1 (expression.bv_nat 8 1));
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      (v_4 : expression (bv 7)) <- eval (extract v_1 1 8);
      (v_5 : expression (bv 4)) <- eval (extract v_1 4 8);
      setRegister (lhs.of_reg rh_0) v_2;
      setRegister af (eq v_5 (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_1 0) (eq v_4 (expression.bv_nat 7 127)));
      setRegister pf (parityFlag v_3);
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end