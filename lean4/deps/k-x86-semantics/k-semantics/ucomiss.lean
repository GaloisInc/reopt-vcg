def ucomiss1 : instruction :=
  definst "ucomiss" $ do
    pattern fun (v_2537 : reg (bv 128)) (v_2538 : reg (bv 128)) => do
      v_4752 <- getRegister v_2538;
      v_4754 <- getRegister v_2537;
      v_4756 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4752 96 128) (extract v_4754 96 128));
      v_4757 <- eval (eq v_4756 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4757 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4757 (eq v_4756 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4757 (eq v_4756 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2530 : Mem) (v_2533 : reg (bv 128)) => do
      v_10321 <- getRegister v_2533;
      v_10323 <- evaluateAddress v_2530;
      v_10324 <- load v_10323 4;
      v_10325 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_10321 96 128) v_10324);
      v_10326 <- eval (eq v_10325 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_10326 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_10326 (eq v_10325 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_10326 (eq v_10325 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
