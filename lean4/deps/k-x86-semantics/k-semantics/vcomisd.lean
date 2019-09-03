def vcomisd1 : instruction :=
  definst "vcomisd" $ do
    pattern fun (v_2997 : reg (bv 128)) (v_2998 : reg (bv 128)) => do
      v_6203 <- getRegister v_2998;
      v_6205 <- getRegister v_2997;
      v_6207 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_6203 64 128) (extract v_6205 64 128));
      v_6208 <- eval (eq v_6207 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_6208 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_6208 (eq v_6207 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_6208 (eq v_6207 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2990 : Mem) (v_2993 : reg (bv 128)) => do
      v_11598 <- getRegister v_2993;
      v_11600 <- evaluateAddress v_2990;
      v_11601 <- load v_11600 8;
      v_11602 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_11598 64 128) v_11601);
      v_11603 <- eval (eq v_11602 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_11603 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_11603 (eq v_11602 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_11603 (eq v_11602 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
