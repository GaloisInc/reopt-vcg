def vcomiss1 : instruction :=
  definst "vcomiss" $ do
    pattern fun (v_2993 : reg (bv 128)) (v_2994 : reg (bv 128)) => do
      v_5767 <- getRegister v_2994;
      v_5769 <- getRegister v_2993;
      v_5771 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_5767 96 128) (extract v_5769 96 128));
      v_5772 <- eval (eq v_5771 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_5772 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_5772 (eq v_5771 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_5772 (eq v_5771 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2986 : Mem) (v_2989 : reg (bv 128)) => do
      v_10075 <- getRegister v_2989;
      v_10077 <- evaluateAddress v_2986;
      v_10078 <- load v_10077 4;
      v_10079 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_10075 96 128) v_10078);
      v_10080 <- eval (eq v_10079 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_10080 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_10080 (eq v_10079 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_10080 (eq v_10079 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
