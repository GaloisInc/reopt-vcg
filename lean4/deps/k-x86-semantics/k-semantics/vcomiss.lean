def vcomiss1 : instruction :=
  definst "vcomiss" $ do
    pattern fun (v_3006 : reg (bv 128)) (v_3007 : reg (bv 128)) => do
      v_6226 <- getRegister v_3007;
      v_6228 <- getRegister v_3006;
      v_6230 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_6226 96 128) (extract v_6228 96 128));
      v_6231 <- eval (eq v_6230 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_6231 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_6231 (eq v_6230 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_6231 (eq v_6230 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2999 : Mem) (v_3002 : reg (bv 128)) => do
      v_11617 <- getRegister v_3002;
      v_11619 <- evaluateAddress v_2999;
      v_11620 <- load v_11619 4;
      v_11621 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_11617 96 128) v_11620);
      v_11622 <- eval (eq v_11621 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_11622 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_11622 (eq v_11621 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_11622 (eq v_11621 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
