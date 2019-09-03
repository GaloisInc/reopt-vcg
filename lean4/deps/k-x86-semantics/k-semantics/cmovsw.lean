def cmovsw1 : instruction :=
  definst "cmovsw" $ do
    pattern fun (v_3282 : reg (bv 16)) (v_3283 : reg (bv 16)) => do
      v_5175 <- getRegister sf;
      v_5177 <- getRegister v_3282;
      v_5178 <- getRegister v_3283;
      setRegister (lhs.of_reg v_3283) (mux (eq v_5175 (expression.bv_nat 1 1)) v_5177 v_5178);
      pure ()
    pat_end;
    pattern fun (v_3272 : Mem) (v_3274 : reg (bv 16)) => do
      v_8591 <- getRegister sf;
      v_8593 <- evaluateAddress v_3272;
      v_8594 <- load v_8593 2;
      v_8595 <- getRegister v_3274;
      setRegister (lhs.of_reg v_3274) (mux (eq v_8591 (expression.bv_nat 1 1)) v_8594 v_8595);
      pure ()
    pat_end
