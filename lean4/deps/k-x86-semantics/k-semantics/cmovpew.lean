def cmovpew1 : instruction :=
  definst "cmovpew" $ do
    pattern fun (v_3227 : reg (bv 16)) (v_3228 : reg (bv 16)) => do
      v_5118 <- getRegister pf;
      v_5120 <- getRegister v_3227;
      v_5121 <- getRegister v_3228;
      setRegister (lhs.of_reg v_3228) (mux (eq v_5118 (expression.bv_nat 1 1)) v_5120 v_5121);
      pure ()
    pat_end;
    pattern fun (v_3222 : Mem) (v_3223 : reg (bv 16)) => do
      v_8535 <- getRegister pf;
      v_8537 <- evaluateAddress v_3222;
      v_8538 <- load v_8537 2;
      v_8539 <- getRegister v_3223;
      setRegister (lhs.of_reg v_3223) (mux (eq v_8535 (expression.bv_nat 1 1)) v_8538 v_8539);
      pure ()
    pat_end
