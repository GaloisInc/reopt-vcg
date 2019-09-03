def cmovew1 : instruction :=
  definst "cmovew" $ do
    pattern fun (v_2565 : reg (bv 16)) (v_2566 : reg (bv 16)) => do
      v_4251 <- getRegister zf;
      v_4253 <- getRegister v_2565;
      v_4254 <- getRegister v_2566;
      setRegister (lhs.of_reg v_2566) (mux (eq v_4251 (expression.bv_nat 1 1)) v_4253 v_4254);
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2561 : reg (bv 16)) => do
      v_7922 <- getRegister zf;
      v_7924 <- evaluateAddress v_2559;
      v_7925 <- load v_7924 2;
      v_7926 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2561) (mux (eq v_7922 (expression.bv_nat 1 1)) v_7925 v_7926);
      pure ()
    pat_end
