def cmovpw1 : instruction :=
  definst "cmovpw" $ do
    pattern fun (v_3281 : reg (bv 16)) (v_3282 : reg (bv 16)) => do
      v_5181 <- getRegister pf;
      v_5183 <- getRegister v_3281;
      v_5184 <- getRegister v_3282;
      setRegister (lhs.of_reg v_3282) (mux (eq v_5181 (expression.bv_nat 1 1)) v_5183 v_5184);
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 16)) => do
      v_8580 <- getRegister pf;
      v_8582 <- evaluateAddress v_3276;
      v_8583 <- load v_8582 2;
      v_8584 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3277) (mux (eq v_8580 (expression.bv_nat 1 1)) v_8583 v_8584);
      pure ()
    pat_end
