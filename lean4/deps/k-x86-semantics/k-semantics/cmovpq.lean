def cmovpq1 : instruction :=
  definst "cmovpq" $ do
    pattern fun (v_3272 : reg (bv 64)) (v_3273 : reg (bv 64)) => do
      v_5171 <- getRegister pf;
      v_5173 <- getRegister v_3272;
      v_5174 <- getRegister v_3273;
      setRegister (lhs.of_reg v_3273) (mux (eq v_5171 (expression.bv_nat 1 1)) v_5173 v_5174);
      pure ()
    pat_end;
    pattern fun (v_3267 : Mem) (v_3268 : reg (bv 64)) => do
      v_8573 <- getRegister pf;
      v_8575 <- evaluateAddress v_3267;
      v_8576 <- load v_8575 8;
      v_8577 <- getRegister v_3268;
      setRegister (lhs.of_reg v_3268) (mux (eq v_8573 (expression.bv_nat 1 1)) v_8576 v_8577);
      pure ()
    pat_end
