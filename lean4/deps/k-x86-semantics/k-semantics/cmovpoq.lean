def cmovpoq1 : instruction :=
  definst "cmovpoq" $ do
    pattern fun (v_3280 : reg (bv 64)) (v_3281 : reg (bv 64)) => do
      v_5049 <- getRegister pf;
      v_5051 <- getRegister v_3280;
      v_5052 <- getRegister v_3281;
      setRegister (lhs.of_reg v_3281) (mux (notBool_ v_5049) v_5051 v_5052);
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 64)) => do
      v_8283 <- getRegister pf;
      v_8285 <- evaluateAddress v_3276;
      v_8286 <- load v_8285 8;
      v_8287 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3277) (mux (notBool_ v_8283) v_8286 v_8287);
      pure ()
    pat_end
