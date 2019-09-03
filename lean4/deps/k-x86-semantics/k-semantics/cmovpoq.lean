def cmovpoq1 : instruction :=
  definst "cmovpoq" $ do
    pattern fun (v_3202 : reg (bv 64)) (v_3203 : reg (bv 64)) => do
      v_5098 <- getRegister pf;
      v_5101 <- getRegister v_3202;
      v_5102 <- getRegister v_3203;
      setRegister (lhs.of_reg v_3203) (mux (notBool_ (eq v_5098 (expression.bv_nat 1 1))) v_5101 v_5102);
      pure ()
    pat_end;
    pattern fun (v_3198 : Mem) (v_3199 : reg (bv 64)) => do
      v_8544 <- getRegister pf;
      v_8547 <- evaluateAddress v_3198;
      v_8548 <- load v_8547 8;
      v_8549 <- getRegister v_3199;
      setRegister (lhs.of_reg v_3199) (mux (notBool_ (eq v_8544 (expression.bv_nat 1 1))) v_8548 v_8549);
      pure ()
    pat_end
