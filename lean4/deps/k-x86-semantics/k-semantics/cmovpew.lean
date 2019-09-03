def cmovpew1 : instruction :=
  definst "cmovpew" $ do
    pattern fun (v_3163 : reg (bv 16)) (v_3164 : reg (bv 16)) => do
      v_5054 <- getRegister pf;
      v_5056 <- getRegister v_3163;
      v_5057 <- getRegister v_3164;
      setRegister (lhs.of_reg v_3164) (mux (eq v_5054 (expression.bv_nat 1 1)) v_5056 v_5057);
      pure ()
    pat_end;
    pattern fun (v_3160 : Mem) (v_3159 : reg (bv 16)) => do
      v_8549 <- getRegister pf;
      v_8551 <- evaluateAddress v_3160;
      v_8552 <- load v_8551 2;
      v_8553 <- getRegister v_3159;
      setRegister (lhs.of_reg v_3159) (mux (eq v_8549 (expression.bv_nat 1 1)) v_8552 v_8553);
      pure ()
    pat_end
