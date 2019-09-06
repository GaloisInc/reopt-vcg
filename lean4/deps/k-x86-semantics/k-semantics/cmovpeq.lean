def cmovpeq1 : instruction :=
  definst "cmovpeq" $ do
    pattern fun (v_3244 : reg (bv 64)) (v_3245 : reg (bv 64)) => do
      v_5012 <- getRegister pf;
      v_5013 <- getRegister v_3244;
      v_5014 <- getRegister v_3245;
      setRegister (lhs.of_reg v_3245) (mux v_5012 v_5013 v_5014);
      pure ()
    pat_end;
    pattern fun (v_3240 : Mem) (v_3241 : reg (bv 64)) => do
      v_8258 <- getRegister pf;
      v_8259 <- evaluateAddress v_3240;
      v_8260 <- load v_8259 8;
      v_8261 <- getRegister v_3241;
      setRegister (lhs.of_reg v_3241) (mux v_8258 v_8260 v_8261);
      pure ()
    pat_end
