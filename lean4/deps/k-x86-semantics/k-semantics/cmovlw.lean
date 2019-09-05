def cmovlw1 : instruction :=
  definst "cmovlw" $ do
    pattern fun (v_2771 : reg (bv 16)) (v_2772 : reg (bv 16)) => do
      v_4511 <- getRegister sf;
      v_4513 <- getRegister of;
      v_4517 <- getRegister v_2771;
      v_4518 <- getRegister v_2772;
      setRegister (lhs.of_reg v_2772) (mux (notBool_ (eq (eq v_4511 (expression.bv_nat 1 1)) (eq v_4513 (expression.bv_nat 1 1)))) v_4517 v_4518);
      pure ()
    pat_end;
    pattern fun (v_2766 : Mem) (v_2767 : reg (bv 16)) => do
      v_8084 <- getRegister sf;
      v_8086 <- getRegister of;
      v_8090 <- evaluateAddress v_2766;
      v_8091 <- load v_8090 2;
      v_8092 <- getRegister v_2767;
      setRegister (lhs.of_reg v_2767) (mux (notBool_ (eq (eq v_8084 (expression.bv_nat 1 1)) (eq v_8086 (expression.bv_nat 1 1)))) v_8091 v_8092);
      pure ()
    pat_end
