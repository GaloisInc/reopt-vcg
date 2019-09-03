def cmovle1 : instruction :=
  definst "cmovle" $ do
    pattern fun (v_2646 : Mem) (v_2647 : reg (bv 32)) => do
      v_9022 <- getRegister zf;
      v_9024 <- getRegister sf;
      v_9026 <- getRegister of;
      v_9031 <- evaluateAddress v_2646;
      v_9032 <- load v_9031 4;
      v_9033 <- getRegister v_2647;
      setRegister (lhs.of_reg v_2647) (mux (bit_or (eq v_9022 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9024 (expression.bv_nat 1 1)) (eq v_9026 (expression.bv_nat 1 1))))) v_9032 v_9033);
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) (v_2664 : reg (bv 64)) => do
      v_9036 <- getRegister zf;
      v_9038 <- getRegister sf;
      v_9040 <- getRegister of;
      v_9045 <- evaluateAddress v_2663;
      v_9046 <- load v_9045 8;
      v_9047 <- getRegister v_2664;
      setRegister (lhs.of_reg v_2664) (mux (bit_or (eq v_9036 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9038 (expression.bv_nat 1 1)) (eq v_9040 (expression.bv_nat 1 1))))) v_9046 v_9047);
      pure ()
    pat_end;
    pattern fun (v_2680 : Mem) (v_2682 : reg (bv 16)) => do
      v_9050 <- getRegister zf;
      v_9052 <- getRegister sf;
      v_9054 <- getRegister of;
      v_9059 <- evaluateAddress v_2680;
      v_9060 <- load v_9059 2;
      v_9061 <- getRegister v_2682;
      setRegister (lhs.of_reg v_2682) (mux (bit_or (eq v_9050 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9052 (expression.bv_nat 1 1)) (eq v_9054 (expression.bv_nat 1 1))))) v_9060 v_9061);
      pure ()
    pat_end
