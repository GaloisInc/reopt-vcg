def cmovle1 : instruction :=
  definst "cmovle" $ do
    pattern fun (v_2697 : Mem) (v_2700 : reg (bv 32)) => do
      v_9003 <- getRegister zf;
      v_9005 <- getRegister sf;
      v_9007 <- getRegister of;
      v_9012 <- evaluateAddress v_2697;
      v_9013 <- load v_9012 4;
      v_9014 <- getRegister v_2700;
      setRegister (lhs.of_reg v_2700) (mux (bit_or (eq v_9003 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9005 (expression.bv_nat 1 1)) (eq v_9007 (expression.bv_nat 1 1))))) v_9013 v_9014);
      pure ()
    pat_end;
    pattern fun (v_2715 : Mem) (v_2714 : reg (bv 64)) => do
      v_9017 <- getRegister zf;
      v_9019 <- getRegister sf;
      v_9021 <- getRegister of;
      v_9026 <- evaluateAddress v_2715;
      v_9027 <- load v_9026 8;
      v_9028 <- getRegister v_2714;
      setRegister (lhs.of_reg v_2714) (mux (bit_or (eq v_9017 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9019 (expression.bv_nat 1 1)) (eq v_9021 (expression.bv_nat 1 1))))) v_9027 v_9028);
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2731 : reg (bv 16)) => do
      v_9031 <- getRegister zf;
      v_9033 <- getRegister sf;
      v_9035 <- getRegister of;
      v_9040 <- evaluateAddress v_2732;
      v_9041 <- load v_9040 2;
      v_9042 <- getRegister v_2731;
      setRegister (lhs.of_reg v_2731) (mux (bit_or (eq v_9031 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9033 (expression.bv_nat 1 1)) (eq v_9035 (expression.bv_nat 1 1))))) v_9041 v_9042);
      pure ()
    pat_end
