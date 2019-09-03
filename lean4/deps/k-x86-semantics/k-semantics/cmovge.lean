def cmovge1 : instruction :=
  definst "cmovge" $ do
    pattern fun (v_2568 : Mem) (v_2569 : reg (bv 32)) => do
      v_8992 <- getRegister sf;
      v_8994 <- getRegister of;
      v_8997 <- evaluateAddress v_2568;
      v_8998 <- load v_8997 4;
      v_8999 <- getRegister v_2569;
      setRegister (lhs.of_reg v_2569) (mux (eq (eq v_8992 (expression.bv_nat 1 1)) (eq v_8994 (expression.bv_nat 1 1))) v_8998 v_8999);
      pure ()
    pat_end;
    pattern fun (v_2585 : Mem) (v_2586 : reg (bv 64)) => do
      v_9002 <- getRegister sf;
      v_9004 <- getRegister of;
      v_9007 <- evaluateAddress v_2585;
      v_9008 <- load v_9007 8;
      v_9009 <- getRegister v_2586;
      setRegister (lhs.of_reg v_2586) (mux (eq (eq v_9002 (expression.bv_nat 1 1)) (eq v_9004 (expression.bv_nat 1 1))) v_9008 v_9009);
      pure ()
    pat_end;
    pattern fun (v_2602 : Mem) (v_2604 : reg (bv 16)) => do
      v_9012 <- getRegister sf;
      v_9014 <- getRegister of;
      v_9017 <- evaluateAddress v_2602;
      v_9018 <- load v_9017 2;
      v_9019 <- getRegister v_2604;
      setRegister (lhs.of_reg v_2604) (mux (eq (eq v_9012 (expression.bv_nat 1 1)) (eq v_9014 (expression.bv_nat 1 1))) v_9018 v_9019);
      pure ()
    pat_end
