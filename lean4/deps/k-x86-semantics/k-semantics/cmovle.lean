def cmovle1 : instruction :=
  definst "cmovle" $ do
    pattern fun (v_2635 : Mem) (v_2634 : reg (bv 32)) => do
      v_9081 <- getRegister zf;
      v_9083 <- getRegister sf;
      v_9085 <- getRegister of;
      v_9090 <- evaluateAddress v_2635;
      v_9091 <- load v_9090 4;
      v_9092 <- getRegister v_2634;
      setRegister (lhs.of_reg v_2634) (mux (bit_or (eq v_9081 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9083 (expression.bv_nat 1 1)) (eq v_9085 (expression.bv_nat 1 1))))) v_9091 v_9092);
      pure ()
    pat_end;
    pattern fun (v_2651 : Mem) (v_2652 : reg (bv 64)) => do
      v_9095 <- getRegister zf;
      v_9097 <- getRegister sf;
      v_9099 <- getRegister of;
      v_9104 <- evaluateAddress v_2651;
      v_9105 <- load v_9104 8;
      v_9106 <- getRegister v_2652;
      setRegister (lhs.of_reg v_2652) (mux (bit_or (eq v_9095 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9097 (expression.bv_nat 1 1)) (eq v_9099 (expression.bv_nat 1 1))))) v_9105 v_9106);
      pure ()
    pat_end;
    pattern fun (v_2669 : Mem) (v_2668 : reg (bv 16)) => do
      v_9109 <- getRegister zf;
      v_9111 <- getRegister sf;
      v_9113 <- getRegister of;
      v_9118 <- evaluateAddress v_2669;
      v_9119 <- load v_9118 2;
      v_9120 <- getRegister v_2668;
      setRegister (lhs.of_reg v_2668) (mux (bit_or (eq v_9109 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9111 (expression.bv_nat 1 1)) (eq v_9113 (expression.bv_nat 1 1))))) v_9119 v_9120);
      pure ()
    pat_end
