def cmovsl1 : instruction :=
  definst "cmovsl" $ do
    pattern fun (v_3234 : reg (bv 32)) (v_3235 : reg (bv 32)) => do
      v_5132 <- getRegister sf;
      v_5134 <- getRegister v_3234;
      v_5135 <- getRegister v_3235;
      setRegister (lhs.of_reg v_3235) (mux (eq v_5132 (expression.bv_nat 1 1)) v_5134 v_5135);
      pure ()
    pat_end;
    pattern fun (v_3226 : Mem) (v_3227 : reg (bv 32)) => do
      v_8602 <- getRegister sf;
      v_8604 <- evaluateAddress v_3226;
      v_8605 <- load v_8604 4;
      v_8606 <- getRegister v_3227;
      setRegister (lhs.of_reg v_3227) (mux (eq v_8602 (expression.bv_nat 1 1)) v_8605 v_8606);
      pure ()
    pat_end
