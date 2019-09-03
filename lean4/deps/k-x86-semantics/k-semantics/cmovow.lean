def cmovow1 : instruction :=
  definst "cmovow" $ do
    pattern fun (v_3136 : reg (bv 16)) (v_3137 : reg (bv 16)) => do
      v_5024 <- getRegister of;
      v_5026 <- getRegister v_3136;
      v_5027 <- getRegister v_3137;
      setRegister (lhs.of_reg v_3137) (mux (eq v_5024 (expression.bv_nat 1 1)) v_5026 v_5027);
      pure ()
    pat_end;
    pattern fun (v_3133 : Mem) (v_3132 : reg (bv 16)) => do
      v_8528 <- getRegister of;
      v_8530 <- evaluateAddress v_3133;
      v_8531 <- load v_8530 2;
      v_8532 <- getRegister v_3132;
      setRegister (lhs.of_reg v_3132) (mux (eq v_8528 (expression.bv_nat 1 1)) v_8531 v_8532);
      pure ()
    pat_end
