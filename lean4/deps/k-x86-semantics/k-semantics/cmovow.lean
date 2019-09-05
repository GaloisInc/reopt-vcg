def cmovow1 : instruction :=
  definst "cmovow" $ do
    pattern fun (v_3200 : reg (bv 16)) (v_3201 : reg (bv 16)) => do
      v_5088 <- getRegister of;
      v_5090 <- getRegister v_3200;
      v_5091 <- getRegister v_3201;
      setRegister (lhs.of_reg v_3201) (mux (eq v_5088 (expression.bv_nat 1 1)) v_5090 v_5091);
      pure ()
    pat_end;
    pattern fun (v_3195 : Mem) (v_3196 : reg (bv 16)) => do
      v_8514 <- getRegister of;
      v_8516 <- evaluateAddress v_3195;
      v_8517 <- load v_8516 2;
      v_8518 <- getRegister v_3196;
      setRegister (lhs.of_reg v_3196) (mux (eq v_8514 (expression.bv_nat 1 1)) v_8517 v_8518);
      pure ()
    pat_end
