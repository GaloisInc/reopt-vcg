def cmovpeq1 : instruction :=
  definst "cmovpeq" $ do
    pattern fun (v_3166 : reg (bv 64)) (v_3167 : reg (bv 64)) => do
      v_5057 <- getRegister pf;
      v_5059 <- getRegister v_3166;
      v_5060 <- getRegister v_3167;
      setRegister (lhs.of_reg v_3167) (mux (eq v_5057 (expression.bv_nat 1 1)) v_5059 v_5060);
      pure ()
    pat_end;
    pattern fun (v_3162 : Mem) (v_3163 : reg (bv 64)) => do
      v_8515 <- getRegister pf;
      v_8517 <- evaluateAddress v_3162;
      v_8518 <- load v_8517 8;
      v_8519 <- getRegister v_3163;
      setRegister (lhs.of_reg v_3163) (mux (eq v_8515 (expression.bv_nat 1 1)) v_8518 v_8519);
      pure ()
    pat_end
