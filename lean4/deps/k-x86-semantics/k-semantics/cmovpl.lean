def cmovpl1 : instruction :=
  definst "cmovpl" $ do
    pattern fun (v_3172 : reg (bv 32)) (v_3173 : reg (bv 32)) => do
      v_5064 <- getRegister pf;
      v_5066 <- getRegister v_3172;
      v_5067 <- getRegister v_3173;
      setRegister (lhs.of_reg v_3173) (mux (eq v_5064 (expression.bv_nat 1 1)) v_5066 v_5067);
      pure ()
    pat_end;
    pattern fun (v_3168 : Mem) (v_3169 : reg (bv 32)) => do
      v_8556 <- getRegister pf;
      v_8558 <- evaluateAddress v_3168;
      v_8559 <- load v_8558 4;
      v_8560 <- getRegister v_3169;
      setRegister (lhs.of_reg v_3169) (mux (eq v_8556 (expression.bv_nat 1 1)) v_8559 v_8560);
      pure ()
    pat_end
