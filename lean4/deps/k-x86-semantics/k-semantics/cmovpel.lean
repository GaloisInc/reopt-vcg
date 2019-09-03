def cmovpel1 : instruction :=
  definst "cmovpel" $ do
    pattern fun (v_3145 : reg (bv 32)) (v_3146 : reg (bv 32)) => do
      v_5034 <- getRegister pf;
      v_5036 <- getRegister v_3145;
      v_5037 <- getRegister v_3146;
      setRegister (lhs.of_reg v_3146) (mux (eq v_5034 (expression.bv_nat 1 1)) v_5036 v_5037);
      pure ()
    pat_end;
    pattern fun (v_3141 : Mem) (v_3142 : reg (bv 32)) => do
      v_8535 <- getRegister pf;
      v_8537 <- evaluateAddress v_3141;
      v_8538 <- load v_8537 4;
      v_8539 <- getRegister v_3142;
      setRegister (lhs.of_reg v_3142) (mux (eq v_8535 (expression.bv_nat 1 1)) v_8538 v_8539);
      pure ()
    pat_end
