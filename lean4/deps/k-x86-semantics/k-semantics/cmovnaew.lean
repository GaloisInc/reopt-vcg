def cmovnaew1 : instruction :=
  definst "cmovnaew" $ do
    pattern fun (v_2798 : reg (bv 16)) (v_2799 : reg (bv 16)) => do
      v_4545 <- getRegister cf;
      v_4547 <- getRegister v_2798;
      v_4548 <- getRegister v_2799;
      setRegister (lhs.of_reg v_2799) (mux (eq v_4545 (expression.bv_nat 1 1)) v_4547 v_4548);
      pure ()
    pat_end;
    pattern fun (v_2793 : Mem) (v_2794 : reg (bv 16)) => do
      v_8109 <- getRegister cf;
      v_8111 <- evaluateAddress v_2793;
      v_8112 <- load v_8111 2;
      v_8113 <- getRegister v_2794;
      setRegister (lhs.of_reg v_2794) (mux (eq v_8109 (expression.bv_nat 1 1)) v_8112 v_8113);
      pure ()
    pat_end
