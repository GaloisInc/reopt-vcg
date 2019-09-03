def cmovnael1 : instruction :=
  definst "cmovnael" $ do
    pattern fun (v_2716 : reg (bv 32)) (v_2717 : reg (bv 32)) => do
      v_4461 <- getRegister cf;
      v_4463 <- getRegister v_2716;
      v_4464 <- getRegister v_2717;
      setRegister (lhs.of_reg v_2717) (mux (eq v_4461 (expression.bv_nat 1 1)) v_4463 v_4464);
      pure ()
    pat_end;
    pattern fun (v_2712 : Mem) (v_2713 : reg (bv 32)) => do
      v_8109 <- getRegister cf;
      v_8111 <- evaluateAddress v_2712;
      v_8112 <- load v_8111 4;
      v_8113 <- getRegister v_2713;
      setRegister (lhs.of_reg v_2713) (mux (eq v_8109 (expression.bv_nat 1 1)) v_8112 v_8113);
      pure ()
    pat_end
