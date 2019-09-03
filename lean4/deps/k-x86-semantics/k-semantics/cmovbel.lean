def cmovbel1 : instruction :=
  definst "cmovbel" $ do
    pattern fun (v_2436 : reg (bv 32)) (v_2437 : reg (bv 32)) => do
      v_4109 <- getRegister cf;
      v_4111 <- getRegister zf;
      v_4114 <- getRegister v_2436;
      v_4115 <- getRegister v_2437;
      setRegister (lhs.of_reg v_2437) (mux (bit_or (eq v_4109 (expression.bv_nat 1 1)) (eq v_4111 (expression.bv_nat 1 1))) v_4114 v_4115);
      pure ()
    pat_end;
    pattern fun (v_2428 : Mem) (v_2429 : reg (bv 32)) => do
      v_7861 <- getRegister cf;
      v_7863 <- getRegister zf;
      v_7866 <- evaluateAddress v_2428;
      v_7867 <- load v_7866 4;
      v_7868 <- getRegister v_2429;
      setRegister (lhs.of_reg v_2429) (mux (bit_or (eq v_7861 (expression.bv_nat 1 1)) (eq v_7863 (expression.bv_nat 1 1))) v_7867 v_7868);
      pure ()
    pat_end
