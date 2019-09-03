def cmovbq1 : instruction :=
  definst "cmovbq" $ do
    pattern fun (v_2500 : reg (bv 64)) (v_2501 : reg (bv 64)) => do
      v_4181 <- getRegister cf;
      v_4183 <- getRegister v_2500;
      v_4184 <- getRegister v_2501;
      setRegister (lhs.of_reg v_2501) (mux (eq v_4181 (expression.bv_nat 1 1)) v_4183 v_4184);
      pure ()
    pat_end;
    pattern fun (v_2496 : Mem) (v_2497 : reg (bv 64)) => do
      v_7873 <- getRegister cf;
      v_7875 <- evaluateAddress v_2496;
      v_7876 <- load v_7875 8;
      v_7877 <- getRegister v_2497;
      setRegister (lhs.of_reg v_2497) (mux (eq v_7873 (expression.bv_nat 1 1)) v_7876 v_7877);
      pure ()
    pat_end
