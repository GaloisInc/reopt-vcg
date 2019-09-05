def cmovbq1 : instruction :=
  definst "cmovbq" $ do
    pattern fun (v_2552 : reg (bv 64)) (v_2553 : reg (bv 64)) => do
      v_4232 <- getRegister cf;
      v_4234 <- getRegister v_2552;
      v_4235 <- getRegister v_2553;
      setRegister (lhs.of_reg v_2553) (mux (eq v_4232 (expression.bv_nat 1 1)) v_4234 v_4235);
      pure ()
    pat_end;
    pattern fun (v_2547 : Mem) (v_2548 : reg (bv 64)) => do
      v_7886 <- getRegister cf;
      v_7888 <- evaluateAddress v_2547;
      v_7889 <- load v_7888 8;
      v_7890 <- getRegister v_2548;
      setRegister (lhs.of_reg v_2548) (mux (eq v_7886 (expression.bv_nat 1 1)) v_7889 v_7890);
      pure ()
    pat_end
