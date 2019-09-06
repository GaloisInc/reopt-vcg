def cmovbq1 : instruction :=
  definst "cmovbq" $ do
    pattern fun (v_2578 : reg (bv 64)) (v_2579 : reg (bv 64)) => do
      v_4244 <- getRegister cf;
      v_4245 <- getRegister v_2578;
      v_4246 <- getRegister v_2579;
      setRegister (lhs.of_reg v_2579) (mux v_4244 v_4245 v_4246);
      pure ()
    pat_end;
    pattern fun (v_2574 : Mem) (v_2575 : reg (bv 64)) => do
      v_7724 <- getRegister cf;
      v_7725 <- evaluateAddress v_2574;
      v_7726 <- load v_7725 8;
      v_7727 <- getRegister v_2575;
      setRegister (lhs.of_reg v_2575) (mux v_7724 v_7726 v_7727);
      pure ()
    pat_end
