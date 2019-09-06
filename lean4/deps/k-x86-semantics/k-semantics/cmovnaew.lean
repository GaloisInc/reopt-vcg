def cmovnaew1 : instruction :=
  definst "cmovnaew" $ do
    pattern fun (v_2824 : reg (bv 16)) (v_2825 : reg (bv 16)) => do
      v_4517 <- getRegister cf;
      v_4518 <- getRegister v_2824;
      v_4519 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2825) (mux v_4517 v_4518 v_4519);
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 16)) => do
      v_7907 <- getRegister cf;
      v_7908 <- evaluateAddress v_2820;
      v_7909 <- load v_7908 2;
      v_7910 <- getRegister v_2821;
      setRegister (lhs.of_reg v_2821) (mux v_7907 v_7909 v_7910);
      pure ()
    pat_end
