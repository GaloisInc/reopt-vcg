def cmovpq1 : instruction :=
  definst "cmovpq" $ do
    pattern fun (v_3298 : reg (bv 64)) (v_3299 : reg (bv 64)) => do
      v_5069 <- getRegister pf;
      v_5070 <- getRegister v_3298;
      v_5071 <- getRegister v_3299;
      setRegister (lhs.of_reg v_3299) (mux v_5069 v_5070 v_5071);
      pure ()
    pat_end;
    pattern fun (v_3294 : Mem) (v_3295 : reg (bv 64)) => do
      v_8297 <- getRegister pf;
      v_8298 <- evaluateAddress v_3294;
      v_8299 <- load v_8298 8;
      v_8300 <- getRegister v_3295;
      setRegister (lhs.of_reg v_3295) (mux v_8297 v_8299 v_8300);
      pure ()
    pat_end
