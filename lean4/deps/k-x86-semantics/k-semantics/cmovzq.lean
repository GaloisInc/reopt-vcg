def cmovzq1 : instruction :=
  definst "cmovzq" $ do
    pattern fun (v_3376 : reg (bv 64)) (v_3377 : reg (bv 64)) => do
      v_5138 <- getRegister zf;
      v_5139 <- getRegister v_3376;
      v_5140 <- getRegister v_3377;
      setRegister (lhs.of_reg v_3377) (mux v_5138 v_5139 v_5140);
      pure ()
    pat_end;
    pattern fun (v_3372 : Mem) (v_3373 : reg (bv 64)) => do
      v_8336 <- getRegister zf;
      v_8337 <- evaluateAddress v_3372;
      v_8338 <- load v_8337 8;
      v_8339 <- getRegister v_3373;
      setRegister (lhs.of_reg v_3373) (mux v_8336 v_8338 v_8339);
      pure ()
    pat_end
