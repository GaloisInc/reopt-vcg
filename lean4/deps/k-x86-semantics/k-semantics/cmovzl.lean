def cmovzl1 : instruction :=
  definst "cmovzl" $ do
    pattern fun (v_3370 : reg (bv 32)) (v_3371 : reg (bv 32)) => do
      v_5129 <- getRegister zf;
      v_5130 <- getRegister v_3370;
      v_5131 <- getRegister v_3371;
      setRegister (lhs.of_reg v_3371) (mux v_5129 v_5130 v_5131);
      pure ()
    pat_end;
    pattern fun (v_3363 : Mem) (v_3366 : reg (bv 32)) => do
      v_8330 <- getRegister zf;
      v_8331 <- evaluateAddress v_3363;
      v_8332 <- load v_8331 4;
      v_8333 <- getRegister v_3366;
      setRegister (lhs.of_reg v_3366) (mux v_8330 v_8332 v_8333);
      pure ()
    pat_end
