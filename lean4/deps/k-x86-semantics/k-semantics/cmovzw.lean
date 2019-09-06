def cmovzw1 : instruction :=
  definst "cmovzw" $ do
    pattern fun (v_3385 : reg (bv 16)) (v_3386 : reg (bv 16)) => do
      v_5147 <- getRegister zf;
      v_5148 <- getRegister v_3385;
      v_5149 <- getRegister v_3386;
      setRegister (lhs.of_reg v_3386) (mux v_5147 v_5148 v_5149);
      pure ()
    pat_end;
    pattern fun (v_3381 : Mem) (v_3382 : reg (bv 16)) => do
      v_8342 <- getRegister zf;
      v_8343 <- evaluateAddress v_3381;
      v_8344 <- load v_8343 2;
      v_8345 <- getRegister v_3382;
      setRegister (lhs.of_reg v_3382) (mux v_8342 v_8344 v_8345);
      pure ()
    pat_end
