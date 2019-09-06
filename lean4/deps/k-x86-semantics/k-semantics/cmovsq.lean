def cmovsq1 : instruction :=
  definst "cmovsq" $ do
    pattern fun (v_3341 : reg (bv 64)) (v_3342 : reg (bv 64)) => do
      v_5106 <- getRegister sf;
      v_5107 <- getRegister v_3341;
      v_5108 <- getRegister v_3342;
      setRegister (lhs.of_reg v_3342) (mux v_5106 v_5107 v_5108);
      pure ()
    pat_end;
    pattern fun (v_3333 : Mem) (v_3334 : reg (bv 64)) => do
      v_8317 <- getRegister sf;
      v_8318 <- evaluateAddress v_3333;
      v_8319 <- load v_8318 8;
      v_8320 <- getRegister v_3334;
      setRegister (lhs.of_reg v_3334) (mux v_8317 v_8319 v_8320);
      pure ()
    pat_end
