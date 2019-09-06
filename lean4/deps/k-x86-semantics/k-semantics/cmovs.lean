def cmovs1 : instruction :=
  definst "cmovs" $ do
    pattern fun (v_3312 : Mem) (v_3315 : reg (bv 32)) => do
      v_8753 <- getRegister sf;
      v_8754 <- evaluateAddress v_3312;
      v_8755 <- load v_8754 4;
      v_8756 <- getRegister v_3315;
      setRegister (lhs.of_reg v_3315) (mux v_8753 v_8755 v_8756);
      pure ()
    pat_end;
    pattern fun (v_3330 : Mem) (v_3329 : reg (bv 64)) => do
      v_8759 <- getRegister sf;
      v_8760 <- evaluateAddress v_3330;
      v_8761 <- load v_8760 8;
      v_8762 <- getRegister v_3329;
      setRegister (lhs.of_reg v_3329) (mux v_8759 v_8761 v_8762);
      pure ()
    pat_end;
    pattern fun (v_3346 : Mem) (v_3347 : reg (bv 16)) => do
      v_8765 <- getRegister sf;
      v_8766 <- evaluateAddress v_3346;
      v_8767 <- load v_8766 2;
      v_8768 <- getRegister v_3347;
      setRegister (lhs.of_reg v_3347) (mux v_8765 v_8767 v_8768);
      pure ()
    pat_end
