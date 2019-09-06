def cmovsl1 : instruction :=
  definst "cmovsl" $ do
    pattern fun (v_3327 : reg (bv 32)) (v_3328 : reg (bv 32)) => do
      v_5092 <- getRegister sf;
      v_5093 <- getRegister v_3327;
      v_5094 <- getRegister v_3328;
      setRegister (lhs.of_reg v_3328) (mux v_5092 v_5093 v_5094);
      pure ()
    pat_end;
    pattern fun (v_3316 : Mem) (v_3319 : reg (bv 32)) => do
      v_8310 <- getRegister sf;
      v_8311 <- evaluateAddress v_3316;
      v_8312 <- load v_8311 4;
      v_8313 <- getRegister v_3319;
      setRegister (lhs.of_reg v_3319) (mux v_8310 v_8312 v_8313);
      pure ()
    pat_end
