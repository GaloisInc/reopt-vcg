def cmovow1 : instruction :=
  definst "cmovow" $ do
    pattern fun (v_3226 : reg (bv 16)) (v_3227 : reg (bv 16)) => do
      v_4994 <- getRegister of;
      v_4995 <- getRegister v_3226;
      v_4996 <- getRegister v_3227;
      setRegister (lhs.of_reg v_3227) (mux v_4994 v_4995 v_4996);
      pure ()
    pat_end;
    pattern fun (v_3222 : Mem) (v_3223 : reg (bv 16)) => do
      v_8246 <- getRegister of;
      v_8247 <- evaluateAddress v_3222;
      v_8248 <- load v_8247 2;
      v_8249 <- getRegister v_3223;
      setRegister (lhs.of_reg v_3223) (mux v_8246 v_8248 v_8249);
      pure ()
    pat_end
