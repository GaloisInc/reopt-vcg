def cmovsw1 : instruction :=
  definst "cmovsw" $ do
    pattern fun (v_3358 : reg (bv 16)) (v_3359 : reg (bv 16)) => do
      v_5120 <- getRegister sf;
      v_5121 <- getRegister v_3358;
      v_5122 <- getRegister v_3359;
      setRegister (lhs.of_reg v_3359) (mux v_5120 v_5121 v_5122);
      pure ()
    pat_end;
    pattern fun (v_3350 : Mem) (v_3351 : reg (bv 16)) => do
      v_8324 <- getRegister sf;
      v_8325 <- evaluateAddress v_3350;
      v_8326 <- load v_8325 2;
      v_8327 <- getRegister v_3351;
      setRegister (lhs.of_reg v_3351) (mux v_8324 v_8326 v_8327);
      pure ()
    pat_end
