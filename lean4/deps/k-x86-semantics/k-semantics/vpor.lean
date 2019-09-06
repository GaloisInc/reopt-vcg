def vpor1 : instruction :=
  definst "vpor" $ do
    pattern fun (v_3048 : Mem) (v_3049 : reg (bv 128)) (v_3050 : reg (bv 128)) => do
      v_13288 <- getRegister v_3049;
      v_13289 <- evaluateAddress v_3048;
      v_13290 <- load v_13289 16;
      setRegister (lhs.of_reg v_3050) (bv_or v_13288 v_13290);
      pure ()
    pat_end;
    pattern fun (v_3059 : Mem) (v_3060 : reg (bv 256)) (v_3061 : reg (bv 256)) => do
      v_13293 <- getRegister v_3060;
      v_13294 <- evaluateAddress v_3059;
      v_13295 <- load v_13294 32;
      setRegister (lhs.of_reg v_3061) (bv_or v_13293 v_13295);
      pure ()
    pat_end
