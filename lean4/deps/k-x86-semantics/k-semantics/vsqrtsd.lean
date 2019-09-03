def vsqrtsd1 : instruction :=
  definst "vsqrtsd" $ do
    pattern fun (v_2341 : reg (bv 128)) (v_2342 : reg (bv 128)) (v_2343 : reg (bv 128)) => do
      v_3179 <- getRegister v_2342;
      v_3181 <- getRegister v_2341;
      setRegister (lhs.of_reg v_2343) (concat (extract v_3179 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_3181 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2334 : Mem) (v_2336 : reg (bv 128)) (v_2337 : reg (bv 128)) => do
      v_6486 <- getRegister v_2336;
      v_6488 <- evaluateAddress v_2334;
      v_6489 <- load v_6488 8;
      setRegister (lhs.of_reg v_2337) (concat (extract v_6486 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_6489));
      pure ()
    pat_end
