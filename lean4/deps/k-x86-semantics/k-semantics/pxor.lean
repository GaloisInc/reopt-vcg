def pxor1 : instruction :=
  definst "pxor" $ do
    pattern fun (v_3258 : reg (bv 128)) (v_3259 : reg (bv 128)) => do
      v_8903 <- getRegister v_3259;
      v_8904 <- getRegister v_3258;
      setRegister (lhs.of_reg v_3259) (bv_xor v_8903 v_8904);
      pure ()
    pat_end;
    pattern fun (v_3254 : Mem) (v_3255 : reg (bv 128)) => do
      v_15462 <- getRegister v_3255;
      v_15463 <- evaluateAddress v_3254;
      v_15464 <- load v_15463 16;
      setRegister (lhs.of_reg v_3255) (bv_xor v_15462 v_15464);
      pure ()
    pat_end
