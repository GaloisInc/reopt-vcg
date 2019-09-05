def movlpd1 : instruction :=
  definst "movlpd" $ do
    pattern fun (v_2561 : reg (bv 128)) (v_2560 : Mem) => do
      v_8448 <- evaluateAddress v_2560;
      v_8449 <- getRegister v_2561;
      store v_8448 (extract v_8449 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2564 : Mem) (v_2565 : reg (bv 128)) => do
      v_8707 <- getRegister v_2565;
      v_8709 <- evaluateAddress v_2564;
      v_8710 <- load v_8709 8;
      setRegister (lhs.of_reg v_2565) (concat (extract v_8707 0 64) v_8710);
      pure ()
    pat_end
