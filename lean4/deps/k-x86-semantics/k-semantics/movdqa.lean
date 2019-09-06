def movdqa1 : instruction :=
  definst "movdqa" $ do
    pattern fun (v_2520 : reg (bv 128)) (v_2521 : reg (bv 128)) => do
      v_3949 <- getRegister v_2520;
      setRegister (lhs.of_reg v_2521) v_3949;
      pure ()
    pat_end;
    pattern fun (v_2513 : reg (bv 128)) (v_2512 : Mem) => do
      v_8450 <- evaluateAddress v_2512;
      v_8451 <- getRegister v_2513;
      store v_8450 v_8451 16;
      pure ()
    pat_end;
    pattern fun (v_2516 : Mem) (v_2517 : reg (bv 128)) => do
      v_8713 <- evaluateAddress v_2516;
      v_8714 <- load v_8713 16;
      setRegister (lhs.of_reg v_2517) v_8714;
      pure ()
    pat_end
