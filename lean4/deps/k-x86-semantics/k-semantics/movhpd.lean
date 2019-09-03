def movhpd1 : instruction :=
  definst "movhpd" $ do
    pattern fun (v_2455 : reg (bv 128)) (v_2454 : Mem) => do
      v_8587 <- evaluateAddress v_2454;
      v_8588 <- getRegister v_2455;
      store v_8587 (extract v_8588 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2458 : Mem) (v_2459 : reg (bv 128)) => do
      v_8849 <- evaluateAddress v_2458;
      v_8850 <- load v_8849 8;
      v_8851 <- getRegister v_2459;
      setRegister (lhs.of_reg v_2459) (concat v_8850 (extract v_8851 64 128));
      pure ()
    pat_end
