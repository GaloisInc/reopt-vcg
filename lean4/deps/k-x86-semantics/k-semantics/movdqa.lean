def movdqa1 : instruction :=
  definst "movdqa" $ do
    pattern fun (v_2432 : reg (bv 128)) (v_2433 : reg (bv 128)) => do
      v_3858 <- getRegister v_2432;
      setRegister (lhs.of_reg v_2433) v_3858;
      pure ()
    pat_end;
    pattern fun (v_2424 : reg (bv 128)) (v_2423 : Mem) => do
      v_8579 <- evaluateAddress v_2423;
      v_8580 <- getRegister v_2424;
      store v_8579 v_8580 16;
      pure ()
    pat_end;
    pattern fun (v_2427 : Mem) (v_2428 : reg (bv 128)) => do
      v_8843 <- evaluateAddress v_2427;
      v_8844 <- load v_8843 16;
      setRegister (lhs.of_reg v_2428) v_8844;
      pure ()
    pat_end
