def movdqu1 : instruction :=
  definst "movdqu" $ do
    pattern fun (v_2508 : reg (bv 128)) (v_2509 : reg (bv 128)) => do
      v_3932 <- getRegister v_2508;
      setRegister (lhs.of_reg v_2509) v_3932;
      pure ()
    pat_end;
    pattern fun (v_2500 : reg (bv 128)) (v_2499 : Mem) => do
      v_8427 <- evaluateAddress v_2499;
      v_8428 <- getRegister v_2500;
      store v_8427 v_8428 16;
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 128)) => do
      v_8689 <- evaluateAddress v_2503;
      v_8690 <- load v_8689 16;
      setRegister (lhs.of_reg v_2504) v_8690;
      pure ()
    pat_end
