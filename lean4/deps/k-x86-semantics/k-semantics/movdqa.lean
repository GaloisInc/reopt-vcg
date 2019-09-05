def movdqa1 : instruction :=
  definst "movdqa" $ do
    pattern fun (v_2495 : reg (bv 128)) (v_2496 : reg (bv 128)) => do
      v_3922 <- getRegister v_2495;
      setRegister (lhs.of_reg v_2496) v_3922;
      pure ()
    pat_end;
    pattern fun (v_2487 : reg (bv 128)) (v_2486 : Mem) => do
      v_8423 <- evaluateAddress v_2486;
      v_8424 <- getRegister v_2487;
      store v_8423 v_8424 16;
      pure ()
    pat_end;
    pattern fun (v_2490 : Mem) (v_2491 : reg (bv 128)) => do
      v_8686 <- evaluateAddress v_2490;
      v_8687 <- load v_8686 16;
      setRegister (lhs.of_reg v_2491) v_8687;
      pure ()
    pat_end
