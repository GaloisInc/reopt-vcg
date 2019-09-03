def movhpd1 : instruction :=
  definst "movhpd" $ do
    pattern fun (v_2468 : reg (bv 128)) (v_2467 : Mem) => do
      v_8567 <- evaluateAddress v_2467;
      v_8568 <- getRegister v_2468;
      store v_8567 (extract v_8568 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2471 : Mem) (v_2472 : reg (bv 128)) => do
      v_8828 <- evaluateAddress v_2471;
      v_8829 <- load v_8828 8;
      v_8830 <- getRegister v_2472;
      setRegister (lhs.of_reg v_2472) (concat v_8829 (extract v_8830 64 128));
      pure ()
    pat_end
