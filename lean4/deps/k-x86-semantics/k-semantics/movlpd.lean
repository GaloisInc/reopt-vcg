def movlpd1 : instruction :=
  definst "movlpd" $ do
    pattern fun (v_2498 : reg (bv 128)) (v_2497 : Mem) => do
      v_8604 <- evaluateAddress v_2497;
      v_8605 <- getRegister v_2498;
      store v_8604 (extract v_8605 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2501 : Mem) (v_2502 : reg (bv 128)) => do
      v_8864 <- getRegister v_2502;
      v_8866 <- evaluateAddress v_2501;
      v_8867 <- load v_8866 8;
      setRegister (lhs.of_reg v_2502) (concat (extract v_8864 0 64) v_8867);
      pure ()
    pat_end
