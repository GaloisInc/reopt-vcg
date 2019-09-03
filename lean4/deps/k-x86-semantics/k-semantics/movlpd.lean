def movlpd1 : instruction :=
  definst "movlpd" $ do
    pattern fun (v_2511 : reg (bv 128)) (v_2510 : Mem) => do
      v_8584 <- evaluateAddress v_2510;
      v_8585 <- getRegister v_2511;
      store v_8584 (extract v_8585 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2514 : Mem) (v_2515 : reg (bv 128)) => do
      v_8843 <- getRegister v_2515;
      v_8845 <- evaluateAddress v_2514;
      v_8846 <- load v_8845 8;
      setRegister (lhs.of_reg v_2515) (concat (extract v_8843 0 64) v_8846);
      pure ()
    pat_end
