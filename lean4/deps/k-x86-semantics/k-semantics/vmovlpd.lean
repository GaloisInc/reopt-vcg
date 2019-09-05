def vmovlpd1 : instruction :=
  definst "vmovlpd" $ do
    pattern fun (v_2903 : Mem) (v_2904 : reg (bv 128)) (v_2905 : reg (bv 128)) => do
      v_10188 <- getRegister v_2904;
      v_10190 <- evaluateAddress v_2903;
      v_10191 <- load v_10190 8;
      setRegister (lhs.of_reg v_2905) (concat (extract v_10188 0 64) v_10191);
      pure ()
    pat_end;
    pattern fun (v_2900 : reg (bv 128)) (v_2899 : Mem) => do
      v_12428 <- evaluateAddress v_2899;
      v_12429 <- getRegister v_2900;
      store v_12428 (extract v_12429 64 128) 8;
      pure ()
    pat_end
