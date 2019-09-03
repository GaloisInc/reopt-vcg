def movlps1 : instruction :=
  definst "movlps" $ do
    pattern fun (v_2519 : reg (bv 128)) (v_2518 : Mem) => do
      v_8589 <- evaluateAddress v_2518;
      v_8590 <- getRegister v_2519;
      store v_8589 (extract v_8590 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2522 : Mem) (v_2523 : reg (bv 128)) => do
      v_8849 <- getRegister v_2523;
      v_8851 <- evaluateAddress v_2522;
      v_8852 <- load v_8851 8;
      setRegister (lhs.of_reg v_2523) (concat (extract v_8849 0 64) v_8852);
      pure ()
    pat_end
