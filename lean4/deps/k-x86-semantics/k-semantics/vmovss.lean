def vmovss1 : instruction :=
  definst "vmovss" $ do
    pattern fun (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) (v_3072 : reg (bv 128)) => do
      v_5103 <- getRegister v_3071;
      v_5105 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3072) (concat (extract v_5103 0 96) (extract v_5105 96 128));
      pure ()
    pat_end;
    pattern fun (v_3066 : Mem) (v_3067 : reg (bv 128)) => do
      v_10266 <- evaluateAddress v_3066;
      v_10267 <- load v_10266 4;
      setRegister (lhs.of_reg v_3067) (concat (expression.bv_nat 96 0) v_10267);
      pure ()
    pat_end;
    pattern fun (v_3063 : reg (bv 128)) (v_3062 : Mem) => do
      v_12455 <- evaluateAddress v_3062;
      v_12456 <- getRegister v_3063;
      store v_12455 (extract v_12456 96 128) 4;
      pure ()
    pat_end
