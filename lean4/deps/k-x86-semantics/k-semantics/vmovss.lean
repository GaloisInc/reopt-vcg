def vmovss1 : instruction :=
  definst "vmovss" $ do
    pattern fun (v_3007 : reg (bv 128)) (v_3008 : reg (bv 128)) (v_3009 : reg (bv 128)) => do
      v_5045 <- getRegister v_3008;
      v_5047 <- getRegister v_3007;
      setRegister (lhs.of_reg v_3009) (concat (extract v_5045 0 96) (extract v_5047 96 128));
      pure ()
    pat_end;
    pattern fun (v_3002 : Mem) (v_3003 : reg (bv 128)) => do
      v_10400 <- evaluateAddress v_3002;
      v_10401 <- load v_10400 4;
      setRegister (lhs.of_reg v_3003) (concat (expression.bv_nat 96 0) v_10401);
      pure ()
    pat_end;
    pattern fun (v_2999 : reg (bv 128)) (v_2998 : Mem) => do
      v_12775 <- evaluateAddress v_2998;
      v_12776 <- getRegister v_2999;
      store v_12775 (extract v_12776 96 128) 4;
      pure ()
    pat_end
