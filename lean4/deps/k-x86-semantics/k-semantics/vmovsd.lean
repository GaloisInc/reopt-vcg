def vmovsd1 : instruction :=
  definst "vmovsd" $ do
    pattern fun (v_3045 : reg (bv 128)) (v_3046 : reg (bv 128)) (v_3047 : reg (bv 128)) => do
      v_5060 <- getRegister v_3046;
      v_5062 <- getRegister v_3045;
      setRegister (lhs.of_reg v_3047) (concat (extract v_5060 0 64) (extract v_5062 64 128));
      pure ()
    pat_end;
    pattern fun (v_3041 : Mem) (v_3042 : reg (bv 128)) => do
      v_10244 <- evaluateAddress v_3041;
      v_10245 <- load v_10244 8;
      setRegister (lhs.of_reg v_3042) (concat (expression.bv_nat 64 0) v_10245);
      pure ()
    pat_end;
    pattern fun (v_3038 : reg (bv 128)) (v_3037 : Mem) => do
      v_12478 <- evaluateAddress v_3037;
      v_12479 <- getRegister v_3038;
      store v_12478 (extract v_12479 64 128) 8;
      pure ()
    pat_end
