def vcomisd1 : instruction :=
  definst "vcomisd" $ do
    pattern fun (v_2984 : reg (bv 128)) (v_2985 : reg (bv 128)) => do
      v_5744 <- getRegister v_2985;
      v_5746 <- getRegister v_2984;
      v_5748 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_5744 64 128) (extract v_5746 64 128));
      v_5749 <- eval (eq v_5748 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_5749 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_5749 (eq v_5748 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_5749 (eq v_5748 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2977 : Mem) (v_2980 : reg (bv 128)) => do
      v_10056 <- getRegister v_2980;
      v_10058 <- evaluateAddress v_2977;
      v_10059 <- load v_10058 8;
      v_10060 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_10056 64 128) v_10059);
      v_10061 <- eval (eq v_10060 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_10061 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_10061 (eq v_10060 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_10061 (eq v_10060 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
