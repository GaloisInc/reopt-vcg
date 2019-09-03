def comisd1 : instruction :=
  definst "comisd" $ do
    pattern fun (v_2442 : reg (bv 128)) (v_2443 : reg (bv 128)) => do
      v_4020 <- getRegister v_2443;
      v_4022 <- getRegister v_2442;
      v_4024 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4020 64 128) (extract v_4022 64 128));
      v_4025 <- eval (eq v_4024 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4025 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4025 (eq v_4024 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4025 (eq v_4024 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2438 : Mem) (v_2439 : reg (bv 128)) => do
      v_7981 <- getRegister v_2439;
      v_7983 <- evaluateAddress v_2438;
      v_7984 <- load v_7983 8;
      v_7985 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_7981 64 128) v_7984);
      v_7986 <- eval (eq v_7985 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_7986 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_7986 (eq v_7985 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_7986 (eq v_7985 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
