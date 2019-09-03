def vucomisd1 : instruction :=
  definst "vucomisd" $ do
    pattern fun (v_2462 : reg (bv 128)) (v_2463 : reg (bv 128)) => do
      v_3634 <- getRegister v_2463;
      v_3636 <- getRegister v_2462;
      v_3638 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_3634 64 128) (extract v_3636 64 128));
      v_3639 <- eval (eq v_3638 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_3639 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_3639 (eq v_3638 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_3639 (eq v_3638 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2458 : Mem) (v_2459 : reg (bv 128)) => do
      v_6894 <- getRegister v_2459;
      v_6896 <- evaluateAddress v_2458;
      v_6897 <- load v_6896 8;
      v_6898 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_6894 64 128) v_6897);
      v_6899 <- eval (eq v_6898 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_6899 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_6899 (eq v_6898 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_6899 (eq v_6898 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
