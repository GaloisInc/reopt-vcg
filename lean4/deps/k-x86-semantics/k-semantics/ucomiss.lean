def ucomiss1 : instruction :=
  definst "ucomiss" $ do
    pattern fun (v_2524 : reg (bv 128)) (v_2525 : reg (bv 128)) => do
      v_4741 <- getRegister v_2525;
      v_4743 <- getRegister v_2524;
      v_4745 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4741 96 128) (extract v_4743 96 128));
      v_4746 <- eval (eq v_4745 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4746 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4746 (eq v_4745 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4746 (eq v_4745 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2517 : Mem) (v_2520 : reg (bv 128)) => do
      v_9227 <- getRegister v_2520;
      v_9229 <- evaluateAddress v_2517;
      v_9230 <- load v_9229 4;
      v_9231 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_9227 96 128) v_9230);
      v_9232 <- eval (eq v_9231 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_9232 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_9232 (eq v_9231 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_9232 (eq v_9231 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
