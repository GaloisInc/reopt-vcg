def vucomiss1 : instruction :=
  definst "vucomiss" $ do
    pattern fun (v_2471 : reg (bv 128)) (v_2472 : reg (bv 128)) => do
      v_3657 <- getRegister v_2472;
      v_3659 <- getRegister v_2471;
      v_3661 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_3657 96 128) (extract v_3659 96 128));
      v_3662 <- eval (eq v_3661 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_3662 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_3662 (eq v_3661 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_3662 (eq v_3661 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2467 : Mem) (v_2468 : reg (bv 128)) => do
      v_6913 <- getRegister v_2468;
      v_6915 <- evaluateAddress v_2467;
      v_6916 <- load v_6915 4;
      v_6917 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_6913 96 128) v_6916);
      v_6918 <- eval (eq v_6917 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_6918 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_6918 (eq v_6917 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_6918 (eq v_6917 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
